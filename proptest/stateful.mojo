# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Stateful testing: random sequences of operations against a model.

Port of `hypothesis.stateful`. Hypothesis discovers `@rule`, `@invariant`,
`@precondition` and `@initialize` methods by reflection; in Mojo a state
machine instead numbers its rules and dispatches on the number:

```mojo
struct StackMachine(StateMachine):
    var model: List[Int]
    var stack: MyStack

    def __init__(out self):
        self.model = []
        self.stack = MyStack()

    def rule_count(self) -> Int:
        return 2

    def rule_name(self, rule: Int) -> String:
        return "push" if rule == 0 else "pop"

    def precondition(self, rule: Int) -> Bool:
        return rule == 0 or len(self.model) > 0   # pop needs an element

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            var x = data.draw(integers(), "x")
            self.model.append(x)
            self.stack.push(x)
        else:
            assert_equal(self.stack.pop(), self.model.pop())

    def check_invariants(self) raises:
        assert_equal(len(self.stack), len(self.model))

run_state_machine_as_test[StackMachine]()
```

A failure is reported as the (shrunk) sequence of steps:

```
state = StackMachine()
state.push(x=0)
state.pop()
```

Rule arguments are the labelled draws a rule makes. `Bundle[T]` holds
values produced by earlier steps for later steps to use (Hypothesis's
`Bundle`); `initialize_count`/`run_initialize` give rules that run exactly
once, first, in a random order (`@initialize`).
"""

from std.reflection import call_location, SourceLocation, reflect

from std.collections import Dict, Set

from proptest.internal.data import (
    FILTER_LABEL,
    ConjectureData,
    BUFFER_SIZE,
    calc_label_from_name,
)
from proptest.core import (
    run_test,
    _resolve_settings,
    _raise_failures,
    _check_deadline,
)
from std.time import perf_counter_ns
from proptest.settings import Settings, Verbosity, HealthCheck
from proptest.strategies.strategy import Drawable, format_value

comptime STATE_MACHINE_RUN_LABEL: UInt64 = 0x73746174656D61636869
comptime _NEVER_STOP_P = 1.52587890625e-05  # 2**-16


trait StateMachine(Deinitable, Movable):
    """A model of a system under test, driven by numbered rules."""

    def __init__(out self):
        """A fresh machine, in its initial state."""
        ...

    def rule_count(self) -> Int:
        """How many rules there are (numbered from 0)."""
        ...

    def rule_name(self, rule: Int) -> String:
        """The name printed for a rule in failure reports."""
        return String("rule", rule)

    def precondition(self, rule: Int) -> Bool:
        """Whether `rule` may run in the current state."""
        return True

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        """Run one step: draw any arguments with `data.draw(strategy,
        "name")`, apply the operation, and check its result."""
        ...

    def check_invariants(self) raises:
        """Checked after initialization and after every step."""
        return

    def initialize_count(self) -> Int:
        """How many initialize rules there are; each runs exactly once,
        before any ordinary rule."""
        return 0

    def initialize_name(self, rule: Int) -> String:
        return String("initialize", rule)

    def run_initialize(mut self, rule: Int, mut data: ConjectureData) raises:
        return

    def teardown(mut self) raises:
        """Called at the end of every run, even a failing one."""
        return


struct Bundle[T: Drawable](Copyable, Sized):
    """A named collection of values produced by earlier steps, for later
    steps to use (Hypothesis's `Bundle`). Keep bundles as fields of the
    state machine."""

    var name: String
    var values: List[Self.T]

    def __init__(out self, name: String):
        self.name = name
        self.values = List[Self.T]()

    def __len__(self) -> Int:
        return len(self.values)

    def add(mut self, var value: Self.T):
        """Add a value (Hypothesis's `target=bundle`)."""
        self.values.append(value^)

    def draw(self, mut data: ConjectureData) raises -> Self.T:
        """One of the values, shrinking towards the most recently added.
        The rule's precondition must ensure the bundle is non-empty."""
        var n = len(self.values)
        if n == 0:
            data.mark_invalid(String("empty bundle ", self.name))
        data.start_span(calc_label_from_name("bundle"))
        var i = data.draw_integer(
            Int128(0), Int128(n - 1), shrink_towards=Int128(n - 1)
        )
        data.stop_span()
        var v = self.values[Int(i)].copy()
        if (
            data.is_final
            and data.collect_step_draws
            and data.depth == data.report_depth
        ):
            data.step_draws.append(
                String(self.name, "[", i, "]=", format_value(v))
            )
        return v^

    def consume(mut self, mut data: ConjectureData) raises -> Self.T:
        """Like `draw`, but also removes the value (Hypothesis's
        `consumes(bundle)`)."""
        var n = len(self.values)
        if n == 0:
            data.mark_invalid(String("empty bundle ", self.name))
        data.start_span(calc_label_from_name("bundle"))
        var i = Int(
            data.draw_integer(
                Int128(0), Int128(n - 1), shrink_towards=Int128(n - 1)
            )
        )
        data.stop_span()
        var v = self.values.pop(i)
        if (
            data.is_final
            and data.collect_step_draws
            and data.depth == data.report_depth
        ):
            data.step_draws.append(
                String("consumes(", self.name, ")=", format_value(v))
            )
        return v^


comptime FEATURE_LABEL: UInt64 = 0x66656174757265


struct FeatureFlags(Movable):
    """Swarm testing (port of `hypothesis.strategies._internal.featureflags`).

    Each test case disables a random subset of the rules, which makes
    programs that hammer a few operations far more likely than uniform
    rule choice would. The flags "shrink open": the simplest choice enables
    a rule, so shrinking can use any rule.
    """

    var p_disabled: Float64
    var disabled: Dict[Int, Bool]
    var at_least_one_of: Set[Int]

    def __init__(out self, mut data: ConjectureData, n_rules: Int) raises:
        data.start_span(FEATURE_LABEL)
        self.p_disabled = (
            Float64(data.draw_integer(Int128(0), Int128(254))) / 255
        )
        data.stop_span()
        self.disabled = Dict[Int, Bool]()
        self.at_least_one_of = Set[Int]()
        for r in range(n_rules):
            self.at_least_one_of.add(r)

    def is_enabled(
        mut self, mut data: ConjectureData, rule: Int
    ) raises -> Bool:
        data.start_span(FEATURE_LABEL)
        var forced: Optional[Bool] = None
        if len(self.at_least_one_of) == 1 and rule in self.at_least_one_of:
            forced = False
        elif rule in self.disabled:
            forced = self.disabled[rule]
        var is_disabled = data.draw_boolean(self.p_disabled, forced=forced)
        self.disabled[rule] = is_disabled
        if rule in self.at_least_one_of and not is_disabled:
            self.at_least_one_of = Set[Int]()
        if rule in self.at_least_one_of:
            self.at_least_one_of.remove(rule)
        data.stop_span()
        return not is_disabled


def _call_text(name: String, var args: List[String]) -> String:
    var s = String("state.", name, "(")
    for k in range(len(args)):
        if k > 0:
            s += ", "
        s += args[k]
    s += ")"
    return s^


def run_state_machine[
    M: StateMachine
](mut data: ConjectureData, max_steps: Int, deadline_ns: Int = -1) raises:
    """Run one random program against a fresh `M` (the body of
    Hypothesis's `run_state_machine`). With `deadline_ns >= 0`, each step
    (the rule and the invariant checks after it, excluding time spent
    drawing data) must finish within the deadline."""
    var machine = M()
    if data.is_final:
        data.notes.append(String("state = ", reflect[M].base_name(), "()"))
    var failure: Optional[Error] = None
    try:
        machine.check_invariants()
        # initialize rules, each once, in a random order
        var pending = List[Int]()
        for i in range(machine.initialize_count()):
            pending.append(i)
        var steps = 0
        var flags: Optional[FeatureFlags] = None
        while True:
            data.start_span(STATE_MACHINE_RUN_LABEL)
            var must_stop: Optional[Bool] = None
            if steps >= max_steps:
                must_stop = True
            elif steps < 1:
                must_stop = False
            elif data.length > (BUFFER_SIZE * 8) // 10:
                must_stop = True
            if len(pending) > 0:
                must_stop = False
            if data.draw_boolean(_NEVER_STOP_P, forced=must_stop):
                data.stop_span()
                break
            steps += 1
            data.report_depth = data.depth
            data.collect_step_draws = data.is_final
            data.step_draws = List[String]()
            var name: String
            var step_start = perf_counter_ns()
            var drawn_before = data.draw_time_ns
            if len(pending) > 0:
                var k = Int(
                    data.draw_integer(Int128(0), Int128(len(pending) - 1))
                )
                var rule = pending.pop(k)
                name = machine.initialize_name(rule)
                machine.run_initialize(rule, data)
            else:
                var n_rules = machine.rule_count()
                var any_valid = False
                for r in range(n_rules):
                    if machine.precondition(r):
                        any_valid = True
                        break
                if not any_valid:
                    raise Error(
                        "InvalidDefinition: no rule's precondition holds, so"
                        " the state machine cannot make progress"
                    )
                if not flags:
                    flags = FeatureFlags(data, n_rules)
                # sampled_from(rules).filter(valid and enabled), as Hypothesis
                var rule = -1
                for _ in range(3):
                    data.start_span(FILTER_LABEL)
                    var k = Int(
                        data.draw_integer(Int128(0), Int128(n_rules - 1))
                    )
                    if machine.precondition(k) and flags.value().is_enabled(
                        data, k
                    ):
                        data.stop_span()
                        rule = k
                        break
                    data.stop_span(discard=True)
                if rule < 0:
                    data.mark_invalid("no enabled rule was drawn")
                name = machine.rule_name(rule)
                # don't charge rule selection to the step's deadline
                step_start = perf_counter_ns()
                drawn_before = data.draw_time_ns
                try:
                    machine.run_rule(rule, data)
                except e:
                    if data.is_final:
                        data.notes.append(
                            _call_text(name, data.step_draws.copy())
                        )
                    data.collect_step_draws = False
                    data.report_depth = 0
                    raise e^
            if data.is_final:
                data.notes.append(_call_text(name, data.step_draws.copy()))
            data.collect_step_draws = False
            data.report_depth = 0
            machine.check_invariants()
            _check_deadline(
                data,
                step_start + (data.draw_time_ns - drawn_before),
                deadline_ns,
            )
            data.stop_span()
    except e:
        failure = e^
    if data.is_final:
        data.notes.append("state.teardown()")
    machine.teardown()
    if failure:
        raise failure.take()


@always_inline
def run_state_machine_as_test[
    M: StateMachine
](
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Run random programs of up to `settings.stateful_step_count` steps
    against `M`, raising with the shrunk failing program if one fails."""
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    s.suppress_health_check.append(HealthCheck.data_too_large)
    s.suppress_health_check.append(HealthCheck.large_base_example)
    # Rule arguments aren't reported per argument, so explaining them would
    # only cost time.
    s.phases.explain = False
    var max_steps = s.stateful_step_count
    var deadline = s.deadline_ns()

    def run_one(mut data: ConjectureData) raises {max_steps, deadline}:
        run_state_machine[M](data, max_steps, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)
