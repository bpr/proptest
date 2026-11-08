# Stateful testing, ported from hypothesis/tests/cover/test_stateful.py and
# the "Die Hard" example in Hypothesis's documentation.

from std.time import sleep
from std.testing import TestSuite, assert_equal, assert_true, assert_false

from proptest import *
from std.utils import Variant

from proptest.stateful import StateMachine, Bundle, run_state_machine_as_test


# --- Die Hard: get exactly 4 gallons with a 3- and a 5-gallon jug ----------


struct DieHard(StateMachine):
    var small: Int
    var big: Int

    def __init__(out self):
        self.small = 0
        self.big = 0

    def rule_count(self) -> Int:
        return 6

    def rule_name(self, rule: Int) -> String:
        var names: List[String] = [
            "fill_small",
            "fill_big",
            "empty_small",
            "empty_big",
            "pour_small_into_big",
            "pour_big_into_small",
        ]
        return names[rule]

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            self.small = 3
        elif rule == 1:
            self.big = 5
        elif rule == 2:
            self.small = 0
        elif rule == 3:
            self.big = 0
        elif rule == 4:
            var old_big = self.big
            self.big = min(5, self.big + self.small)
            self.small = self.small - (self.big - old_big)
        else:
            var old_small = self.small
            self.small = min(3, self.small + self.big)
            self.big = self.big - (self.small - old_small)

    def check_invariants(self) raises:
        assert_true(0 <= self.small and self.small <= 3)
        assert_true(0 <= self.big and self.big <= 5)
        if self.big == 4:
            fail("big jug holds 4 gallons")


def test_die_hard_finds_solution() raises:
    var msg = String()
    try:
        run_state_machine_as_test[DieHard](
            Settings(database=None, max_examples=10000)
        )
    except e:
        msg = String(e)
    assert_true("big jug holds 4 gallons" in msg, msg)
    assert_true("state = DieHard()" in msg, msg)
    # The shortest solution has 6 steps (fill_big first). The 8-step one that
    # starts with fill_small is also a local minimum of every shrink pass:
    # no single deletion or lowering reaches the 6-step solution from it, so,
    # as with Hypothesis, which one is reported depends on the search path.
    var steps = (
        msg.count("state.fill_")
        + msg.count("state.pour_")
        + msg.count("state.empty_")
    )
    assert_true(steps == 6 or steps == 8, msg)


# --- A buggy set that loses elements above a threshold ---------------------


struct BuggySet(Movable):
    var items: List[Int]

    def __init__(out self):
        self.items = []

    def add(mut self, x: Int):
        if x > 10 and len(self.items) >= 2:
            return  # bug: silently drops the element
        for y in self.items:
            if y == x:
                return
        self.items.append(x)

    def contains(self, x: Int) -> Bool:
        for y in self.items:
            if y == x:
                return True
        return False


struct SetMachine(StateMachine):
    var real: BuggySet
    var model: List[Int]

    def __init__(out self):
        self.real = BuggySet()
        self.model = []

    def rule_count(self) -> Int:
        return 2

    def rule_name(self, rule: Int) -> String:
        return "add" if rule == 0 else "check"

    def precondition(self, rule: Int) -> Bool:
        return rule == 0 or len(self.model) > 0

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            var x = data.draw(integers(0, 100), "x")
            self.real.add(x)
            var found = False
            for y in self.model:
                if y == x:
                    found = True
            if not found:
                self.model.append(x)
        else:
            var i = data.draw(integers(0, len(self.model) - 1), "i")
            assert_true(
                self.real.contains(self.model[i]), "element went missing"
            )


def test_buggy_set_shrinks_to_minimal_program() raises:
    var msg = String()
    try:
        run_state_machine_as_test[SetMachine](Settings(database=None))
    except e:
        msg = String(e)
    assert_true("element went missing" in msg, msg)
    # minimal: two small adds, one add of 11, then a check of it
    assert_true("state.add(x=0)" in msg, msg)
    assert_true("state.add(x=1)" in msg, msg)
    assert_true("state.add(x=11)" in msg, msg)
    assert_true("state.check(i=2)" in msg, msg)
    assert_equal(msg.count("state.add"), 3, msg)
    assert_equal(msg.count("state.check"), 1, msg)


# --- Bundles ------------------------------------------------------------------


struct BundleMachine(StateMachine):
    var values: Bundle[Int]
    var total_drawn: Int

    def __init__(out self):
        self.values = Bundle[Int]("values")
        self.total_drawn = 0

    def rule_count(self) -> Int:
        return 2

    def rule_name(self, rule: Int) -> String:
        return "make" if rule == 0 else "use"

    def precondition(self, rule: Int) -> Bool:
        return rule == 0 or len(self.values) > 0

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            self.values.add(data.draw(integers(0, 1000), "v"))
        else:
            var v = self.values.draw(data)
            if v >= 500:
                fail("used a big value")


def test_bundle_values_flow_between_steps() raises:
    var msg = String()
    try:
        run_state_machine_as_test[BundleMachine](Settings(database=None))
    except e:
        msg = String(e)
    assert_true("used a big value" in msg, msg)
    assert_true("state.make(v=500)" in msg, msg)
    assert_true("state.use(values[0]=500)" in msg, msg)


# --- A passing machine, and initialize rules ----------------------------------


struct Counter(StateMachine):
    var n: Int
    var initialized: Int

    def __init__(out self):
        self.n = 0
        self.initialized = 0

    def rule_count(self) -> Int:
        return 2

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        assert_equal(self.initialized, 2, "initialize rules must run first")
        if rule == 0:
            self.n += data.draw(integers(0, 10))
        else:
            self.n = max(0, self.n - data.draw(integers(0, 10)))

    def initialize_count(self) -> Int:
        return 2

    def run_initialize(mut self, rule: Int, mut data: ConjectureData) raises:
        self.initialized += 1

    def check_invariants(self) raises:
        assert_true(self.n >= 0)


def test_passing_machine_with_initialize_rules() raises:
    run_state_machine_as_test[Counter](Settings(database=None, max_examples=50))


# --- Typed state machines ----------------------------------------------------


@fieldwise_init
struct Add(Copyable, Writable):
    var x: Int


@fieldwise_init
struct Check(Copyable, Writable):
    var i: Int


struct TypedSetMachine(TypedStateMachine):
    comptime Transition = Variant[Add, Check]
    var real: BuggySet
    var model: List[Int]

    def __init__(out self):
        self.real = BuggySet()
        self.model = []

    def transition(self, mut data: ConjectureData) raises -> Self.Transition:
        # only valid transitions: Check needs an element to look up
        if len(self.model) == 0 or data.draw(booleans()) == False:
            return Add(data.draw(integers(0, 100)))
        return Check(data.draw(integers(0, len(self.model) - 1)))

    def apply(mut self, t: Self.Transition) raises:
        if t.isa[Add]():
            var x = t[Add].x
            self.real.add(x)
            if x not in self.model:
                self.model.append(x)
        else:
            assert_true(
                self.real.contains(self.model[t[Check].i]),
                "element went missing",
            )


def test_typed_machine_shrinks_to_minimal_transitions() raises:
    var msg = String()
    try:
        run_typed_state_machine_as_test[TypedSetMachine](
            Settings(database=None)
        )
    except e:
        msg = String(e)
    assert_true("element went missing" in msg, msg)
    assert_true("state = TypedSetMachine()" in msg, msg)
    assert_true(
        "state.apply(Add(x=0))\n"
        + "    state.apply(Add(x=1))\n"
        + "    state.apply(Add(x=11))\n"
        + "    state.apply(Check(i=2))"
        in msg,
        msg,
    )
    assert_equal(msg.count("state.apply"), 4, msg)


@fieldwise_init
struct Jugs(Copyable, Writable):
    """A plain struct as the transition type: one of six operations."""

    var op: Int

    def write_to(self, mut writer: Some[Writer]):
        var names: List[String] = [
            "fill_small",
            "fill_big",
            "empty_small",
            "empty_big",
            "pour_small_into_big",
            "pour_big_into_small",
        ]
        writer.write(names[self.op])


struct TypedDieHard(TypedStateMachine):
    comptime Transition = Jugs
    var small: Int
    var big: Int

    def __init__(out self):
        self.small = 0
        self.big = 0

    def transition(self, mut data: ConjectureData) raises -> Jugs:
        return Jugs(data.draw(integers(0, 5)))

    def precondition(self, t: Jugs) -> Bool:
        # pointless moves are rejected rather than avoided, to exercise
        # preconditions: filling a full jug or emptying an empty one
        return not (
            (t.op == 0 and self.small == 3)
            or (t.op == 1 and self.big == 5)
            or (t.op == 2 and self.small == 0)
            or (t.op == 3 and self.big == 0)
        )

    def apply(mut self, t: Jugs) raises:
        if t.op == 0:
            self.small = 3
        elif t.op == 1:
            self.big = 5
        elif t.op == 2:
            self.small = 0
        elif t.op == 3:
            self.big = 0
        elif t.op == 4:
            var old_big = self.big
            self.big = min(5, self.big + self.small)
            self.small = self.small - (self.big - old_big)
        else:
            var old_small = self.small
            self.small = min(3, self.small + self.big)
            self.big = self.big - (self.small - old_small)

    def check_invariants(self) raises:
        assert_true(0 <= self.small and self.small <= 3)
        assert_true(0 <= self.big and self.big <= 5)
        if self.big == 4:
            fail("big jug holds 4 gallons")


def test_typed_die_hard_with_preconditions() raises:
    var msg = String()
    try:
        run_typed_state_machine_as_test[TypedDieHard](
            Settings(database=None, max_examples=10000)
        )
    except e:
        msg = String(e)
    assert_true("big jug holds 4 gallons" in msg, msg)
    assert_true("state.apply(fill_" in msg, msg)
    var steps = msg.count("state.apply(")
    assert_true(steps == 6 or steps == 8, msg)


# --- deadlines apply to each step -----------------------------------------


struct SlowStep(StateMachine):
    var n: Int

    def __init__(out self):
        self.n = 0

    def rule_count(self) -> Int:
        return 1

    def rule_name(self, rule: Int) -> String:
        return "step"

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 10), "x")
        if x > 5:
            sleep(0.3)  # past the 250 ms (200 ms + 25% grace) limit
        self.n += 1


def test_slow_step_exceeds_deadline() raises:
    var msg = String()
    try:
        run_state_machine_as_test[SlowStep](Settings(database=None))
    except e:
        msg = String(e)
    assert_true("DeadlineExceeded" in msg, msg)
    assert_true("state.step(x=6)" in msg, msg)
    # ... and deadline=None turns it off
    run_state_machine_as_test[SlowStep](
        Settings(
            database=None, deadline=None, max_examples=3, stateful_step_count=3
        )
    )


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
