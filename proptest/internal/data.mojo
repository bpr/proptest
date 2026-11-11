# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""`ConjectureData`: one run of a test function over a choice sequence.

Port of `hypothesis.internal.conjecture.data`. A `ConjectureData` either
replays a *prefix* of choices (for shrinking and the example database) or
draws fresh choices from the generation provider, records every choice as
a `ChoiceNode`, and records *spans* -- the nested structure of strategy
draws -- which the shrinker uses to make structural changes.

Control flow: Hypothesis raises `StopTest` to abandon a test case; proptest
raises an `Error` whose message is `STOP_TEST` after setting `status`, and
the engine recognizes it. `assume()` raises `UNSATISFIED_ASSUMPTION`.
"""

from std.memory import ArcPointer
from std.memory.alloc import unsafe_alloc
from std.reflection import reflect
from std.time import perf_counter_ns
from std.hash import hash
from std.collections import Dict
from std.math import isnan

from proptest.internal.choice import (
    ChoiceValue,
    ChoiceNode,
    Constraints,
    INTEGER,
    FLOAT,
    BOOLEAN,
    BYTES,
    STRING,
    choice_permitted,
    choice_simplest,
    choice_size,
    COLLECTION_DEFAULT_MAX_SIZE,
)
from proptest.internal.floats import (
    float_to_int,
    int_to_float,
    neg_inf,
    pos_inf,
    smallest_subnormal,
)
from proptest.internal.intervals import IntervalSet
from proptest.internal.fork import (
    ForkLog,
    LogReader,
    TAG_NODE,
    TAG_SPAN_START,
    TAG_SPAN_STOP,
    TAG_ARG_SPAN,
    TAG_NOTE,
    TAG_END,
)
from proptest.internal.random import Random
from proptest.internal.provider import Provider
from proptest.strategies.strategy import Strategy, format_value


comptime STOP_TEST = "proptest.StopTest"
"""Message of the `Error` that abandons the current test case."""
comptime UNSATISFIED_ASSUMPTION = "proptest.UnsatisfiedAssumption"
"""Message of the `Error` raised by a failed `assume()`."""

comptime BUFFER_SIZE = 8 * 1024
"""Maximum serialized size of one test case (Hypothesis's BUFFER_SIZE)."""
comptime MAX_DEPTH = 100
"""Maximum nesting of strategy draws before a test case is invalid."""


def is_stop_test(e: Error) -> Bool:
    return String(e) == STOP_TEST


def is_unsatisfied_assumption(e: Error) -> Bool:
    return String(e) == UNSATISFIED_ASSUMPTION


struct Status(
    Comparable, Copyable, Equatable, TrivialRegisterPassable, Writable
):
    """The outcome of a test case, ordered as in Hypothesis."""

    var value: Int

    comptime OVERRUN = Status(0)
    comptime INVALID = Status(1)
    comptime VALID = Status(2)
    comptime INTERESTING = Status(3)

    def __init__(out self, value: Int):
        self.value = value

    def __eq__(self, other: Self) -> Bool:
        return self.value == other.value

    def __lt__(self, other: Self) -> Bool:
        return self.value < other.value

    def write_to(self, mut writer: Some[Writer]):
        if self.value == 0:
            writer.write("OVERRUN")
        elif self.value == 1:
            writer.write("INVALID")
        elif self.value == 2:
            writer.write("VALID")
        else:
            writer.write("INTERESTING")


def calc_label_from_name(name: StringSlice) -> UInt64:
    """A label for a span, derived from a name."""
    return hash(String(name))


def combine_labels(a: UInt64, b: UInt64) -> UInt64:
    """Combine two labels into one (order-sensitive)."""
    var x = a * 0x9E3779B97F4A7C15 + b
    x ^= x >> 31
    x *= 0xBF58476D1CE4E5B9
    return x ^ (x >> 29)


comptime TOP_LABEL: UInt64 = 0x746F70  # "top"
comptime ONE_FROM_MANY_LABEL: UInt64 = 0x6F6E655F6D616E79
comptime FILTER_LABEL: UInt64 = 0x66696C746572
comptime ONE_OF_LABEL: UInt64 = 0x6F6E655F6F66
comptime SAMPLE_LABEL: UInt64 = 0x73616D706C65
comptime UNIQUE_LABEL: UInt64 = 0x756E69717565


struct Span(Copyable, Writable):
    """A contiguous run of choices made by one strategy draw."""

    var label: UInt64
    var start: Int
    """Index of the first node in the span."""
    var end: Int
    """Index one past the last node in the span."""
    var parent: Int
    """Index of the parent span, or -1 for the top span."""
    var depth: Int
    var discarded: Bool

    def __init__(out self, label: UInt64, start: Int, parent: Int, depth: Int):
        self.label = label
        self.start = start
        self.end = start
        self.parent = parent
        self.depth = depth
        self.discarded = False

    def choice_count(self) -> Int:
        return self.end - self.start

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "Span(start=",
            self.start,
            ", end=",
            self.end,
            ", depth=",
            self.depth,
        )
        if self.discarded:
            writer.write(", discarded")
        writer.write(")")


# ===----------------------------------------------------------------------=== #
# Type-erased values (for shared())
# ===----------------------------------------------------------------------=== #

comptime _ErasedPtr = MutOpaquePointer[MutUntrackedOrigin]


struct ErasedValue(Movable):
    """A heap-allocated value of any copyable type, remembering its type's
    name so it can only be read back as that type."""

    var _ptr: _ErasedPtr
    var _free: def(_ErasedPtr) thin
    var type_name: String

    def __init__[T: Copyable & Deinitable](out self, var value: T):
        def free_(p: _ErasedPtr):
            var q = p.unsafe_bitcast[T]()
            _ = q.unsafe_take_pointee()
            q.unsafe_free()

        var q = unsafe_alloc[T](1)
        q.unsafe_write(value^)
        self._ptr = q.unsafe_bitcast[NoneType]()
        self._free = free_
        self.type_name = String(reflect[T].name())

    def __deinit__(deinit self):
        self._free(self._ptr)

    def get[T: Copyable & Deinitable](self) raises -> T:
        """A copy of the value, which must be a `T`."""
        if self.type_name != String(reflect[T].name()):
            raise Error(
                String(
                    "InvalidArgument: shared() key holds a ",
                    self.type_name,
                    " but was drawn as a ",
                    reflect[T].name(),
                )
            )
        return self._ptr.unsafe_bitcast[T]()[].copy()


# ===----------------------------------------------------------------------=== #
# Results
# ===----------------------------------------------------------------------=== #


struct ConjectureResult(Copyable):
    """The frozen record of a finished test case."""

    var id: Int
    """Unique per test case, used for identity comparisons."""
    var status: Status
    var nodes: List[ChoiceNode]
    var spans: List[Span]
    var interesting_origin: String
    var has_discards: Bool
    var target_observations: Dict[String, Float64]
    var notes: List[String]
    var events: List[String]
    var table_entries: List[Tuple[String, String]]
    var covers: Dict[String, Float64]
    var covered: Dict[String, Bool]
    var length: Int
    var misaligned: Bool
    var draw_time_ns: Int
    """Time spent in top-level draws (generating data)."""
    var arg_spans: List[Int]
    """Indices of the spans of top-level draws (the test's arguments)."""
    var hit_max_choices: Bool
    """Overran because of a limit on the number of choices (a prefix that
    ran out, or a size limit set by the engine), not because the data was
    too large."""

    def __init__(out self, *, id: Int, status: Status):
        self.id = id
        self.status = status
        self.nodes = List[ChoiceNode]()
        self.spans = List[Span]()
        self.interesting_origin = String()
        self.has_discards = False
        self.target_observations = Dict[String, Float64]()
        self.notes = List[String]()
        self.events = List[String]()
        self.table_entries = List[Tuple[String, String]]()
        self.covers = Dict[String, Float64]()
        self.covered = Dict[String, Bool]()
        self.length = 0
        self.misaligned = False
        self.draw_time_ns = 0
        self.hit_max_choices = False
        self.arg_spans = List[Int]()

    def choices(self) -> List[ChoiceValue]:
        var out = List[ChoiceValue](capacity=len(self.nodes))
        for n in self.nodes:
            out.append(n.value.copy())
        return out^

    def span_children(self, i: Int) -> List[Int]:
        """Indices of the direct children of span `i`."""
        var out = List[Int]()
        for j in range(i + 1, len(self.spans)):
            if (
                self.spans[j].start >= self.spans[i].end
                and self.spans[j].start > self.spans[i].start
            ):
                break
            if self.spans[j].parent == i:
                out.append(j)
        return out^


comptime Result = ArcPointer[ConjectureResult]
"""Results are shared, like Python objects, so copies are cheap."""


# ===----------------------------------------------------------------------=== #
# ConjectureData
# ===----------------------------------------------------------------------=== #


struct ConjectureData(Movable):
    """The state of one test case while it runs."""

    var prefix: List[ChoiceValue]
    var index: Int
    """Position in `prefix` of the next choice to replay."""
    var extend_simplest: Bool
    """When the prefix runs out, draw simplest choices instead of random ones
    (Hypothesis's `ChoiceTemplate("simplest")`)."""
    var max_choices: Int
    """Overrun after this many choices (-1 for no limit)."""
    var max_length: Int
    var length: Int
    var nodes: List[ChoiceNode]
    var spans: List[Span]
    var span_stack: List[Int]
    var depth: Int
    var max_depth: Int
    var status: Status
    var frozen: Bool
    var interesting_origin: String
    var has_discards: Bool
    var misaligned: Bool
    var notes: List[String]
    var events: List[String]
    var table_entries: List[Tuple[String, String]]
    """Values recorded with `tabulate`, as (table, value)."""
    var covers: Dict[String, Float64]
    """Coverage requirements (percentages) declared with `cover`."""
    var covered: Dict[String, Bool]
    """Coverage labels whose condition held in this test case."""
    var target_observations: Dict[String, Float64]
    var provider: Provider
    var id: Int
    var leaf_budgets: List[Int]
    """Stack of remaining leaf counts for nested `recursive()` strategies."""
    var report_draws: Bool
    """Record top-level interactive draws as notes (set by `given_data`)."""
    var is_final: Bool
    """This is the final replay of a failing example, whose notes and
    draws are reported."""
    var draw_count: Int
    var report_depth: Int
    """Draws at this span depth count as top-level for reporting."""
    var collect_step_draws: Bool
    """Collect `label=value` for top-level draws into `step_draws` (used to
    print stateful steps)."""
    var step_draws: List[String]
    var draw_time_ns: Int
    var hit_max_choices: Bool
    var arg_spans: List[Int]
    var arg_comments: Dict[Int, String]
    """Explain-phase comments for the final report, by argument number."""
    var explain_note: String
    var shared_values: Dict[String, ErasedValue]
    """Values drawn by `shared()` strategies, by key."""
    var live_tokens: List[ArcPointer[Bool]]
    """Set to False when the test case ends; generated functions
    (`functions()`) check theirs before drawing."""
    var fork_log: Optional[ForkLog]
    """In a forked child (`Settings(fork=True)`), where to record the test
    case as it runs, for the parent to rebuild if the child crashes."""

    def __init__(
        out self,
        var prefix: List[ChoiceValue],
        var provider: Provider,
        *,
        id: Int = 0,
        max_choices: Int = -1,
        extend_simplest: Bool = False,
        max_length: Int = BUFFER_SIZE,
    ):
        self.prefix = prefix^
        self.index = 0
        self.extend_simplest = extend_simplest
        self.max_choices = max_choices
        self.max_length = max_length
        self.length = 0
        self.nodes = List[ChoiceNode]()
        self.spans = List[Span]()
        self.span_stack = List[Int]()
        self.depth = -1
        self.max_depth = 0
        self.status = Status.VALID
        self.frozen = False
        self.interesting_origin = String()
        self.has_discards = False
        self.misaligned = False
        self.notes = List[String]()
        self.events = List[String]()
        self.table_entries = List[Tuple[String, String]]()
        self.covers = Dict[String, Float64]()
        self.covered = Dict[String, Bool]()
        self.target_observations = Dict[String, Float64]()
        self.provider = provider^
        self.id = id
        self.leaf_budgets = List[Int]()
        self.report_draws = False
        self.is_final = False
        self.draw_count = 0
        self.report_depth = 0
        self.collect_step_draws = False
        self.step_draws = List[String]()
        self.draw_time_ns = 0
        self.hit_max_choices = False
        self.arg_spans = List[Int]()
        self.arg_comments = Dict[Int, String]()
        self.explain_note = String()
        self.shared_values = Dict[String, ErasedValue]()
        self.live_tokens = List[ArcPointer[Bool]]()
        self.fork_log = None
        # the top span (depth 0)
        self.depth = 0
        self.span_stack.append(0)
        self.spans.append(Span(TOP_LABEL, 0, -1, 0))

    # ===------------------------------------------------------------------=== #
    # Drawing choices
    # ===------------------------------------------------------------------=== #

    def _draw(
        mut self, var constraints: Constraints, forced: Optional[ChoiceValue]
    ) raises -> ChoiceValue:
        if self.frozen:
            raise Error("proptest: cannot draw from a frozen test case")
        if self.length >= self.max_length:
            self.mark_overrun()
        if self.max_choices >= 0 and len(self.nodes) >= self.max_choices:
            self.hit_max_choices = True
            self.mark_overrun()
        var value: ChoiceValue
        if self.index < len(self.prefix):
            value = self._pop_choice(constraints)
            if forced:
                value = forced.value().copy()
        elif forced:
            value = forced.value().copy()
        elif self.extend_simplest:
            value = choice_simplest(constraints)
        else:
            value = self.provider.draw(constraints)
        if value.kind == FLOAT and isnan(value.f):
            value = ChoiceValue(float=int_to_float(float_to_int(value.f)))
        var size = choice_size(value)
        if self.length + size > self.max_length:
            self.mark_overrun()
        self.nodes.append(
            ChoiceNode(
                value.copy(), constraints^, Bool(forced), index=len(self.nodes)
            )
        )
        self.length += size
        if self.fork_log:
            ref log = self.fork_log.value()
            ref node = self.nodes[len(self.nodes) - 1]
            log.begin(TAG_NODE)
            log.value(node.value)
            log.constraints(node.constraints)
            log.bool(node.was_forced)
            log.commit()
        return value^

    def _pop_choice(mut self, constraints: Constraints) raises -> ChoiceValue:
        var value = self.prefix[self.index].copy()
        self.index += 1
        if value.kind != constraints.kind or not choice_permitted(
            value, constraints
        ):
            # Misaligned: the prefix doesn't fit what the test now draws.
            self.misaligned = True
            if value.kind == INTEGER and constraints.kind == INTEGER:
                # Unlike Hypothesis (which uses the simplest choice), clamp
                # an out-of-range integer into range: after the shrinker
                # deletes part of a collection, an index into it then keeps
                # pointing at the end instead of jumping to the start.
                var v = value.i
                if constraints.has_min and v < constraints.min_value:
                    v = constraints.min_value
                if constraints.has_max and v > constraints.max_value:
                    v = constraints.max_value
                return ChoiceValue(integer=v)
            return choice_simplest(constraints)
        return value^

    def draw_integer(
        mut self,
        min_value: Optional[Int128] = None,
        max_value: Optional[Int128] = None,
        *,
        shrink_towards: Int128 = 0,
        forced: Optional[Int128] = None,
        weights: Optional[ArcPointer[List[Float64]]] = None,
    ) raises -> Int128:
        """Draw an integer in the (optionally bounded) range. `weights`, if
        given, are the probabilities of generating `min_value`,
        `min_value + 1`, ..., `max_value`."""
        var f: Optional[ChoiceValue] = None
        if forced:
            f = ChoiceValue(integer=forced.value())
        var v = self._draw(
            Constraints.integer(min_value, max_value, shrink_towards, weights),
            f,
        )
        return v.i

    def draw_float(
        mut self,
        min_value: Float64 = neg_inf(),
        max_value: Float64 = pos_inf(),
        *,
        allow_nan: Bool = True,
        smallest_nonzero_magnitude: Float64 = smallest_subnormal(),
        forced: Optional[Float64] = None,
    ) raises -> Float64:
        """Draw a float in `[min_value, max_value]`."""
        var f: Optional[ChoiceValue] = None
        if forced:
            f = ChoiceValue(float=forced.value())
        var v = self._draw(
            Constraints.float(
                min_value, max_value, allow_nan, smallest_nonzero_magnitude
            ),
            f,
        )
        return v.f

    def draw_boolean(
        mut self, p: Float64 = 0.5, *, forced: Optional[Bool] = None
    ) raises -> Bool:
        """Draw a boolean which is True with probability `p`."""
        var f: Optional[ChoiceValue] = None
        if forced:
            f = ChoiceValue(boolean=forced.value())
        var v = self._draw(Constraints.boolean(p), f)
        return v.as_bool()

    def draw_bytes(
        mut self,
        min_size: Int = 0,
        max_size: Int = COLLECTION_DEFAULT_MAX_SIZE,
    ) raises -> List[UInt8]:
        """Draw a byte string with length in `[min_size, max_size]`."""
        var v = self._draw(Constraints.bytes(min_size, max_size), None)
        var out = List[UInt8](capacity=len(v.seq))
        for b in v.seq:
            out.append(UInt8(b))
        return out^

    def draw_string(
        mut self,
        intervals: ArcPointer[IntervalSet],
        min_size: Int = 0,
        max_size: Int = COLLECTION_DEFAULT_MAX_SIZE,
    ) raises -> List[UInt32]:
        """Draw a string, as codepoints from `intervals`."""
        var v = self._draw(
            Constraints.string(intervals, min_size, max_size), None
        )
        return v.seq.copy()

    def draw[
        S: Strategy
    ](mut self, strategy: S, label: String = "") raises -> S.Value:
        """Draw a value from `strategy`. This is how composite strategies,
        interactive tests (`given_data`) and stateful rules draw data."""
        var top_level = self.depth == self.report_depth
        var start = perf_counter_ns() if top_level else 0
        if top_level:
            self.arg_spans.append(len(self.spans))
            if self.fork_log:
                self.fork_log.value().begin(TAG_ARG_SPAN)
                self.fork_log.value().int(len(self.spans))
                self.fork_log.value().commit()
        self.start_span(strategy.label())
        var v = strategy.do_draw(self)
        self.stop_span()
        if top_level:
            self.draw_time_ns += perf_counter_ns() - start
            self.draw_count += 1
            if self.is_final and self.collect_step_draws:
                if label.byte_length() > 0:
                    self.step_draws.append(String(label, "=", format_value(v)))
                else:
                    self.step_draws.append(format_value(v))
            elif self.report_draws and self.is_final:
                var line = String("Draw ", self.draw_count)
                if label.byte_length() > 0:
                    line += String(" (", label, ")")
                line += String(": ", format_value(v))
                line += self.arg_comment(self.draw_count - 1)
                self.note(line)
        return v^

    def arg_comment(self, i: Int) -> String:
        """The explain-phase comment for argument `i` (`"  # ..."`), if any."""
        try:
            if i in self.arg_comments:
                return String("  # ", self.arg_comments[i])
        except:
            pass
        return String()

    # ===------------------------------------------------------------------=== #
    # Spans
    # ===------------------------------------------------------------------=== #

    def start_span(mut self, label: UInt64) raises:
        """Begin a span (a strategy draw) with the given label."""
        self.depth += 1
        if self.depth > self.max_depth:
            self.max_depth = self.depth
        var parent = (
            self.span_stack[len(self.span_stack) - 1] if len(self.span_stack)
            > 0 else -1
        )
        self.span_stack.append(len(self.spans))
        self.spans.append(Span(label, len(self.nodes), parent, self.depth))
        if self.fork_log:
            self.fork_log.value().begin(TAG_SPAN_START)
            self.fork_log.value().u64(label)
            self.fork_log.value().commit()
        if self.depth > MAX_DEPTH:
            self.mark_invalid("max depth exceeded")

    def stop_span(mut self, discard: Bool = False):
        """End the innermost span; `discard` marks its choices as not
        contributing to the final value (e.g. a rejected filter draw)."""
        if self.frozen or len(self.span_stack) == 0:
            return
        if self.fork_log:
            self.fork_log.value().begin(TAG_SPAN_STOP)
            self.fork_log.value().bool(discard)
            self.fork_log.value().commit()
        var i = self.span_stack.pop()
        self.spans[i].end = len(self.nodes)
        if discard:
            self.spans[i].discarded = True
            self.has_discards = True
        self.depth -= 1

    # ===------------------------------------------------------------------=== #
    # Concluding
    # ===------------------------------------------------------------------=== #

    def __deinit__(deinit self):
        # generated functions keep a pointer to this test case: make sure
        # they stop using it, whether or not the test case was frozen
        for t in self.live_tokens:
            t[] = False

    def freeze(mut self):
        if self.frozen:
            return
        while len(self.span_stack) > 0:
            self.stop_span()
        self.frozen = True
        for t in self.live_tokens:
            t[] = False

    def conclude_test(mut self, status: Status, origin: String = "") raises:
        """Mark the test case finished with `status` and abandon it."""
        self.status = status
        if status == Status.INTERESTING:
            self.interesting_origin = origin
        self.freeze()
        raise Error(STOP_TEST)

    def mark_overrun(mut self) raises:
        self.conclude_test(Status.OVERRUN)

    def mark_invalid(mut self, why: String = "") raises:
        if why:
            self.events.append(String("invalid because: ", why))
        self.conclude_test(Status.INVALID)

    def note(mut self, msg: String):
        self.notes.append(msg)
        self.log_note(msg)

    def log_note(mut self, msg: String):
        """Record a note of the final replay in the fork log only: if the
        child crashes, the notes in the log are the ones reported."""
        if self.fork_log and self.is_final:
            self.fork_log.value().begin(TAG_NOTE)
            self.fork_log.value().string(msg)
            self.fork_log.value().commit()

    # ===------------------------------------------------------------------=== #
    # Forked test cases
    # ===------------------------------------------------------------------=== #

    def log_end(mut self, msg: String):
        """In the child, after the test case is frozen: record the rest of
        its result, and the error message `msg` if it failed."""
        if not self.fork_log:
            return
        ref log = self.fork_log.value()
        log.begin(TAG_END)
        log.int(self.status.value)
        log.string(self.interesting_origin)
        log.string(msg)
        log.bool(self.has_discards)
        log.bool(self.misaligned)
        log.int(self.length)
        log.int(self.draw_time_ns)
        log.bool(self.hit_max_choices)
        log.strings(self.notes)
        log.strings(self.events)
        log.int(len(self.table_entries))
        for e in self.table_entries:
            log.string(e[0])
            log.string(e[1])
        log.int(len(self.covers))
        for item in self.covers.items():
            log.string(item.key)
            log.f64(item.value)
        log.int(len(self.covered))
        for item in self.covered.items():
            log.string(item.key)
            log.bool(item.value)
        log.int(len(self.target_observations))
        for item in self.target_observations.items():
            log.string(item.key)
            log.f64(item.value)
        log.int(len(self.arg_spans))
        for a in self.arg_spans:
            log.int(a)
        log.int(len(self.spans))
        for sp in self.spans:
            log.u64(sp.label)
            log.int(sp.start)
            log.int(sp.end)
            log.int(sp.parent)
            log.int(sp.depth)
            log.bool(sp.discarded)
        log.commit()

    def load_fork_log(mut self, mut r: LogReader) raises -> Optional[String]:
        """In the parent: fill in this (unused) test case from a child's
        log, and freeze it. Returns the error message if the child
        finished the test case, or None if it died first (the test case
        then holds what the child did up to that point).

        The child may have corrupted its memory, so nothing in the log is
        trusted: raises if it is inconsistent, leaving the test case frozen
        with the nodes read so far and no structure."""
        try:
            return self._load_fork_log(r)
        except e:
            self.spans = [Span(TOP_LABEL, 0, -1, 0)]
            self.spans[0].end = len(self.nodes)
            self.span_stack = []
            self.arg_spans = []
            self.notes = []
            self.freeze()
            raise e^

    def _load_fork_log(mut self, mut r: LogReader) raises -> Optional[String]:
        var crash_notes = List[String]()
        while r.more():
            var tag = r.u8()
            if tag == TAG_NODE:
                var v = r.value()
                var c = r.constraints()
                var forced = r.bool()
                if not choice_permitted(v, c):
                    raise Error("a choice its constraints don't permit")
                if c.weights and (
                    not c.has_min
                    or not c.has_max
                    or Int128(len(c.weights.value()[]))
                    != c.max_value - c.min_value + 1
                ):
                    raise Error("weights that don't match their range")
                self.length += choice_size(v)
                self.nodes.append(
                    ChoiceNode(v^, c^, forced, index=len(self.nodes))
                )
            elif tag == TAG_SPAN_START:
                var label = r.u64()
                self.depth += 1
                var parent = self.span_stack[len(self.span_stack) - 1]
                self.span_stack.append(len(self.spans))
                self.spans.append(
                    Span(label, len(self.nodes), parent, self.depth)
                )
            elif tag == TAG_SPAN_STOP:
                self.stop_span(r.bool())
            elif tag == TAG_ARG_SPAN:
                self.arg_spans.append(r.int())
            elif tag == TAG_NOTE:
                crash_notes.append(r.string())
            elif tag == TAG_END:
                self.status = Status(r.int())
                self.interesting_origin = r.string()
                var msg = r.string()
                self.has_discards = r.bool()
                self.misaligned = r.bool()
                self.length = r.int()
                self.draw_time_ns = r.int()
                self.hit_max_choices = r.bool()
                self.notes = r.strings()
                self.events = r.strings()
                self.table_entries = []
                for _ in range(r.int()):
                    var table = r.string()
                    self.table_entries.append((table, r.string()))
                self.covers = {}
                for _ in range(r.int()):
                    var k = r.string()
                    self.covers[k] = r.f64()
                self.covered = {}
                for _ in range(r.int()):
                    var k = r.string()
                    self.covered[k] = r.bool()
                self.target_observations = {}
                for _ in range(r.int()):
                    var k = r.string()
                    self.target_observations[k] = r.f64()
                self.arg_spans = []
                for _ in range(r.int()):
                    self.arg_spans.append(r.int())
                self.spans = []
                for _ in range(r.int()):
                    var label = r.u64()
                    var start = r.int()
                    var sp = Span(label, start, 0, 0)
                    sp.end = r.int()
                    sp.parent = r.int()
                    sp.depth = r.int()
                    sp.discarded = r.bool()
                    self.spans.append(sp^)
                self.span_stack = []
                self.freeze()
                if self.status.value < 0 or self.status.value > 3:
                    raise Error("a bad status")
                self._check_structure()
                return msg
            else:
                raise Error("proptest: bad fork log record ", Int(tag))
        self.notes = crash_notes^
        self.freeze()
        self._check_structure()
        return None

    def _check_structure(self) raises:
        """Raise unless the spans nest within the nodes, and the argument
        spans are spans."""
        var n = len(self.nodes)
        if len(self.spans) == 0 or self.spans[0].start != 0:
            raise Error("no top span")
        for i in range(len(self.spans)):
            ref sp = self.spans[i]
            if not (0 <= sp.start <= sp.end <= n):
                raise Error("a span outside the choices")
            if i > 0 and not (0 <= sp.parent < i):
                raise Error("a span with a bad parent")
            if i > 0 and sp.depth != self.spans[sp.parent].depth + 1:
                raise Error("a span at the wrong depth")
        for a in self.arg_spans:
            if not (0 < a < len(self.spans)):
                raise Error("a bad argument span")
        if self.length < 0 or self.draw_time_ns < 0:
            raise Error("a bad length")

    def event(mut self, msg: String):
        """Record that something happened in this test case. Run statistics
        (`Settings(show_statistics=True)`) give the share of test cases
        that recorded each event (Hypothesis's `event`)."""
        self.events.append(msg)

    def tabulate(mut self, table: String, value: String):
        """Add `value` to the table `table`. Run statistics show how often
        each value occurred (QuickCheck's `tabulate`)."""
        self.table_entries.append((table, value))

    def cover(mut self, percent: Float64, condition: Bool, label: String):
        """Require that at least `percent`% of passing test cases satisfy
        `condition` (QuickCheck's `cover`). A requirement that isn't met
        is a warning, or with `Settings(check_coverage=Confidence())` a
        statistically checked failure. Calling it several times in one
        test case counts the case if any call's condition holds."""
        if label not in self.covers:
            self.covers[label] = percent
        if condition:
            self.covered[label] = True

    def target(mut self, score: Float64, label: String = ""):
        self.target_observations[label] = score

    def as_result(self) -> ConjectureResult:
        var r = ConjectureResult(id=self.id, status=self.status)
        r.nodes = self.nodes.copy()
        r.spans = self.spans.copy()
        r.interesting_origin = self.interesting_origin
        r.has_discards = self.has_discards
        r.target_observations = self.target_observations.copy()
        r.notes = self.notes.copy()
        r.events = self.events.copy()
        r.table_entries = self.table_entries.copy()
        r.covers = self.covers.copy()
        r.covered = self.covered.copy()
        r.length = self.length
        r.misaligned = self.misaligned
        r.draw_time_ns = self.draw_time_ns
        r.hit_max_choices = self.hit_max_choices
        r.arg_spans = self.arg_spans.copy()
        return r^

    def choices(self) -> List[ChoiceValue]:
        var out = List[ChoiceValue](capacity=len(self.nodes))
        for n in self.nodes:
            out.append(n.value.copy())
        return out^
