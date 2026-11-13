# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Running a property as a fuzz target: Hypothesis's `fuzz_one_input`.

`fuzz_target(strategies..., test)` takes the same arguments as `given`,
but instead of running the test it returns a `FuzzTarget`, whose
`fuzz_one_input(bytes)` runs the test once on inputs read from `bytes`:

```mojo
var target = fuzz_target(lists(integers()), prop)
for input in inputs_from_a_fuzzer:
    _ = target.fuzz_one_input(input)
```

The bytes are read as the test's choices (see
`internal/bytestring.mojo`), so a byte-level fuzzer drives the strategies.
A failure is saved to the example database before its error is re-raised,
so `given` replays and shrinks it on the next run, as long as both use the
same `Settings.database_key` (each defaults to its call site).

`target.fuzz(seconds)` is a fuzzer of its own, with no bytes involved: a
loop that keeps a corpus of choice sequences that covered something new
and mutates them, then shrinks and reports any failures as `given` does.
Hypothesis has no such loop (HypoFuzz, a separate project, is one).
"""

from std.collections import Set
from std.hash import hash
from std.memory.alloc import unsafe_alloc
from std.reflection import call_location, SourceLocation
from std.time import perf_counter_ns

from proptest.core import (
    _log_given,
    _note_given,
    _raise_failures,
    _resolve_settings,
    shrink_and_replay,
)
from proptest.internal.bytestring import ByteReader, encode_choices
from proptest.internal.choice import (
    ChoiceValue,
    Constraints,
    INTEGER,
    FLOAT,
    BOOLEAN,
    BYTES,
    choice_permitted,
    choice_simplest,
    sort_key_less,
)
from proptest.internal.data import (
    BUFFER_SIZE,
    ConjectureData,
    ConjectureResult,
    Result,
    Status,
)
from proptest.internal.provider import _boundary_byte
from proptest.internal.datatree import DataTree
from proptest.internal.engine import ConjectureRunner, RunReport
from proptest.internal.floats import (
    float_nan,
    neg_inf,
    next_up,
    pos_inf,
    smallest_subnormal,
)
from proptest.internal.random import Random
from proptest.settings import Settings, Verbosity
from proptest.strategies.strategy import Strategy, format_value

comptime _ErasedPtr = MutOpaquePointer[MutUntrackedOrigin]


def _fuzz_one[
    F: def(mut ConjectureData) raises
](mut runner: ConjectureRunner[F], buffer: List[UInt8]) raises -> Optional[
    List[UInt8]
]:
    var data = runner.new_data(List[ChoiceValue]())
    var n = min(len(buffer), BUFFER_SIZE)
    data.byte_reader = ByteReader(List[UInt8](buffer[:n]))
    var msg = runner.execute(data)
    if data.status == Status.INTERESTING:
        # Save only the simplest failure seen so far for each origin, so a
        # long run makes a logarithmic number of writes (as in Hypothesis).
        var origin = data.interesting_origin
        var known = runner.interesting.get(origin)
        if not known or not sort_key_less(known.value()[].nodes, data.nodes):
            if runner.db and runner.db_key.byte_length() > 0:
                runner.db.value().save(runner.db_key, data.choices())
            runner.interesting[origin] = Result(data.as_result())
        raise Error(msg)
    if data.status != Status.VALID:
        return None
    return encode_choices(data.nodes)


# ===----------------------------------------------------------------------=== #
# The fuzz loop
# ===----------------------------------------------------------------------=== #

comptime _MAX_TREE_NODES = 200_000
"""The DataTree is cleared when it grows past this many nodes: a long
fuzzing run records every test case in it."""


def _mix(a: UInt64, b: UInt64) -> UInt64:
    var z = (a ^ (b + 0x9E3779B97F4A7C15 + (a << 6) + (a >> 2))) * (
        0xBF58476D1CE4E5B9
    )
    return z ^ (z >> 31)


def _bucket(n: Int) -> UInt64:
    """AFL's hit-count buckets: 1, 2, 3, 4-7, 8-15, 16-31, 32-127, 128+."""
    if n <= 3:
        return UInt64(n)
    if n < 8:
        return 4
    if n < 16:
        return 5
    if n < 32:
        return 6
    if n < 128:
        return 7
    return 8


def _features(r: ConjectureResult) -> List[UInt64]:
    """What a test case covers, in place of code coverage: each pair of a
    strategy and the strategy that drew it (by span label), with how often
    it occurred (bucketed), and each event."""
    var counts = Dict[UInt64, Int]()
    for s in r.spans:
        var parent = r.spans[s.parent].label if s.parent >= 0 else UInt64(0)
        var edge = _mix(parent, s.label)
        counts[edge] = counts.get(edge, 0) + 1
    var out = List[UInt64]()
    for item in counts.items():
        out.append(_mix(item.key, _bucket(item.value)))
    for e in r.events:
        out.append(_mix(0x6576656E74, UInt64(hash(e))))
    return out^


struct _Corpus(Movable):
    """The valid test cases that covered something new."""

    var entries: List[Result]
    var seen: Set[UInt64]
    var best: Dict[String, Float64]
    """The best score seen for each `target` label."""

    def __init__(out self):
        self.entries = List[Result]()
        self.seen = Set[UInt64]()
        self.best = Dict[String, Float64]()

    def add(mut self, r: Result) -> Bool:
        """Keep `r` if it covers a new feature or improves a target score."""
        if r[].status != Status.VALID:
            return False
        var novel = False
        for f in _features(r[]):
            if f not in self.seen:
                self.seen.add(f)
                novel = True
        for item in r[].target_observations.items():
            var best = self.best.get(item.key)
            if not best or item.value > best.value():
                self.best[item.key] = item.value
                novel = True
        if novel:
            self.entries.append(r)
        return novel


def _boundary(mut rnd: Random, c: Constraints, v: ChoiceValue) -> ChoiceValue:
    """A value at an edge of `c`, or near `v`: the values bugs hide at."""
    var out: ChoiceValue
    if c.kind == INTEGER:
        var x = v.i
        var k = rnd.below(8)
        var y: Int128
        if k == 0:
            y = c.min_value if c.has_min else Int128(Int64.MIN)
        elif k == 1:
            y = c.max_value if c.has_max else Int128(Int64.MAX)
        elif k == 2:
            y = x + 1
        elif k == 3:
            y = x - 1
        elif k == 4:
            y = -x
        elif k == 5:
            y = c.shrink_towards
        else:
            # just below or at a power of two that bounds a machine type
            var bits: List[Int] = [7, 8, 15, 16, 31, 32, 63, 64]
            var b = bits[Int(rnd.below(8))]
            y = (Int128(1) << Int128(b)) - Int128(rnd.below(2))
            if rnd.below(2) == 0:
                y = -y
        if c.has_min and y < c.min_value:
            y = c.min_value
        if c.has_max and y > c.max_value:
            y = c.max_value
        out = ChoiceValue(integer=y)
    elif c.kind == FLOAT:
        var k = rnd.below(13)
        var f: Float64
        if k == 0:
            f = 0.0
        elif k == 1:
            f = -0.0
        elif k == 2:
            f = 1.0
        elif k == 3:
            f = -1.0
        elif k == 4:
            f = pos_inf()
        elif k == 5:
            f = neg_inf()
        elif k == 6:
            f = float_nan()
        elif k == 7:
            f = Float64.MAX_FINITE
        elif k == 8:
            f = smallest_subnormal()
        elif k == 9:
            f = 2.2250738585072014e-308
        elif k == 10:
            f = c.fmin
        elif k == 11:
            f = c.fmax
        else:
            f = next_up(v.f)
        out = ChoiceValue(float=f)
    elif c.kind == BOOLEAN:
        out = ChoiceValue(boolean=v.i == 0)
    else:
        var seq = List[UInt32]()
        var k = rnd.below(4) if c.kind == BYTES else rnd.below(3)
        if k == 3 and len(v.seq) > 0:
            # one byte set to a boundary byte
            seq = v.seq.copy()
            seq[Int(rnd.below(UInt64(len(seq))))] = _boundary_byte(rnd.below(6))
        elif k == 1:
            # repeat it
            for _ in range(2):
                for x in v.seq:
                    if len(seq) < c.max_size:
                        seq.append(x)
        elif k == 2 and len(v.seq) > 0:
            for i in range(len(v.seq) - 1):
                seq.append(v.seq[i])
        out = ChoiceValue(bytes=seq^) if c.kind == BYTES else ChoiceValue(
            string=seq^
        )
    if not choice_permitted(out, c):
        return choice_simplest(c)
    return out^


def _mutate[
    F: def(mut ConjectureData) raises
](mut runner: ConjectureRunner[F], corpus: _Corpus, parent: Result) -> List[
    ChoiceValue
]:
    """A variant of `parent`'s choices: a few values replaced (by random or
    boundary values), and maybe a span spliced in from another corpus
    entry, deleted, duplicated, or cut off (the rest is then drawn at
    random)."""
    ref p = parent[]
    var choices = p.choices()
    var free = List[Int]()
    for k in range(len(p.nodes)):
        if not p.nodes[k].was_forced:
            free.append(k)
    var structural = (
        len(free) == 0 or len(p.spans) > 0 and runner.random.below(2) == 0
    )
    var n_values = 0
    if len(free) > 0:
        n_values = Int(runner.random.below(4)) if structural else 1 + Int(
            runner.random.below(3)
        )
    # value changes keep every choice in place, so `p.spans` still apply
    for _ in range(n_values):
        var k = free[Int(runner.random.below(UInt64(len(free))))]
        ref c = p.nodes[k].constraints
        if runner.random.below(2) == 0:
            choices[k] = runner.tree_provider.draw(c)
        else:
            choices[k] = _boundary(runner.random, c, choices[k])
    if not structural or len(p.spans) == 0:
        return choices^
    ref s = p.spans[Int(runner.random.below(UInt64(len(p.spans))))]
    var op = runner.random.below(4)
    var out = List[ChoiceValue]()
    for k in range(s.start):
        out.append(choices[k].copy())
    if op == 0:
        # splice in a span with the same label from another entry
        ref other = corpus.entries[
            Int(runner.random.below(UInt64(len(corpus.entries))))
        ][]
        var matches = List[Int]()
        for i in range(len(other.spans)):
            if other.spans[i].label == s.label:
                matches.append(i)
        if len(matches) == 0:
            return choices^
        ref o = other.spans[
            matches[Int(runner.random.below(UInt64(len(matches))))]
        ]
        for k in range(o.start, o.end):
            out.append(other.nodes[k].value.copy())
    elif op == 1:
        pass  # delete the span
    elif op == 2:
        # duplicate it (e.g. a list element)
        for _ in range(2):
            for k in range(s.start, s.end):
                out.append(choices[k].copy())
    else:
        # cut off here: the rest is drawn at random
        return out^
    for k in range(s.end, len(choices)):
        out.append(choices[k].copy())
    return out^


def _keep_looking[
    F: def(mut ConjectureData) raises
](runner: ConjectureRunner[F]) -> Bool:
    """Whether to go on after a failure, looking for other bugs (as the
    generate phase does)."""
    if len(runner.interesting) == 0:
        return True
    if (
        not runner.settings.phases.shrink
        or not runner.settings.report_multiple_bugs
    ):
        return False
    return runner.call_count < min(
        runner.first_bug_found_at + 1000, runner.last_bug_found_at * 2
    )


struct FuzzReport(Copyable, Writable):
    """What a run of `FuzzTarget.fuzz` did, when it found no failure."""

    var inputs: Int
    """Test cases run."""
    var valid: Int
    """Test cases that ran to completion."""
    var corpus: Int
    """Test cases kept for covering something new."""
    var features: Int
    """Distinct features covered (see `fuzz`)."""
    var seconds: Float64

    def __init__(out self):
        self.inputs = 0
        self.valid = 0
        self.corpus = 0
        self.features = 0
        self.seconds = 0

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            self.inputs,
            " inputs (",
            self.valid,
            " valid) in ",
            Float64(Int(self.seconds * 10)) / 10,
            "s; corpus of ",
            self.corpus,
            " covering ",
            self.features,
            " features",
        )


def _fuzz_loop[
    F: def(mut ConjectureData) raises
](
    mut runner: ConjectureRunner[F], seconds: Float64, max_inputs: Int
) raises -> FuzzReport:
    var start = perf_counter_ns()
    var stop_at = start + Int(seconds * 1e9)
    var next_progress = start + 5_000_000_000
    var calls0 = runner.call_count
    var valid0 = runner.valid_count
    var corpus = _Corpus()
    var key = runner.db_key + ".fuzz"
    var use_db = Bool(runner.db) and runner.db_key.byte_length() > 0
    # failures saved by earlier runs (`given`'s, or fuzzing's)
    runner.reuse_existing_examples()
    if len(runner.interesting) > 0:
        # report them now, as `given` does
        return FuzzReport()
    # seeds: the simplest test case, then the corpus saved by earlier runs
    _ = corpus.add(
        runner.cached_test_function(List[ChoiceValue](), extend_simplest=True)
    )
    if use_db:
        for choices in runner.db.value().fetch(key):
            if not corpus.add(runner.cached_test_function(choices)):
                runner.db.value().delete(key, choices)
    var verbose = runner.settings.verbosity >= Verbosity.verbose
    while _keep_looking(runner):
        if runner.call_count - calls0 >= max_inputs:
            break
        var now = perf_counter_ns()
        if now >= stop_at:
            break
        if verbose and now >= next_progress:
            next_progress = now + 5_000_000_000
            print(
                String(
                    "proptest: fuzzing: ",
                    runner.call_count - calls0,
                    " inputs, corpus of ",
                    len(corpus.entries),
                    ", ",
                    len(corpus.seen),
                    " features",
                )
            )
        runner.check_flaky()
        if runner.tree.is_exhausted():
            break
        if len(runner.tree.nodes) > _MAX_TREE_NODES:
            runner.tree = DataTree()
        var result: Result
        if len(corpus.entries) == 0 or runner.random.below(10) == 0:
            var prefix = runner.tree.generate_novel_prefix(runner.tree_provider)
            var data = runner.new_data(prefix^)
            result = runner.test_function(data)
        else:
            var parent = corpus.entries[
                Int(runner.random.below(UInt64(len(corpus.entries))))
            ]
            var attempt = _mutate(runner, corpus, parent)
            result = runner.cached_test_function(attempt, extend=-1)
        if corpus.add(result) and use_db:
            runner.db.value().save(key, result[].choices())
    var report = FuzzReport()
    report.inputs = runner.call_count - calls0
    report.valid = runner.valid_count - valid0
    report.corpus = len(corpus.entries)
    report.features = len(corpus.seen)
    report.seconds = Float64(perf_counter_ns() - start) / 1e9
    if verbose:
        print(String("proptest: fuzzed ", report))
    return report^


struct FuzzTarget[P: Movable & Deinitable](Movable):
    """A property to run once per input from a fuzzer; see `fuzz_target`.

    `P` is the type of the test and its strategies, which the target owns:
    it keeps alive whatever the test captures by reference.
    """

    var _parts: Pointer[Self.P, MutUntrackedOrigin]
    var _ptr: _ErasedPtr
    var _run: def(_ErasedPtr, List[UInt8]) thin raises -> Optional[List[UInt8]]
    var _loop: def(_ErasedPtr, Float64, Int, String) thin raises -> FuzzReport
    var _free: def(_ErasedPtr) thin
    var _name: String

    def __init__[
        F: def(mut ConjectureData) raises
    ](
        out self,
        parts: Pointer[Self.P, MutUntrackedOrigin],
        var test_fn: F,
        settings: Settings,
        name: String,
    ):
        """Take ownership of `parts` (a heap allocation), and run
        `test_fn`, which reads them through its pointer."""
        comptime R = ConjectureRunner[F]

        def run_(
            p: _ErasedPtr, buffer: List[UInt8]
        ) raises -> Optional[List[UInt8]]:
            return _fuzz_one(p.unsafe_bitcast[R]()[], buffer)

        def loop_(
            p: _ErasedPtr, seconds: Float64, max_inputs: Int, name: String
        ) raises -> FuzzReport:
            ref runner = p.unsafe_bitcast[R]()[]
            var fr = _fuzz_loop(runner, seconds, max_inputs)
            if len(runner.interesting) > 0:
                var settings = runner.settings.copy()
                var report = RunReport()
                report.seed = runner.seed
                shrink_and_replay(runner, report, settings, name)
                _raise_failures(report, name, settings)
            return fr^

        def free_(p: _ErasedPtr):
            var q = p.unsafe_bitcast[R]()
            _ = q.unsafe_take_pointee()
            q.unsafe_free()

        var q = unsafe_alloc[R](1)
        q.unsafe_write(R(test_fn^, settings))
        self._parts = parts
        self._ptr = q.unsafe_bitcast[NoneType]()
        self._run = run_
        self._loop = loop_
        self._free = free_
        self._name = name

    def __deinit__(deinit self):
        self._free(self._ptr)
        _ = self._parts.unsafe_take_pointee()
        self._parts.unsafe_free()

    def fuzz_one_input(
        mut self, buffer: Span[UInt8, _]
    ) raises -> Optional[List[UInt8]]:
        """Run the test once, reading its inputs from `buffer` (at most
        `BUFFER_SIZE` bytes of it).

        Returns None if `buffer` doesn't make a valid test case (it ran
        out, or `assume` or a filter rejected it). Returns the canonical
        bytes for the test case if the test passed: the shortest input
        that replays it, which a fuzzer can keep in place of `buffer`.
        Raises the test's error if it failed, after saving the failing
        example to the database (if it's the simplest seen so far for that
        error).
        """
        return self._run(self._ptr, List[UInt8](buffer))

    def fuzz(
        mut self, seconds: Float64 = 60, *, max_inputs: Optional[Int] = None
    ) raises -> FuzzReport:
        """Fuzz the test for `seconds` (or `max_inputs` test cases, if
        that comes first), then shrink and report any failures as `given`
        does.

        Like a coverage-guided fuzzer, it keeps a corpus of the test cases
        that covered something new, and runs variants of them: some values
        replaced (at random, or by boundary values such as 0, -1, 2**31 or
        NaN), and spans of choices spliced from one test case into another,
        deleted, duplicated, or cut off. Proptest can't see the test's code
        coverage, so a test case's coverage is what its strategies did:
        each pair of strategies (one drawing from the other), with roughly
        how often, and each `event`. Improving a `target` score counts too.

        With a database, failures go to the test's `database_key` and the
        corpus to `<database_key>.fuzz`, so the next run starts where this
        one stopped. Raises the shrunk failures if it found any; returns
        what it did otherwise.
        """
        return self._loop(
            self._ptr, seconds, max_inputs.or_else(Int.MAX), self._name
        )


@always_inline
def fuzz_target_data[
    T: def(mut ConjectureData) raises
](
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[T]]:
    """A fuzz target for a test that draws its own data (as `given_data`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[T]](1)
    parts.unsafe_write(Tuple(test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        data.report_draws = True
        ref p = parts[]
        p[0](data)

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )


@always_inline
def fuzz_target[
    S1: Strategy, //, T: def(S1.Value) raises
](
    var s1: S1,
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[S1, T]]:
    """A fuzz target running `test(x)` for `x` from `s1` (as `given`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[S1, T]](1)
    parts.unsafe_write(Tuple(s1^, test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        ref p = parts[]
        var a = data.draw(p[0])
        var mark = len(data.notes)
        if data.is_final:
            _log_given(data, [format_value(a)])
        try:
            p[1](a)
        finally:
            if data.is_final:
                _note_given(data, [format_value(a)], at=mark)

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )


@always_inline
def fuzz_target[
    S1: Strategy, S2: Strategy, //, T: def(S1.Value, S2.Value) raises
](
    var s1: S1,
    var s2: S2,
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[S1, S2, T]]:
    """A fuzz target for `test` over two strategies (as `given`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[S1, S2, T]](1)
    parts.unsafe_write(Tuple(s1^, s2^, test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        ref p = parts[]
        var a = data.draw(p[0])
        var b = data.draw(p[1])
        var mark = len(data.notes)
        if data.is_final:
            _log_given(data, [format_value(a), format_value(b)])
        try:
            p[2](a, b)
        finally:
            if data.is_final:
                _note_given(data, [format_value(a), format_value(b)], at=mark)

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )


@always_inline
def fuzz_target[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value) raises,
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[S1, S2, S3, T]]:
    """A fuzz target for `test` over three strategies (as `given`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[S1, S2, S3, T]](1)
    parts.unsafe_write(Tuple(s1^, s2^, s3^, test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        ref p = parts[]
        var a = data.draw(p[0])
        var b = data.draw(p[1])
        var c = data.draw(p[2])
        var mark = len(data.notes)
        if data.is_final:
            _log_given(
                data, [format_value(a), format_value(b), format_value(c)]
            )
        try:
            p[3](a, b, c)
        finally:
            if data.is_final:
                _note_given(
                    data,
                    [format_value(a), format_value(b), format_value(c)],
                    at=mark,
                )

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )


@always_inline
def fuzz_target[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value, S4.Value) raises,
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var s4: S4,
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[S1, S2, S3, S4, T]]:
    """A fuzz target for `test` over four strategies (as `given`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[S1, S2, S3, S4, T]](1)
    parts.unsafe_write(Tuple(s1^, s2^, s3^, s4^, test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        ref p = parts[]
        var a = data.draw(p[0])
        var b = data.draw(p[1])
        var c = data.draw(p[2])
        var d = data.draw(p[3])
        var mark = len(data.notes)
        if data.is_final:
            _log_given(
                data,
                [
                    format_value(a),
                    format_value(b),
                    format_value(c),
                    format_value(d),
                ],
            )
        try:
            p[4](a, b, c, d)
        finally:
            if data.is_final:
                _note_given(
                    data,
                    [
                        format_value(a),
                        format_value(b),
                        format_value(c),
                        format_value(d),
                    ],
                    at=mark,
                )

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )


@always_inline
def fuzz_target[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value, S4.Value, S5.Value) raises,
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var s4: S4,
    var s5: S5,
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[S1, S2, S3, S4, S5, T]]:
    """A fuzz target for `test` over five strategies (as `given`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[S1, S2, S3, S4, S5, T]](1)
    parts.unsafe_write(Tuple(s1^, s2^, s3^, s4^, s5^, test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        ref p = parts[]
        var a = data.draw(p[0])
        var b = data.draw(p[1])
        var c = data.draw(p[2])
        var d = data.draw(p[3])
        var e = data.draw(p[4])
        var mark = len(data.notes)
        if data.is_final:
            _log_given(
                data,
                [
                    format_value(a),
                    format_value(b),
                    format_value(c),
                    format_value(d),
                    format_value(e),
                ],
            )
        try:
            p[5](a, b, c, d, e)
        finally:
            if data.is_final:
                _note_given(
                    data,
                    [
                        format_value(a),
                        format_value(b),
                        format_value(c),
                        format_value(d),
                        format_value(e),
                    ],
                    at=mark,
                )

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )


@always_inline
def fuzz_target[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value, S4.Value, S5.Value, S6.Value) raises,
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var s4: S4,
    var s5: S5,
    var s6: S6,
    var test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) -> FuzzTarget[Tuple[S1, S2, S3, S4, S5, S6, T]]:
    """A fuzz target for `test` over six strategies (as `given`)."""
    var loc = location.value() if location else call_location()

    var parts = unsafe_alloc[Tuple[S1, S2, S3, S4, S5, S6, T]](1)
    parts.unsafe_write(Tuple(s1^, s2^, s3^, s4^, s5^, s6^, test^))

    def run_one(mut data: ConjectureData) raises {var parts}:
        ref p = parts[]
        var a = data.draw(p[0])
        var b = data.draw(p[1])
        var c = data.draw(p[2])
        var d = data.draw(p[3])
        var e = data.draw(p[4])
        var f = data.draw(p[5])
        var mark = len(data.notes)
        if data.is_final:
            _log_given(
                data,
                [
                    format_value(a),
                    format_value(b),
                    format_value(c),
                    format_value(d),
                    format_value(e),
                    format_value(f),
                ],
            )
        try:
            p[6](a, b, c, d, e, f)
        finally:
            if data.is_final:
                _note_given(
                    data,
                    [
                        format_value(a),
                        format_value(b),
                        format_value(c),
                        format_value(d),
                        format_value(e),
                        format_value(f),
                    ],
                    at=mark,
                )

    return FuzzTarget(
        parts, run_one, _resolve_settings(settings, loc), String(loc)
    )
