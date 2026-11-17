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
`fuzz_all(t1, t2, ...)` shares a time budget among several targets, as
HypoFuzz does, favoring those still covering new features.
"""

from std.collections import Set
from std.hash import hash
from std.math import ceil, log
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
    STRING,
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
from proptest.internal.provider import Constants, _boundary_byte
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
    it occurred (bucketed), each event and `feature`, and how close each
    comparison made with a `Traced` value came to equality."""
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
    for f in r.features:
        out.append(_mix(0x66656174, f))
    # the closest each comparison site came to equality (libFuzzer's value
    # profile), so the corpus keeps each step toward a match
    var closest = Dict[UInt64, Int]()
    for c in r.comparisons:
        if c.closeness > closest.get(c.site, -1):
            closest[c.site] = c.closeness
    for item in closest.items():
        out.append(_mix(_mix(0x636D70, item.key), UInt64(item.value)))
    return out^


struct _Entry(Copyable):
    """A corpus entry, with its features and how many of them (and of the
    `target` labels) it is the entry to keep for."""

    var result: Result
    var features: List[UInt64]
    var owns: Int
    var valid: Bool

    def __init__(out self, result: Result, var features: List[UInt64]):
        self.valid = result[].status == Status.VALID
        self.result = result
        self.features = features^
        self.owns = 0


comptime _INVALID_WEIGHT = 0.25
"""An invalid entry's weight as a parent, relative to a valid entry with
the same features."""

comptime _REWEIGH_EVERY = 256
"""Parent weights are recomputed after this many picks (feature
frequencies change with every test case), or when the corpus changes."""


struct _Corpus(Movable):
    """The test cases worth mutating: for each feature, the simplest valid
    test case that covered it, and for each `target` label, the valid test
    case with the best score.

    As in Zest's validity fuzzing, an invalid test case (rejected by
    `assume` or a filter) that covers a feature no valid one has joins
    too, as a stepping stone: its features are often a step toward a
    valid test case that covers them. A valid test case covering the
    feature takes it over, and an invalid entry is mutated a quarter as
    often as a valid one with the same features.

    As in libFuzzer, a test case that covers only features already seen
    still joins the corpus if it is simpler than the entry kept for one
    of them, and an entry is dropped once it is kept for nothing. Parents
    are picked by the rarity of their features (libFuzzer's Entropic,
    simplified): an entry's weight is the sum over its features of
    1 / (the number of test cases that covered the feature), so entries
    that reach rarely covered features are mutated more often.
    """

    var entries: List[_Entry]
    var owner: Dict[UInt64, Int]
    """The entry kept for each feature (an index into `entries`)."""
    var freq: Dict[UInt64, Int]
    """How many valid test cases covered each feature."""
    var invalid_freq: Dict[UInt64, Int]
    """How many invalid test cases covered each feature."""
    var seen: Int
    """Features covered by any test case, valid or not."""
    var best: Dict[String, Float64]
    """The best score seen for each `target` label."""
    var best_owner: Dict[String, Int]
    var dropped: List[Result]
    """Entries dropped since the caller last cleared this (to delete from
    the database)."""
    var _cumulative: List[Float64]
    var _picks: Int

    def __init__(out self):
        self.entries = List[_Entry]()
        self.owner = Dict[UInt64, Int]()
        self.freq = Dict[UInt64, Int]()
        self.invalid_freq = Dict[UInt64, Int]()
        self.seen = 0
        self.best = Dict[String, Float64]()
        self.best_owner = Dict[String, Int]()
        self.dropped = List[Result]()
        self._cumulative = List[Float64]()
        self._picks = 0

    def add(mut self, r: Result) -> Bool:
        """Count `r`'s features, and keep `r` if it covers a new feature,
        is simpler than the entry kept for one, or improves a target
        score. An invalid `r` can only take features that no valid test
        case has covered."""
        var valid = r[].status == Status.VALID
        if not valid and r[].status != Status.INVALID:
            return False
        var features = List[UInt64]()
        var unique = Set[UInt64]()
        for f in _features(r[]):
            if f not in unique:
                unique.add(f)
                features.append(f)
        var claims = List[UInt64]()
        for f in features:
            var n = self.freq.get(f, 0)
            if n == 0 and f not in self.invalid_freq:
                self.seen += 1
            if valid:
                self.freq[f] = n + 1
            else:
                self.invalid_freq[f] = self.invalid_freq.get(f, 0) + 1
                if n > 0:
                    continue  # a valid entry keeps it
            var o = self.owner.get(f)
            if (
                not o
                or valid
                and not self.entries[o.value()].valid
                or sort_key_less(
                    r[].nodes, self.entries[o.value()].result[].nodes
                )
            ):
                claims.append(f)
        var labels = List[String]()
        for item in r[].target_observations.items():
            if not valid:
                break
            var best = self.best.get(item.key)
            if not best or item.value > best.value():
                self.best[item.key] = item.value
                labels.append(item.key)
        if len(claims) == 0 and len(labels) == 0:
            return False
        var idx = len(self.entries)
        self.entries.append(_Entry(r, features^))
        var losers = List[Int]()
        for f in claims:
            var o = self.owner.get(f)
            if o:
                self.entries[o.value()].owns -= 1
                losers.append(o.value())
            self.owner[f] = idx
            self.entries[idx].owns += 1
        for label in labels:
            var o = self.best_owner.get(label)
            if o:
                self.entries[o.value()].owns -= 1
                losers.append(o.value())
            self.best_owner[label] = idx
            self.entries[idx].owns += 1
        # drop the entries now kept for nothing, highest index first, so
        # that each removal moves only entries not yet looked at
        sort(losers)
        var i = len(losers) - 1
        while i >= 0:
            var k = losers[i]
            if (i == 0 or losers[i - 1] != k) and self.entries[k].owns == 0:
                self._remove(k)
            i -= 1
        self._cumulative.clear()
        return True

    def _remove(mut self, k: Int):
        """Drop entry `k`, moving the last entry into its place."""
        self.dropped.append(self.entries[k].result)
        var last = len(self.entries) - 1
        if k != last:
            self.entries[k] = self.entries[last].copy()
            for f in self.entries[k].features:
                if self.owner.get(f, -1) == last:
                    self.owner[f] = k
            var moved = List[String]()
            for item in self.best_owner.items():
                if item.value == last:
                    moved.append(item.key)
            for label in moved:
                self.best_owner[label] = k
        _ = self.entries.pop()

    def pick(mut self, mut rnd: Random) -> Int:
        """The index of a parent to mutate, by the rarity of its
        features."""
        self._picks += 1
        if (
            len(self._cumulative) != len(self.entries)
            or self._picks >= _REWEIGH_EVERY
        ):
            self._reweigh()
        var total = self._cumulative[len(self._cumulative) - 1]
        var x = rnd.random() * total
        var lo = 0
        var hi = len(self._cumulative) - 1
        while lo < hi:
            var mid = (lo + hi) // 2
            if self._cumulative[mid] > x:
                hi = mid
            else:
                lo = mid + 1
        return lo

    def _reweigh(mut self):
        self._picks = 0
        self._cumulative.clear()
        var weights = List[Float64](capacity=len(self.entries))
        var sum = 0.0
        for e in self.entries:
            var w = 0.0
            if e.valid:
                for f in e.features:
                    w += 1.0 / Float64(self.freq.get(f, 1))
            else:
                for f in e.features:
                    w += 1.0 / Float64(
                        max(
                            self.freq.get(f, 0) + self.invalid_freq.get(f, 0), 1
                        )
                    )
                w *= _INVALID_WEIGHT
            weights.append(w)
            sum += w
        # an entry kept for a target score gets an average entry's weight
        # per label, so hill climbing goes on as coverage grows
        var mean = sum / Float64(max(len(self.entries), 1))
        if mean <= 0:
            mean = 1.0
        for item in self.best_owner.items():
            weights[item.value] += mean
        var acc = 0.0
        for w in weights:
            acc += max(w, mean * 1e-3)
            self._cumulative.append(acc)


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


def _input_to_state(
    mut rnd: Random, p: ConjectureResult
) -> Optional[List[ChoiceValue]]:
    """Redqueen's input-to-state replacement: pick a comparison the test
    made with a `Traced` value, and set a choice equal to that value to
    what it was compared with (one either side of it, for integers, to
    get past `<` and `>`; for strings, maybe prefixed or suffixed to the
    current value instead, for `startswith`, `endswith` and `in`). None if
    no choice holds the value (it was computed from the choices, not drawn
    as is)."""
    ref c = p.comparisons[Int(rnd.below(UInt64(len(p.comparisons))))]
    var matches = List[Int]()
    for k in range(len(p.nodes)):
        ref n = p.nodes[k]
        if not n.was_forced and n.value == c.lhs:
            matches.append(k)
    if len(matches) == 0:
        return None
    var k = matches[Int(rnd.below(UInt64(len(matches))))]
    ref node = p.nodes[k]
    var v: ChoiceValue
    if c.rhs.kind == INTEGER:
        var d = Int128(Int(rnd.below(3))) - 1 if rnd.below(2) == 0 else Int128(
            0
        )
        v = ChoiceValue(integer=c.rhs.i + d)
    else:
        var seq = List[UInt32]()
        var how = rnd.below(4)
        if how == 2:
            seq = c.rhs.seq.copy()
            seq.extend(node.value.seq.copy())
        else:
            if how == 3:
                seq = node.value.seq.copy()
            seq.extend(c.rhs.seq.copy())
        v = ChoiceValue(string=seq^)
    if not choice_permitted(v, node.constraints):
        return None
    var choices = p.choices()
    choices[k] = v^
    return choices^


def _dictionary_mutation(
    mut rnd: Random, p: ConjectureResult, k: Constants
) -> Optional[List[ChoiceValue]]:
    """Use tokens from the user's dictionary (`Settings.dictionary`), one
    to three times (stacked, as AFL's havoc stage does, so a few tokens can
    appear together): a string or byte string gets a token inserted,
    written over part of it, or in place of it; an integer is set to a
    token that is a number. None if no choice can take one."""
    var free = List[Int]()
    for i in range(len(p.nodes)):
        ref n = p.nodes[i]
        if n.was_forced:
            continue
        var kind = n.constraints.kind
        if (
            kind == INTEGER
            and len(k.dict_ints) > 0
            or kind == STRING
            and len(k.dict_texts) > 0
            or kind == BYTES
        ):
            free.append(i)
    if len(free) == 0:
        return None
    var choices = p.choices()
    var changed = False
    for _ in range(1 + Int(rnd.below(3))):
        var i = free[Int(rnd.below(UInt64(len(free))))]
        ref c = p.nodes[i].constraints
        var v: ChoiceValue
        if c.kind == INTEGER:
            var d = k.dictionary_value(rnd, c)
            if not d:
                continue
            v = d.take()
        else:
            ref pool = k.dict_texts if c.kind == STRING else k.dict_bytes
            ref tok = pool[Int(rnd.below(UInt64(len(pool))))]
            ref cur = choices[i].seq
            var seq = List[UInt32]()
            var how = rnd.below(3)
            if how == 0:
                seq = tok.copy()
            else:
                # half the time at the end, which builds token sequences
                var at = len(cur) if rnd.below(2) == 0 else Int(
                    rnd.below(UInt64(len(cur) + 1))
                )
                for j in range(at):
                    seq.append(cur[j])
                seq.extend(tok.copy())
                var rest = at if how == 1 else at + len(tok)
                for j in range(rest, len(cur)):
                    seq.append(cur[j])
            v = ChoiceValue(bytes=seq^) if c.kind == BYTES else ChoiceValue(
                string=seq^
            )
        if choice_permitted(v, c):
            choices[i] = v^
            changed = True
    if not changed:
        return None
    return choices^


comptime _MEAN_MUTATIONS = 2.0
"""How many runs of choices a mutation changes, on average (geometric)."""
comptime _MEAN_RUN = 1.5
"""How many consecutive choices a run changes, on average (geometric)."""
comptime _MEAN_SEQ_RUN = 4.0
"""How many consecutive elements of a string or byte string a change
within it overwrites, on average (geometric)."""


def _geometric(mut rnd: Random, mean: Float64) -> Int:
    """A geometrically distributed count, at least 1, with mean `mean`
    (> 1), as Zest samples its mutation counts and sizes."""
    var u = rnd.random()
    return max(1, Int(ceil(log(1.0 - u) / log(1.0 - 1.0 / mean))))


def _seq_run[
    F: def(mut ConjectureData) raises
](
    mut runner: ConjectureRunner[F], c: Constraints, v: ChoiceValue, zero: Bool
) -> ChoiceValue:
    """`v`, a string or byte string, with a run of its elements overwritten:
    with zeros (byte strings, when `zero`) or with elements of a fresh
    draw, so that a string keeps to its alphabet."""
    if len(v.seq) == 0:
        return runner.tree_provider.draw(c)
    var seq = v.seq.copy()
    var fresh = runner.tree_provider.draw(c)
    var start = Int(runner.random.below(UInt64(len(seq))))
    var end = min(start + _geometric(runner.random, _MEAN_SEQ_RUN), len(seq))
    for i in range(start, end):
        if zero and c.kind == BYTES:
            seq[i] = 0
        elif len(fresh.seq) > 0:
            seq[i] = fresh.seq[Int(runner.random.below(UInt64(len(fresh.seq))))]
        elif c.kind == BYTES:
            seq[i] = UInt32(runner.random.below(256))
    var out = ChoiceValue(bytes=seq^) if c.kind == BYTES else ChoiceValue(
        string=seq^
    )
    if not choice_permitted(out, c):
        return v.copy()
    return out^


def _havoc[
    F: def(mut ConjectureData) raises
](
    mut runner: ConjectureRunner[F],
    p: ConjectureResult,
    free: List[Int],
    mut choices: List[ChoiceValue],
    runs: Int,
):
    """Zest's havoc: change `runs` runs of consecutive free choices, each
    of geometric length. Each choice is redrawn, set to a boundary value,
    or (strings and byte strings) has a run of its elements overwritten.
    One time in ten, every run is set to its simplest choices instead
    (Zest sets its bytes to zero)."""
    if len(free) == 0:
        return
    var zero = runner.random.below(10) == 0
    for _ in range(runs):
        var start = Int(runner.random.below(UInt64(len(free))))
        var end = min(start + _geometric(runner.random, _MEAN_RUN), len(free))
        for j in range(start, end):
            var k = free[j]
            ref c = p.nodes[k].constraints
            var seq = c.kind == BYTES or c.kind == STRING
            if zero:
                choices[k] = _seq_run(
                    runner, c, choices[k], True
                ) if seq and c.kind == BYTES else choice_simplest(c)
                continue
            var op = runner.random.below(UInt64(3) if seq else UInt64(2))
            if op == 0:
                choices[k] = runner.tree_provider.draw(c)
            elif op == 1:
                choices[k] = _boundary(runner.random, c, choices[k])
            else:
                choices[k] = _seq_run(runner, c, choices[k], False)


def _mutate[
    F: def(mut ConjectureData) raises
](mut runner: ConjectureRunner[F], corpus: _Corpus, parent: Result) -> List[
    ChoiceValue
]:
    """A variant of `parent`'s choices: runs of values replaced (Zest's
    havoc, see `_havoc`), and maybe a span spliced in from another corpus
    entry, deleted, duplicated, or cut off (the rest is then drawn at
    random)."""
    ref p = parent[]
    if len(runner.constants[].dict_bytes) > 0 and runner.random.below(4) == 0:
        var used = _dictionary_mutation(runner.random, p, runner.constants[])
        if used:
            return used.take()
    if len(p.comparisons) > 0 and runner.random.below(3) == 0:
        var replaced = _input_to_state(runner.random, p)
        if replaced:
            return replaced.take()
    var choices = p.choices()
    var free = List[Int]()
    for k in range(len(p.nodes)):
        if not p.nodes[k].was_forced:
            free.append(k)
    var structural = (
        len(free) == 0 or len(p.spans) > 0 and runner.random.below(2) == 0
    )
    # value changes keep every choice in place, so `p.spans` still apply
    var runs = _geometric(runner.random, _MEAN_MUTATIONS)
    _havoc(runner, p, free, choices, runs - 1 if structural else runs)
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
        ].result[]
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


struct _Fuzzer[F: def(mut ConjectureData) raises](Movable):
    """A fuzz target's runner and its corpus, kept between calls so that
    fuzzing resumes where it stopped (`fuzz` again, or `fuzz_all`'s
    slices)."""

    var runner: ConjectureRunner[Self.F]
    var corpus: _Corpus
    var started: Bool
    var done: Bool
    """Nothing more to do: the test failed (and doesn't look for other
    bugs) or every test case has been tried."""
    var ns: Int
    """Time spent fuzzing."""
    var next_progress: Int
    var last_new: Int
    """`runner.call_count` when the corpus last covered a new feature."""

    def __init__(out self, var test_fn: Self.F, settings: Settings):
        self.runner = ConjectureRunner[Self.F](test_fn^, settings)
        self.corpus = _Corpus()
        self.started = False
        self.done = False
        self.ns = 0
        self.next_progress = 0
        self.last_new = 0

    def _db_key(self) -> String:
        return self.runner.db_key + ".fuzz"

    def _use_db(self) -> Bool:
        return Bool(self.runner.db) and self.runner.db_key.byte_length() > 0

    def start(mut self) raises:
        """Replay saved failures, then seed the corpus: the simplest test
        case, then the corpus saved by earlier runs."""
        self.started = True
        self.next_progress = perf_counter_ns() + 5_000_000_000
        ref runner = self.runner
        runner.reuse_existing_examples()
        if len(runner.interesting) > 0:
            # report them now, as `given` does
            self.done = True
            return
        _ = self.corpus.add(
            runner.cached_test_function(
                List[ChoiceValue](), extend_simplest=True
            )
        )
        if self._use_db():
            var key = self._db_key()
            for choices in runner.db.value().fetch(key):
                if not self.corpus.add(runner.cached_test_function(choices)):
                    runner.db.value().delete(key, choices)
                for r in self.corpus.dropped:
                    runner.db.value().delete(key, r[].choices())
                self.corpus.dropped.clear()

    def run(mut self, stop_at: Int, max_inputs: Int, guided: Bool) raises:
        """Fuzz until `stop_at` (`perf_counter_ns`), or for `max_inputs`
        test cases, or until there's nothing more to do. Unless `guided`,
        every test case is generated afresh (the corpus only counts
        features)."""
        var t0 = perf_counter_ns()
        var calls0 = self.runner.call_count
        if not self.started:
            self.start()
        ref runner = self.runner
        var key = self._db_key()
        var use_db = self._use_db()
        var verbose = runner.settings.verbosity >= Verbosity.verbose
        while not self.done:
            if not _keep_looking(runner) or runner.tree.is_exhausted():
                self.done = True
                break
            if runner.call_count - calls0 >= max_inputs:
                break
            var now = perf_counter_ns()
            if now >= stop_at:
                break
            if verbose and now >= self.next_progress:
                self.next_progress = now + 5_000_000_000
                print(
                    String(
                        "proptest: fuzzing: ",
                        runner.call_count,
                        " inputs, corpus of ",
                        len(self.corpus.entries),
                        ", ",
                        len(self.corpus.freq),
                        " features",
                    )
                )
            runner.check_flaky()
            if len(runner.tree.nodes) > _MAX_TREE_NODES:
                runner.tree = DataTree()
            var result: Result
            if (
                not guided
                or len(self.corpus.entries) == 0
                or runner.random.below(10) == 0
            ):
                var prefix = runner.tree.generate_novel_prefix(
                    runner.tree_provider
                )
                var data = runner.new_data(prefix^)
                result = runner.test_function(data)
            else:
                var parent = self.corpus.entries[
                    self.corpus.pick(runner.random)
                ].result
                var attempt = _mutate(runner, self.corpus, parent)
                result = runner.cached_test_function(attempt, extend=-1)
            var known = self.corpus.seen
            if self.corpus.add(result) and use_db:
                runner.db.value().save(key, result[].choices())
                for r in self.corpus.dropped:
                    runner.db.value().delete(key, r[].choices())
            self.corpus.dropped.clear()
            if self.corpus.seen > known:
                self.last_new = runner.call_count
        self.ns += perf_counter_ns() - t0

    def report(self) -> FuzzReport:
        """Totals so far."""
        var r = FuzzReport()
        r.inputs = self.runner.call_count
        r.valid = self.runner.valid_count
        r.corpus = len(self.corpus.entries)
        r.features = len(self.corpus.freq)
        r.seconds = Float64(self.ns) / 1e9
        return r^

    def since_new(self) -> Int:
        """Test cases run since the corpus last covered a new feature."""
        return self.runner.call_count - self.last_new

    def raise_failures(mut self, name: String) raises:
        """Shrink and raise the failures found, if any, as `given` does."""
        if len(self.runner.interesting) == 0:
            return
        var settings = self.runner.settings.copy()
        var report = RunReport()
        report.seed = self.runner.seed
        shrink_and_replay(self.runner, report, settings, name)
        _raise_failures(report, name, settings)


trait _Fuzzable:
    """A `FuzzTarget`, whatever its type: what `fuzz_all` needs of it."""

    def _handle(self) -> _Handle:
        ...


struct _Handle(Copyable):
    """A fuzz target's type-erased state and operations, for `fuzz_all`
    (valid while the target is)."""

    var ptr: _ErasedPtr
    var step: def(_ErasedPtr, Int, Int, Bool) thin raises
    var report: def(_ErasedPtr) thin -> FuzzReport
    var since_new: def(_ErasedPtr) thin -> Int
    var done: def(_ErasedPtr) thin -> Bool
    var raise_: def(_ErasedPtr, String) thin raises
    var quiet: Bool
    var name: String

    def __init__(
        out self,
        ptr: _ErasedPtr,
        step: def(_ErasedPtr, Int, Int, Bool) thin raises,
        report: def(_ErasedPtr) thin -> FuzzReport,
        since_new: def(_ErasedPtr) thin -> Int,
        done: def(_ErasedPtr) thin -> Bool,
        raise_: def(_ErasedPtr, String) thin raises,
        quiet: Bool,
        name: String,
    ):
        self.ptr = ptr
        self.step = step
        self.report = report
        self.since_new = since_new
        self.done = done
        self.raise_ = raise_
        self.quiet = quiet
        self.name = name


struct FuzzTarget[P: Movable & Deinitable](Movable, _Fuzzable):
    """A property to run once per input from a fuzzer, or to fuzz; see
    `fuzz_target`.

    `P` is the type of the test and its strategies, which the target owns:
    it keeps alive whatever the test captures by reference. The target
    keeps its corpus between calls to `fuzz`.
    """

    var _parts: Pointer[Self.P, MutUntrackedOrigin]
    var _ptr: _ErasedPtr
    var _run: def(_ErasedPtr, List[UInt8]) thin raises -> Optional[List[UInt8]]
    var _step: def(_ErasedPtr, Int, Int, Bool) thin raises
    var _report: def(_ErasedPtr) thin -> FuzzReport
    var _since_new: def(_ErasedPtr) thin -> Int
    var _done: def(_ErasedPtr) thin -> Bool
    """Whether the target has failed or has nothing more to try."""
    var _raise: def(_ErasedPtr, String) thin raises
    var _verbose: Bool
    var _quiet: Bool
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
        comptime R = _Fuzzer[F]

        def run_(
            p: _ErasedPtr, buffer: List[UInt8]
        ) raises -> Optional[List[UInt8]]:
            return _fuzz_one(p.unsafe_bitcast[R]()[].runner, buffer)

        def step_(
            p: _ErasedPtr, stop_at: Int, max_inputs: Int, guided: Bool
        ) raises:
            p.unsafe_bitcast[R]()[].run(stop_at, max_inputs, guided)

        def report_(p: _ErasedPtr) -> FuzzReport:
            return p.unsafe_bitcast[R]()[].report()

        def since_new_(p: _ErasedPtr) -> Int:
            return p.unsafe_bitcast[R]()[].since_new()

        def done_(p: _ErasedPtr) -> Bool:
            ref f = p.unsafe_bitcast[R]()[]
            return f.done or len(f.runner.interesting) > 0

        def raise_(p: _ErasedPtr, name: String) raises:
            p.unsafe_bitcast[R]()[].raise_failures(name)

        def free_(p: _ErasedPtr):
            var q = p.unsafe_bitcast[R]()
            _ = q.unsafe_take_pointee()
            q.unsafe_free()

        var q = unsafe_alloc[R](1)
        q.unsafe_write(R(test_fn^, settings))
        self._parts = parts
        self._ptr = q.unsafe_bitcast[NoneType]()
        self._run = run_
        self._step = step_
        self._report = report_
        self._since_new = since_new_
        self._done = done_
        self._raise = raise_
        self._verbose = settings.verbosity >= Verbosity.verbose
        self._quiet = settings.verbosity == Verbosity.quiet
        self._free = free_
        self._name = name

    def __deinit__(deinit self):
        self._free(self._ptr)
        _ = self._parts.unsafe_take_pointee()
        self._parts.unsafe_free()

    def totals(self) -> FuzzReport:
        """What fuzzing this target has done so far, over every `fuzz` and
        `fuzz_all` call."""
        return self._report(self._ptr)

    def _handle(self) -> _Handle:
        return _Handle(
            self._ptr,
            self._step,
            self._report,
            self._since_new,
            self._done,
            self._raise,
            self._quiet,
            self._name,
        )

    def name(self) -> String:
        """The target's name: its call site, or `Settings.database_key`."""
        return self._name

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
        mut self,
        seconds: Float64 = 60,
        *,
        max_inputs: Optional[Int] = None,
        guided: Bool = True,
    ) raises -> FuzzReport:
        """Fuzz the test for `seconds` (or `max_inputs` test cases, if
        that comes first), then shrink and report any failures as `given`
        does.

        Like a coverage-guided fuzzer, it keeps a corpus of the test cases
        that covered something new, and runs variants of them: runs of
        values replaced (at random, by boundary values such as 0, -1, 2**31
        or NaN, or by their simplest values), runs of bytes or characters
        overwritten within a string, and spans of choices spliced from one
        test case into another, deleted, duplicated, or cut off. Proptest can't see the test's code
        coverage, so a test case's coverage is what its strategies did:
        each pair of strategies (one drawing from the other), with roughly
        how often, and each `event`. Improving a `target` score counts too.

        The corpus keeps, for each feature, the simplest test case that
        covered it (and for each `target` label, the best scorer), and
        picks entries to mutate by the rarity of their features, so the
        test cases that reach rarely covered code get most of the work.
        A test case rejected by `assume` or a filter is kept too if it
        covered a feature no valid test case has (Zest's validity
        fuzzing).

        With `guided=False`, every test case is generated afresh and the
        corpus only counts features: a baseline for how much the guidance
        helps.

        Values drawn with `traced(...)` record what they're compared
        with: the loop tries setting a choice to the value its traced
        value was compared with, and counts getting closer than before at
        a comparison as a new feature. With `Settings.dictionary`, it
        inserts the dictionary's tokens into strings and byte strings, and
        sets integers to the tokens that are numbers.

        The corpus stays with the target, so calling `fuzz` again goes on
        where it stopped. With a database, failures go to the test's
        `database_key` and the corpus to `<database_key>.fuzz`, so the
        next run starts where this one stopped too. Raises the shrunk failures if it found any; returns
        what it did otherwise.
        """
        var before = self._report(self._ptr)
        var stop_at = perf_counter_ns() + Int(seconds * 1e9)
        self._step(self._ptr, stop_at, max_inputs.or_else(Int.MAX), guided)
        self._raise(self._ptr, self._name)
        var r = self._report(self._ptr)
        r.inputs -= before.inputs
        r.valid -= before.valid
        r.seconds -= before.seconds
        if self._verbose:
            print(String("proptest: fuzzed ", r))
        return r^


comptime _SLICE_NS = 100_000_000
"""How long `fuzz_all` runs a target before choosing again."""
comptime _SLICE_INPUTS = 250
"""... or how many test cases, whichever comes first."""
comptime _FIRST_SLICE_INPUTS = 50
"""A target's first slice, enough to estimate its rate."""
comptime _EXPLORE = 10
"""One choice in this many is a target at random."""


def _discovery_rate(r: FuzzReport, since_new: Int) -> Float64:
    """New features a target is expected to find per second: the chance
    that its next test case covers something new, estimated as one over
    the number of test cases since it last did, divided by its time per
    test case."""
    var p_new = 1.0 / Float64(since_new + 1)
    var per_input = r.seconds / Float64(max(r.inputs, 1))
    return p_new / max(per_input, 1e-7)


def fuzz_all[
    *Ts: _Fuzzable
](
    mut *targets: *Ts,
    seconds: Float64 = 60,
    max_inputs: Optional[Int] = None,
    verbose: Bool = False,
) raises -> List[FuzzReport]:
    """Fuzz several targets for `seconds` between them (or `max_inputs`
    test cases in all), giving the time to those finding new behavior
    fastest, as HypoFuzz does.

    Time goes out in slices of 0.1 s (or 250 test cases; 50 for a
    target's first). After each target has had one, each slice goes to the target with the highest
    expected rate of new features: the chance that its next test case
    covers a new one, estimated as one over the number of test cases
    since it last did (HypoFuzz's "since new coverage"), divided by its
    time per test case. One slice in ten goes to a target
    at random, so none is starved by a bad estimate. A target that fails,
    or has run every test case it can, gets no more slices (so, unlike
    `fuzz`, it doesn't go on looking for other bugs).

    Each target keeps its corpus (and saves it to the database) as with
    `fuzz`. A failure is shrunk when found, with a line saying so (unless
    the target's verbosity is quiet), and the failures are raised
    together at the end, once the others have had their time. Returns what each
    target did, in order; with `verbose`, prints each target's totals at
    the end.
    """
    var hs = List[_Handle]()
    comptime for i in range(targets.__len__()):
        hs.append(targets[i]._handle())
    var n = len(hs)
    if n == 0:
        return List[FuzzReport]()
    var stop_at = perf_counter_ns() + Int(seconds * 1e9)
    var budget = max_inputs.or_else(Int.MAX)
    var rnd = Random(UInt64(perf_counter_ns()))
    var before = List[FuzzReport]()
    var stopped = List[Bool]()
    var tried = List[Bool]()
    for i in range(n):
        before.append(hs[i].report(hs[i].ptr))
        stopped.append(False)
        tried.append(False)
    var failures = List[String]()
    var used = 0
    while used < budget and perf_counter_ns() < stop_at:
        var live = List[Int]()
        for i in range(n):
            if not stopped[i]:
                live.append(i)
        if len(live) == 0:
            break
        var pick = -1
        for i in live:
            if not tried[i]:
                pick = i
                break
        if pick < 0:
            if rnd.below(_EXPLORE) == 0:
                pick = live[Int(rnd.below(UInt64(len(live))))]
            else:
                var best = -1.0
                for i in live:
                    ref h = hs[i]
                    var rate = _discovery_rate(
                        h.report(h.ptr), h.since_new(h.ptr)
                    )
                    if rate > best:
                        best = rate
                        pick = i
        var slice = _SLICE_INPUTS if tried[pick] else _FIRST_SLICE_INPUTS
        tried[pick] = True
        ref h = hs[pick]
        var calls0 = h.report(h.ptr).inputs
        h.step(
            h.ptr,
            min(stop_at, perf_counter_ns() + _SLICE_NS),
            min(slice, budget - used),
            True,
        )
        used += h.report(h.ptr).inputs - calls0
        if h.done(h.ptr):
            stopped[pick] = True
            try:
                h.raise_(h.ptr, h.name)
            except e:
                var msg = String(e)
                failures.append(msg)
                if not h.quiet:
                    print(
                        String(
                            "proptest: fuzz_all: ",
                            h.name,
                            " failed (reported at the end)",
                        )
                    )
    var out = List[FuzzReport]()
    for i in range(n):
        ref h = hs[i]
        var r = h.report(h.ptr)
        r.inputs -= before[i].inputs
        r.valid -= before[i].valid
        r.seconds -= before[i].seconds
        if verbose:
            print(String("proptest: ", h.name, ": ", r))
        out.append(r^)
    if len(failures) > 0:
        var msg = String()
        for i in range(len(failures)):
            if i > 0:
                msg += "\n\n"
            msg += failures[i]
        raise Error(msg)
    return out^


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
