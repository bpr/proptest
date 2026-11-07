# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The test case shrinker.

Port of `hypothesis.internal.conjecture.shrinker`. Given a failing test case
it repeatedly tries simpler choice sequences, keeping any that still fail
in the same way, until none of its passes can make progress.

"Simpler" is `sort_key`: fewer choices, then smaller choice indices from
left to right. Every candidate is checked against the current target
before running it, so shrinking always terminates.

The passes, in order (as in Hypothesis):

- `try_trivial_spans`: replace a whole span with its simplest choices;
- `node_program("X"*k)`: delete runs of k consecutive choices;
- `pass_to_descendant`: replace a span by a nested span with the same label
  (e.g. a tree by one of its subtrees);
- `reorder_spans`: sort sibling spans with the same label;
- `minimize_duplicated_choices`: shrink equal choices together;
- `minimize_individual_choices`: shrink each choice with the value shrinkers;
- `redistribute_numeric_pairs`: move value from one number to a later one;
- `lower_integers_together`: lower two nearby integers by the same amount;
- `lower_duplicated_characters`: lower a character shared by two strings.

plus `reduce_each_alternative` (re-target `one_of` branches towards earlier
ones) once at the start, and `remove_discarded` between passes.

Hypothesis's step-at-a-time `ChoiceTree` scheduling is replaced by full
sweeps of each pass, and `normalize_unicode_chars` and
`widen_to_span_with_recorded_value` are not ported.
"""

from std.collections import Set, Dict
from std.time import perf_counter_ns
from std.math import isnan, isinf

from proptest.internal.choice import (
    ChoiceValue,
    ChoiceNode,
    Constraints,
    INTEGER,
    FLOAT,
    BOOLEAN,
    BYTES,
    STRING,
    sort_key_less,
    choice_permitted,
    choice_simplest,
    element_order,
    element_from_order,
)
from proptest.internal.data import (
    ConjectureData,
    ConjectureResult,
    Result,
    Status,
    Span,
)
from proptest.internal.engine import ConjectureRunner, MAX_SHRINKING_SECONDS
from proptest.internal.floats import MAX_PRECISE_INTEGER
from proptest.internal.pareto import dominance, LEFT_DOMINATES
from proptest.internal.shrinking import (
    find_integer,
    shrink_integer,
    shrink_float,
    shrink_ordering,
    shrink_collection,
)
from proptest.settings import Verbosity
from proptest.internal.intervals import IntervalSet
from proptest.internal.decomposition import Decompositions

comptime STOP_SHRINKING = "proptest.StopShrinking"
comptime N_PASSES = 14
"""The number of shrink passes: try_trivial_spans, node_program X*5..X*1, pass_to_descendant,
reorder_spans, minimize_duplicated_choices, minimize_individual_choices,
redistribute_numeric_pairs, lower_integers_together,
lower_duplicated_characters, normalize_unicode_chars."""


def _nodes_equal(a: List[ChoiceNode], b: List[ChoiceNode]) -> Bool:
    if len(a) != len(b):
        return False
    for i in range(len(a)):
        if not (a[i].value == b[i].value):
            return False
    return True


def _values(nodes: List[ChoiceNode]) -> List[ChoiceValue]:
    var out = List[ChoiceValue](capacity=len(nodes))
    for n in nodes:
        out.append(n.value.copy())
    return out^


def _slice(nodes: List[ChoiceNode], start: Int, end: Int) -> List[ChoiceNode]:
    var out = List[ChoiceNode](capacity=max(0, end - start))
    for i in range(max(0, start), min(end, len(nodes))):
        out.append(nodes[i].copy())
    return out^


def _concat(
    a: List[ChoiceNode], b: List[ChoiceNode], c: List[ChoiceNode]
) -> List[ChoiceNode]:
    var out = List[ChoiceNode](capacity=len(a) + len(b) + len(c))
    for x in a:
        out.append(x.copy())
    for x in b:
        out.append(x.copy())
    for x in c:
        out.append(x.copy())
    return out^


def _abs_diff(a: Int128, b: Int128) -> UInt128:
    return UInt128(a - b) if a >= b else UInt128(b - a)


def _simpler_case_chars(
    c: UInt32,
    alphabet: IntervalSet,
    decompositions: Optional[Decompositions] = None,
) -> List[UInt32]:
    """Single characters from the natural simplifications of `c` -- its
    upper- and lowercase forms, and (given `decompositions`) the characters
    of its NFD/NFKD decompositions and casefold -- that are in `alphabet`
    and earlier than `c` in shrink order, simplest first. Port of
    Hypothesis's `_natural_simpler_chars`."""
    var out = List[UInt32]()
    var cp = Codepoint.from_u32(c)
    if not cp or c not in alphabet:
        return out^
    var s = String(cp.value())
    var c_index = alphabet.index_from_char_in_shrink_order(c)
    var candidates = List[UInt32]()
    for form in [s.upper(), s.lower()]:
        for x in form.codepoints():
            candidates.append(x.to_u32())
    if decompositions:
        for x in decompositions.value().components(c):
            candidates.append(x)
    var keys = List[Int]()
    for u in candidates:
        if u == c or u not in alphabet:
            continue
        var k = alphabet.index_from_char_in_shrink_order(u)
        if k >= c_index:
            continue
        var seen = False
        for y in out:
            if y == u:
                seen = True
        if not seen:
            out.append(u)
            keys.append(k)
    # sort by shrink-order index
    for a in range(1, len(out)):
        var b = a
        while b > 0 and keys[b - 1] > keys[b]:
            keys.swap_elements(b - 1, b)
            out.swap_elements(b - 1, b)
            b -= 1
    return out^


struct Shrinker[F: def(mut ConjectureData) raises](Movable):
    """Shrinks one failing example. Owns the runner while it works; take it
    back with `release()`."""

    var runner: ConjectureRunner[Self.F]
    var target: Result
    var origin: String
    var shrinks: Int
    var max_stall: Int
    var calls_at_last_shrink: Int
    var initial_calls: Int
    var changed_nodes: Set[Int]
    var last_checked_id: Int
    var last_checked_nodes: List[ChoiceNode]
    var start_ns: Int
    var max_shrinks: Int
    var stalled: Bool
    """Shrinking stopped early (stalled or hit a limit), so don't explain."""
    var arg_comments: Dict[Int, String]
    """Explain-phase comments, by argument number."""
    var explain_note: String
    var tried: List[Set[Int]]
    """Per pass, the positions tried on the current target."""
    var tried_target: Int
    var last_position: List[Int]
    var pass_calls: List[Int]
    var pass_shrinks: List[Int]
    var pass_deletions: List[Int]
    var dup_groups: List[List[Int]]
    var dup_groups_target: Int
    var call_limit: Int
    """Stop shrinking once the runner has made this many calls (-1: none)."""
    var decompositions: Optional[Decompositions]
    """Built on first use by `normalize_unicode_chars_at`."""
    var pareto: Bool
    """Pareto mode: keep any valid test case that dominates the target
    (used to shrink members of the Pareto front)."""

    def __init__(
        out self,
        var runner: ConjectureRunner[Self.F],
        target: Result,
        *,
        pareto: Bool = False,
    ):
        self.max_shrinks = runner.settings.max_shrinks
        self.initial_calls = runner.call_count
        self.calls_at_last_shrink = runner.call_count
        self.runner = runner^
        self.target = target
        self.origin = target[].interesting_origin
        self.shrinks = 0
        self.max_stall = 200
        self.changed_nodes = Set[Int]()
        self.last_checked_id = target[].id
        self.last_checked_nodes = target[].nodes.copy()
        self.start_ns = perf_counter_ns()
        self.stalled = False
        self.arg_comments = Dict[Int, String]()
        self.explain_note = String()
        self.tried = List[Set[Int]]()
        for _ in range(N_PASSES):
            self.tried.append(Set[Int]())
        self.tried_target = -1
        self.last_position = List[Int](length=N_PASSES, fill=0)
        self.pass_calls = List[Int](length=N_PASSES, fill=0)
        self.pass_shrinks = List[Int](length=N_PASSES, fill=0)
        self.pass_deletions = List[Int](length=N_PASSES, fill=0)
        self.dup_groups = List[List[Int]]()
        self.dup_groups_target = -1
        self.pareto = pareto
        self.decompositions = None
        self.call_limit = -1

    def release(deinit self) -> ConjectureRunner[Self.F]:
        return self.runner^

    # ===------------------------------------------------------------------=== #
    # Core
    # ===------------------------------------------------------------------=== #

    def nodes(self) -> List[ChoiceNode]:
        return self.target[].nodes.copy()

    def num_nodes(self) -> Int:
        return len(self.target[].nodes)

    def calls(self) -> Int:
        return self.runner.call_count

    def predicate(self, r: Result) -> Bool:
        if self.pareto:
            return r[].status >= Status.VALID
        return (
            r[].status == Status.INTERESTING
            and r[].interesting_origin == self.origin
        )

    def check_calls(self) raises:
        if self.calls() - self.calls_at_last_shrink >= self.max_stall:
            raise Error(STOP_SHRINKING)
        if self.shrinks >= self.max_shrinks:
            raise Error(STOP_SHRINKING)
        if self.call_limit >= 0 and self.calls() >= self.call_limit:
            raise Error(STOP_SHRINKING)
        if (perf_counter_ns() - self.start_ns) > Int(
            MAX_SHRINKING_SECONDS
        ) * 1_000_000_000:
            raise Error(STOP_SHRINKING)

    def update_target(mut self, r: Result):
        self.shrinks += 1
        self.max_stall = max(
            self.max_stall, (self.calls() - self.calls_at_last_shrink) * 2
        )
        self.calls_at_last_shrink = self.calls()
        self.target = r
        if self.runner.settings.verbosity >= Verbosity.debug:
            print(
                "  shrunk to",
                len(r[].nodes),
                "choices after",
                self.calls(),
                "calls",
            )

    def incorporate(mut self, r: Result):
        if r[].status < Status.VALID or r[].id == self.target[].id:
            return
        if self.predicate(r) and sort_key_less(r[].nodes, self.target[].nodes):
            if self.pareto:
                if dominance(r[], self.target[]) != LEFT_DOMINATES:
                    return
                # the old target is now dominated
                if self.runner.front:
                    self.runner.front.value().remove(self.target)
                    self.runner.sync_front()
            self.update_target(r)

    def run_nodes(
        mut self, var attempt: List[ChoiceNode]
    ) raises -> Tuple[Bool, Optional[Result]]:
        """Port of `cached_test_function`: try a candidate node sequence.
        Returns whether the target changed, and the result (None if the
        candidate was rejected without running it)."""
        var n = self.num_nodes()
        if len(attempt) > n:
            attempt.resize(n, attempt[0].copy())
        if _nodes_equal(attempt, self.target[].nodes):
            return (True, Optional[Result](None))
        for node in attempt:
            if not choice_permitted(node.value, node.constraints):
                return (False, Optional[Result](None))
        if sort_key_less(self.target[].nodes, attempt):
            return (False, Optional[Result](None))
        var r = self.runner.cached_test_function(_values(attempt))
        var prev = self.target[].id
        self.incorporate(r)
        self.check_calls()
        return (prev != self.target[].id, Optional[Result](r))

    def consider(mut self, var attempt: List[ChoiceNode]) raises -> Bool:
        """Whether `attempt` (run through the test) became the new target."""
        return self.run_nodes(attempt^)[0]

    def replace_node(self, i: Int, var value: ChoiceValue) -> List[ChoiceNode]:
        var nodes = self.nodes()
        if i < len(nodes):
            nodes[i] = nodes[i].with_value(value^)
        return nodes^

    # ===------------------------------------------------------------------=== #
    # Driver
    # ===------------------------------------------------------------------=== #

    def shrink(mut self) raises:
        """Run all shrink passes to a fixed point (or until stalled)."""
        try:
            self.reduce_each_alternative()
            self.greedy_shrink()
        except e:
            if String(e) != STOP_SHRINKING:
                raise e^
            self.stalled = True

    # ===------------------------------------------------------------------=== #
    # Explain phase
    # ===------------------------------------------------------------------=== #

    def explain(mut self) raises:
        """Find the arguments of the shrunk example that can vary freely
        without the test passing or failing differently, and note them
        (port of Hypothesis's `Shrinker._explain`).

        For each argument (a top-level draw), largest first, try replacing
        its choices: first with the choices of other arguments of the same
        shape (so `assert a != b` isn't misreported), then randomly. If 100
        variations fail in the same way, the argument gets the comment "or
        any other generated value"; one passing variation rules it out.
        Finally, if several arguments got comments, check whether they can
        all vary together.
        """
        if self.stalled:
            return
        ref target = self.target[]
        var target_id = target.id
        var nodes = target.nodes.copy()
        var choices = target.choices()
        var n_args = len(target.arg_spans)
        if n_args == 0:
            return
        var starts = List[Int]()
        var ends = List[Int]()
        for k in range(n_args):
            ref sp = target.spans[target.arg_spans[k]]
            starts.append(sp.start)
            ends.append(sp.end)
        # largest first, then by position
        var order = List[Int]()
        for k in range(n_args):
            order.append(k)
        for a in range(1, len(order)):
            var b = a
            while b > 0 and (
                ends[order[b]] - starts[order[b]]
                > ends[order[b - 1]] - starts[order[b - 1]]
            ):
                order.swap_elements(b, b - 1)
                b -= 1
        var chunks = Dict[Int, List[List[ChoiceValue]]]()
        for k in order:
            var start = starts[k]
            var end = ends[k]
            var all_forced = True
            for i in range(start, end):
                if not nodes[i].was_forced:
                    all_forced = False
            if all_forced:
                continue
            var inside_commented = False
            for c in self.arg_comments.keys():
                if starts[c] <= start and end <= ends[c]:
                    inside_commented = True
            if inside_commented:
                continue
            # candidates borrowed from other arguments of the same shape
            var candidates = List[List[ChoiceValue]]()
            for k2 in range(n_args):
                if k2 == k or ends[k2] - starts[k2] != end - start:
                    continue
                var same_kinds = True
                for j in range(end - start):
                    if nodes[starts[k2] + j].kind() != nodes[start + j].kind():
                        same_kinds = False
                if not same_kinds:
                    continue
                var borrowed = List[ChoiceValue]()
                for j in range(end - start):
                    borrowed.append(nodes[starts[k2] + j].value.copy())
                var dup = False
                for c in candidates:
                    if c == borrowed:
                        dup = True
                var current = List[ChoiceValue]()
                for j in range(start, end):
                    current.append(choices[j].copy())
                if not dup and borrowed != current:
                    candidates.append(borrowed^)
            var n_same = 0
            var chunk_list = List[List[ChoiceValue]]()
            for n_attempt in range(500 + len(candidates)):
                if n_attempt - 10 - len(candidates) > n_same * 5:
                    break  # mostly invalid variations
                var replacement: List[ChoiceValue]
                if n_attempt < len(candidates):
                    replacement = candidates[n_attempt].copy()
                else:
                    replacement = List[ChoiceValue]()
                    for i in range(start, end):
                        if nodes[i].was_forced:
                            replacement.append(nodes[i].value.copy())
                        else:
                            replacement.append(
                                self.runner.tree_provider.draw(
                                    nodes[i].constraints
                                )
                            )
                var attempt = List[ChoiceValue]()
                for i in range(start):
                    attempt.append(choices[i].copy())
                for v in replacement:
                    attempt.append(v.copy())
                for i in range(end, len(choices)):
                    attempt.append(choices[i].copy())
                var result = self.runner.cached_test_function(
                    attempt, extend=-1
                )
                if result[].status == Status.OVERRUN:
                    continue
                var arg_span = target.arg_spans[k]
                var same_suffix = len(result[].nodes) == len(attempt)
                if same_suffix:
                    for i in range(end, len(choices)):
                        if not (result[].nodes[i].value == choices[i]):
                            same_suffix = False
                            break
                if not same_suffix:
                    # a variable-length argument: take what it drew
                    if (
                        arg_span >= len(result[].spans)
                        or result[].spans[arg_span].start != start
                    ):
                        continue
                    var result_end = result[].spans[arg_span].end
                    var infix = List[ChoiceValue]()
                    for i in range(start, result_end):
                        infix.append(result[].nodes[i].value.copy())
                    var attempt2 = List[ChoiceValue]()
                    for i in range(start):
                        attempt2.append(choices[i].copy())
                    for v in infix:
                        attempt2.append(v.copy())
                    for i in range(end, len(choices)):
                        attempt2.append(choices[i].copy())
                    chunk_list.append(infix^)
                    result = self.runner.cached_test_function(attempt2)
                    if result[].status == Status.OVERRUN:
                        continue
                else:
                    var infix = List[ChoiceValue]()
                    for i in range(start, end):
                        infix.append(result[].nodes[i].value.copy())
                    chunk_list.append(infix^)
                if self.target[].id != target_id:
                    self.arg_comments = Dict[Int, String]()
                    return
                if result[].status == Status.VALID:
                    break  # this argument matters
                if self.predicate(result):
                    n_same += 1
                    if n_same >= 100:
                        self.arg_comments[k] = "or any other generated value"
                        break
            chunks[k] = chunk_list^
        if len(self.arg_comments) <= 1:
            return
        # can the commented arguments all vary together?
        var commented = List[Int]()
        for k in range(n_args):
            if k in self.arg_comments:
                commented.append(k)
        var n_together = 0
        for _ in range(500):
            var attempt = List[ChoiceValue]()
            var prev_end = 0
            for k in commented:
                for i in range(prev_end, starts[k]):
                    attempt.append(choices[i].copy())
                ref ls = chunks[k]
                if len(ls) == 0:
                    for i in range(starts[k], ends[k]):
                        attempt.append(choices[i].copy())
                else:
                    var pick = Int(self.runner.random.below(UInt64(len(ls))))
                    for v in ls[pick]:
                        attempt.append(v.copy())
                prev_end = ends[k]
            for i in range(prev_end, len(choices)):
                attempt.append(choices[i].copy())
            var result = self.runner.cached_test_function(attempt)
            if result[].status == Status.VALID:
                self.explain_note = (
                    "The test sometimes passed when commented parts were"
                    " varied together."
                )
                return
            if self.predicate(result):
                n_together += 1
                if n_together >= 100:
                    self.explain_note = (
                        "The test always failed when commented parts were"
                        " varied together."
                    )
                    return

    # ===------------------------------------------------------------------=== #
    # Pass scheduling
    # ===------------------------------------------------------------------=== #

    def pass_name(self, p: Int) -> String:
        if p == 0:
            return "try_trivial_spans"
        if p >= 1 and p <= 5:
            return String("node_program_", "X" * (6 - p))
        var names: List[String] = [
            "pass_to_descendant",
            "reorder_spans",
            "minimize_duplicated_choices",
            "minimize_individual_choices",
            "redistribute_numeric_pairs",
            "lower_integers_together",
            "lower_duplicated_characters",
            "normalize_unicode_chars",
        ]
        return names[p - 6]

    def positions(mut self, p: Int) -> Int:
        """How many positions pass `p` can be tried at on the current target."""
        var n = self.num_nodes()
        if p == 0 or p == 6 or p == 7:
            return len(self.target[].spans)
        if p >= 1 and p <= 5:
            return max(0, n - (6 - p) + 1)
        if p == 8:
            return len(self.duplicate_groups())
        return n

    def pass_at(mut self, p: Int, i: Int) raises:
        """Try pass `p` at position `i` (one "step")."""
        if p == 0:
            self.try_trivial_span_at(i)
        elif p >= 1 and p <= 5:
            self.node_program_at(6 - p, i)
        elif p == 6:
            self.pass_to_descendant_at(i)
        elif p == 7:
            self.reorder_spans_at(i)
        elif p == 8:
            self.minimize_duplicated_choices_at(i)
        elif p == 9:
            self.minimize_individual_choice_at(i)
        elif p == 10:
            self.redistribute_numeric_pairs_at(i)
        elif p == 11:
            self.lower_integers_together_at(i)
        elif p == 12:
            self.lower_duplicated_characters_at(i)
        else:
            self.normalize_unicode_chars_at(i)

    def step(mut self, p: Int, random_order: Bool) raises -> Bool:
        """Run pass `p` at one position not yet tried on the current target.
        False if every position has been tried (the pass is exhausted until
        the target changes).

        This stands in for Hypothesis's `ChoiceTree`: positions are tried in
        order starting where the pass last stopped, or in random order once
        the pass is stalling, and a pass is exhausted when all have been
        tried."""
        if self.tried_target != self.target[].id:
            self.tried_target = self.target[].id
            for k in range(N_PASSES):
                self.tried[k] = Set[Int]()
        var n = self.positions(p)
        if len(self.tried[p]) >= n:
            return False
        var i = -1
        if random_order:
            for _ in range(8):
                var c = Int(self.runner.random.below(UInt64(n)))
                if c not in self.tried[p]:
                    i = c
                    break
        if i < 0:
            var start = self.last_position[p] % n
            for d in range(n):
                var c = (start + d) % n
                if c not in self.tried[p]:
                    i = c
                    break
        self.tried[p].add(i)
        self.last_position[p] = i
        var calls_before = self.calls()
        var shrinks_before = self.shrinks
        var size_before = self.num_nodes()
        self.pass_at(p, i)
        self.pass_calls[p] += self.calls() - calls_before
        self.pass_shrinks[p] += self.shrinks - shrinks_before
        self.pass_deletions[p] += size_before - self.num_nodes()
        return True

    def greedy_shrink(mut self) raises:
        """Run the passes to a fixed point (port of `fixate_shrink_passes`).

        Each pass is stepped until it fails 20 times in a row (from the 10th
        failure on, at random positions), then the next pass gets a turn.
        After each round, passes that deleted choices move to the front and
        passes that did nothing to the back."""
        var passes = List[Int]()
        for p in range(N_PASSES):
            passes.append(p)
        var any_ran = True
        while any_ran:
            any_ran = False
            var keys = List[Int](length=N_PASSES, fill=0)
            var can_discard = self.remove_discarded()
            var calls_at_loop_start = self.calls()
            var max_calls_per_failing_step = 1
            for p in passes:
                if can_discard:
                    can_discard = self.remove_discarded()
                var before = self.target[].id
                var before_size = self.num_nodes()
                var failures = 0
                while failures < 20:
                    self.max_stall = max(
                        self.max_stall,
                        2 * max_calls_per_failing_step
                        + (self.calls() - calls_at_loop_start),
                    )
                    var prev = self.target[].id
                    var initial_calls = self.calls()
                    if not self.step(p, failures >= 10):
                        break
                    any_ran = True
                    if initial_calls != self.calls():
                        if prev != self.target[].id:
                            failures = 0
                        else:
                            max_calls_per_failing_step = max(
                                max_calls_per_failing_step,
                                self.calls() - initial_calls,
                            )
                            failures += 1
                if self.target[].id == before:
                    keys[p] = 1
                elif self.num_nodes() < before_size:
                    keys[p] = -1
                else:
                    keys[p] = 0
            # stable sort of the passes by key
            for a in range(1, len(passes)):
                var b = a
                while b > 0 and keys[passes[b - 1]] > keys[passes[b]]:
                    passes.swap_elements(b, b - 1)
                    b -= 1

    def report_pass_statistics(self):
        """Hypothesis's shrink pass profiling, printed at debug verbosity."""
        print(
            String(
                "  shrinking made ",
                self.calls() - self.initial_calls,
                " calls, of which ",
                self.shrinks,
                " shrank",
            )
        )
        for p in range(N_PASSES):
            if self.pass_calls[p] == 0:
                continue
            print(
                String(
                    "    ",
                    self.pass_name(p),
                    ": ",
                    self.pass_calls[p],
                    " calls, ",
                    self.pass_shrinks[p],
                    " shrinks, ",
                    self.pass_deletions[p],
                    " choices deleted",
                )
            )

    # ===------------------------------------------------------------------=== #
    # Passes, one position at a time
    # ===------------------------------------------------------------------=== #

    def remove_discarded(mut self) raises -> Bool:
        """Delete every discarded span (rejected filter draws and such) in
        one go. False if there are discards and deleting them failed."""
        while self.target[].has_discards:
            ref spans = self.target[].spans
            var regions = List[Tuple[Int, Int]]()
            for sp in spans:
                if (
                    sp.choice_count() > 0
                    and sp.discarded
                    and (
                        len(regions) == 0
                        or sp.start >= regions[len(regions) - 1][1]
                    )
                ):
                    regions.append((sp.start, sp.end))
            if len(regions) == 0:
                break
            var nodes = self.nodes()
            var attempt = List[ChoiceNode]()
            var r = 0
            var i = 0
            while i < len(nodes):
                if r < len(regions) and i == regions[r][0]:
                    i = regions[r][1]
                    r += 1
                    continue
                attempt.append(nodes[i].copy())
                i += 1
            if not self.consider(attempt^):
                return False
        return True

    def try_trivial_span_at(mut self, i: Int) raises:
        """Replace span `i` with its simplest choices."""
        if i >= len(self.target[].spans):
            return
        var prev = self.target[].id
        var sp = self.target[].spans[i].copy()
        var nodes = self.nodes()
        var prefix = _slice(nodes, 0, sp.start)
        var replacement = List[ChoiceNode]()
        for k in range(sp.start, min(sp.end, len(nodes))):
            if nodes[k].was_forced:
                replacement.append(nodes[k].copy())
            else:
                replacement.append(
                    nodes[k].with_value(choice_simplest(nodes[k].constraints))
                )
        var suffix = _slice(nodes, sp.end, len(nodes))
        var res = self.run_nodes(_concat(prefix, replacement, suffix))
        if self.target[].id == prev and res[1]:
            var attempt = res[1].value()
            if attempt[].status >= Status.VALID and i < len(attempt[].spans):
                var new_span = attempt[].spans[i].copy()
                var new_rep = _slice(
                    attempt[].nodes, new_span.start, new_span.end
                )
                _ = self.consider(_concat(prefix, new_rep, suffix))

    def run_node_program(
        mut self, i: Int, k: Int, var original: List[ChoiceNode], repeats: Int
    ) raises -> Bool:
        """Delete `k` nodes at `i`, `repeats` times."""
        if i < 0 or i + k > len(original):
            return False
        var attempt = original^
        for _ in range(repeats):
            if i + k > len(attempt):
                return False
            var out = List[ChoiceNode](capacity=len(attempt) - k)
            for j in range(len(attempt)):
                if j < i or j >= i + k:
                    out.append(attempt[j].copy())
            attempt = out^
        return self.consider(attempt^)

    def node_program_at(mut self, k: Int, i: Int) raises:
        """Delete `k` nodes at `i`; if that works, move left to the start of
        the deletable region and delete as many runs there as possible
        (`O(log m)` calls for `m` runs)."""
        if not self.run_node_program(i, k, self.nodes(), 1):
            return
        var start = i

        def offset_left(n: Int) raises {mut self, start, k} -> Bool:
            return self.run_node_program(start - n * k, k, self.nodes(), 1)

        start -= find_integer(offset_left) * k
        var original = self.nodes()

        def repeat(n: Int) raises {mut self, start, k, original} -> Bool:
            return self.run_node_program(start, k, original.copy(), n)

        _ = find_integer(repeat)

    def pass_to_descendant_at(mut self, i: Int) raises:
        """Replace span `i` with a smaller nested span with the same label."""
        if i >= len(self.target[].spans):
            return
        var spans = self.target[].spans.copy()
        var ancestor = spans[i].copy()
        var j = i + 1
        while j < len(spans):
            var d = spans[j].copy()
            if d.start >= ancestor.end:
                break
            if (
                d.label == ancestor.label
                and d.choice_count() < ancestor.choice_count()
                and d.choice_count() > 0
            ):
                var nodes = self.nodes()
                if self.consider(
                    _concat(
                        _slice(nodes, 0, ancestor.start),
                        _slice(nodes, d.start, d.end),
                        _slice(nodes, ancestor.end, len(nodes)),
                    )
                ):
                    return
            j += 1

    def reorder_spans_at(mut self, s: Int) raises:
        """Sort the children of span `s` that share a label."""
        if s >= len(self.target[].spans):
            return
        var children = self.target[].span_children(s)
        var done = Set[UInt64]()
        for c in children:
            if s >= len(self.target[].spans):
                return
            var lbl = self.target[].spans[c].label
            if lbl in done:
                continue
            done.add(lbl)
            var group = List[Int]()
            for c2 in children:
                if self.target[].spans[c2].label == lbl:
                    group.append(c2)
            if len(group) >= 2:
                self._reorder_group(group)
            children = self.target[].span_children(s)

    def _reorder_group(mut self, group: List[Int]) raises:
        var st = self.target
        var n = len(group)
        # rank the span contents by sort_key
        var contents = List[List[ChoiceNode]]()
        for g in group:
            ref sp = st[].spans[g]
            contents.append(_slice(st[].nodes, sp.start, sp.end))
        var keys = List[Int](length=n, fill=0)
        for a in range(n):
            var rank = 0
            for b in range(n):
                if sort_key_less(contents[b], contents[a]):
                    rank += 1
            keys[a] = rank
        var ids = List[Int]()
        for a in range(n):
            ids.append(a)

        def try_order(
            perm: List[Int],
        ) raises {mut self, st, group, contents} -> Bool:
            # rebuild the node list with span a's slot holding perm[a]'s nodes
            ref nodes = st[].nodes
            var out = List[ChoiceNode]()
            var pos = 0
            for a in range(len(group)):
                ref sp = st[].spans[group[a]]
                for k in range(pos, sp.start):
                    out.append(nodes[k].copy())
                for x in contents[perm[a]]:
                    out.append(x.copy())
                pos = sp.end
            for k in range(pos, len(nodes)):
                out.append(nodes[k].copy())
            return self.consider(out^)

        _ = shrink_ordering(ids^, keys^, try_order)

    def duplicate_groups(mut self) -> List[List[Int]]:
        """Groups of (two or more) equal, non-trivial choices in the current
        target, cached per target."""
        if self.dup_groups_target == self.target[].id:
            return self.dup_groups.copy()
        ref nodes = self.target[].nodes
        var groups = List[List[Int]]()
        var used = List[Bool](length=len(nodes), fill=False)
        for a in range(len(nodes)):
            if used[a] or nodes[a].trivial():
                continue
            var g = List[Int]()
            g.append(a)
            for b in range(a + 1, len(nodes)):
                if (
                    not used[b]
                    and nodes[b].value == nodes[a].value
                    and not nodes[b].trivial()
                ):
                    g.append(b)
                    used[b] = True
            if len(g) >= 2:
                groups.append(g^)
        self.dup_groups = groups.copy()
        self.dup_groups_target = self.target[].id
        return groups^

    def minimize_duplicated_choices_at(mut self, g: Int) raises:
        """Shrink the `g`-th group of equal choices together."""
        var groups = self.duplicate_groups()
        if g >= len(groups):
            return
        ref group = groups[g]
        if group[len(group) - 1] >= self.num_nodes():
            return
        self.minimize_nodes(group)

    def minimize_individual_choice_at(mut self, i: Int) raises:
        """Shrink choice `i`; if it can't be lowered because that changes the
        size of what follows, lower it by one and try deleting after it."""
        if i >= self.num_nodes():
            return
        var node = self.target[].nodes[i].copy()
        if node.trivial():
            return
        var before = self.target[].id
        var single = List[Int]()
        single.append(i)
        self.minimize_nodes(single)
        if self.target[].id != before or node.kind() != INTEGER:
            return
        var v = node.value.copy()
        v.i -= 1
        if not choice_permitted(v, node.constraints):
            return
        var lowered = self.replace_node(i, v^)
        var res = self.run_nodes(lowered.copy())
        if not res[1] or self.target[].id != before:
            return
        var attempt = res[1].value()
        if (
            attempt[].status < Status.VALID
            or len(attempt[].nodes) == self.num_nodes()
            or len(attempt[].nodes) == i + 1
        ):
            return
        # try deleting each later span, then each later node
        var spans = self.target[].spans.copy()
        var tries = 0
        for sp in spans:
            if sp.start <= i or sp.choice_count() == 0:
                continue
            if tries >= 16:
                break
            tries += 1
            if self.consider(
                _concat(
                    _slice(lowered, 0, sp.start),
                    List[ChoiceNode](),
                    _slice(lowered, sp.end, len(lowered)),
                )
            ):
                return
        for j in range(i + 1, min(len(lowered), i + 17)):
            if self.consider(
                _concat(
                    _slice(lowered, 0, j),
                    List[ChoiceNode](),
                    _slice(lowered, j + 1, len(lowered)),
                )
            ):
                return

    def minimize_nodes(mut self, indices: List[Int]) raises:
        """Shrink the (equal) nodes at `indices` together."""
        if indices[len(indices) - 1] >= self.num_nodes():
            return
        var node = self.target[].nodes[indices[0]].copy()
        var kind = node.kind()
        if kind == INTEGER:
            var st = node.constraints.shrink_towards
            var dist = _abs_diff(node.value.i, st)

            def up(n: UInt128) raises {mut self, indices, st} -> Bool:
                return self.try_shrinking_nodes(
                    indices, ChoiceValue(integer=st + Int128(n))
                )

            def down(n: UInt128) raises {mut self, indices, st} -> Bool:
                return self.try_shrinking_nodes(
                    indices, ChoiceValue(integer=st - Int128(n))
                )

            # Hypothesis first tries abs(value): the mirror image on the
            # simpler (positive) side of shrink_towards.
            _ = self.try_shrinking_nodes(
                indices, ChoiceValue(integer=st + Int128(dist))
            )
            if indices[len(indices) - 1] >= self.num_nodes():
                return
            dist = (
                _abs_diff(
                    self.target[].nodes[indices[0]].value.i, st
                ) if self.target[]
                .nodes[indices[0]]
                .kind()
                == INTEGER else dist
            )
            _ = shrink_integer(dist, up)
            _ = shrink_integer(dist, down)
        elif kind == FLOAT:
            var f = node.value.f
            if isnan(f):
                _ = self.try_shrinking_nodes(indices, ChoiceValue(float=0.0))
                return
            _ = self.try_shrinking_nodes(indices, ChoiceValue(float=abs(f)))

            def pos(v: Float64) raises {mut self, indices} -> Bool:
                return self.try_shrinking_nodes(indices, ChoiceValue(float=v))

            def neg(v: Float64) raises {mut self, indices} -> Bool:
                return self.try_shrinking_nodes(indices, ChoiceValue(float=-v))

            _ = shrink_float(abs(f), pos)
            _ = shrink_float(abs(f), neg)
        elif kind == BOOLEAN:
            if node.value.as_bool():
                _ = self.try_shrinking_nodes(
                    indices, ChoiceValue(boolean=False)
                )
        else:
            var c = node.constraints.copy()
            var orders = List[Int]()
            for x in node.value.seq:
                orders.append(element_order(c, x))
            var is_bytes = kind == BYTES

            def coll(
                v: List[Int],
            ) raises {mut self, indices, c, is_bytes} -> Bool:
                var seq = List[UInt32](capacity=len(v))
                for o in v:
                    if o < 0 or o >= c.alphabet_size():
                        return False
                    seq.append(element_from_order(c, o))
                if is_bytes:
                    return self.try_shrinking_nodes(
                        indices, ChoiceValue(bytes=seq^)
                    )
                return self.try_shrinking_nodes(
                    indices, ChoiceValue(string=seq^)
                )

            _ = shrink_collection(orders^, c.min_size, coll)

    def try_shrinking_nodes(
        mut self, indices: List[Int], var value: ChoiceValue
    ) raises -> Bool:
        """Replace each node at `indices` with `value` (port of
        `try_shrinking_nodes`, including its repairs when the change alters
        the size of what follows)."""
        var n = self.num_nodes()
        for i in indices:
            if i >= n:
                return False
        var initial = self.nodes()
        for i in indices:
            if initial[i].value.kind != value.kind:
                return False
            initial[i] = initial[i].with_value(value.copy())
        var res = self.run_nodes(initial.copy())
        if not res[1]:
            return res[0]
        var attempt = res[1].value()
        if res[0] and attempt[].id == self.target[].id:
            self.lower_common_node_offset()
            return True
        if attempt[].status == Status.OVERRUN:
            attempt = self.runner.cached_test_function(
                _values(initial), extend=-1
            )
            self.incorporate(attempt)
            if attempt[].status == Status.OVERRUN:
                return False
        if attempt[].status == Status.INVALID:
            return False
        # a lowered size choice can make a later string/bytes too long
        for i in range(min(len(initial), len(attempt[].nodes))):
            ref node = initial[i]
            ref anode = attempt[].nodes[i]
            if (
                node.kind() == anode.kind()
                and (node.kind() == STRING or node.kind() == BYTES)
                and not node.was_forced
                and len(node.value.seq) > anode.constraints.max_size
            ):
                var max_size = anode.constraints.max_size
                for front in [True, False]:
                    var seq = List[UInt32]()
                    var L = len(node.value.seq)
                    if front:
                        for k in range(max_size):
                            seq.append(node.value.seq[k])
                    else:
                        for k in range(L - max_size, L):
                            seq.append(node.value.seq[k])
                    var v2 = ChoiceValue(string=seq.copy())
                    v2.kind = node.kind()
                    var cand = initial.copy()
                    cand[i] = ChoiceNode(v2^, anode.constraints.copy(), False)
                    if self.consider(cand^):
                        return True
        var lost = self.num_nodes() - len(attempt[].nodes)
        if lost <= 0:
            return False
        var start = indices[0]
        var end = indices[len(indices) - 1] + 1
        var regions = List[Tuple[Int, Int]]()
        regions.append((end, end + lost))
        var spans = self.target[].spans.copy()
        for si in range(len(spans)):
            ref ex = spans[si]
            if ex.start > start or ex.end <= end:
                continue
            if si >= len(attempt[].spans):
                continue
            var in_original = List[Int]()
            for c in self.target[].span_children(si):
                if spans[c].start >= end:
                    in_original.append(c)
            var in_replaced = List[Int]()
            for c in attempt[].span_children(si):
                if attempt[].spans[c].start >= end:
                    in_replaced.append(c)
            if len(in_replaced) >= len(in_original) or len(in_replaced) == 0:
                continue
            regions.append(
                (
                    spans[in_original[0]].start,
                    spans[
                        in_original[len(in_original) - len(in_replaced)]
                    ].start,
                )
            )
        # biggest regions first
        for a in range(1, len(regions)):
            var b = a
            while b > 0 and (regions[b][1] - regions[b][0]) > (
                regions[b - 1][1] - regions[b - 1][0]
            ):
                regions.swap_elements(b, b - 1)
                b -= 1
        for reg in regions:
            var u = reg[0]
            var v = reg[1]
            if u >= v or u > len(initial):
                continue
            if self.consider(
                _concat(
                    _slice(initial, 0, u),
                    List[ChoiceNode](),
                    _slice(initial, v, len(initial)),
                )
            ):
                return True
        return False

    def lower_common_node_offset(mut self) raises:
        """When several integer nodes keep changing together, lower their
        common distance from `shrink_towards` all at once."""
        # track which nodes changed since the last check
        ref cur = self.target[].nodes
        if len(cur) != len(self.last_checked_nodes):
            self.changed_nodes = Set[Int]()
        else:
            for i in range(len(cur)):
                if cur[i].kind() != self.last_checked_nodes[i].kind():
                    self.changed_nodes = Set[Int]()
                    break
                if not (cur[i].value == self.last_checked_nodes[i].value):
                    self.changed_nodes.add(i)
        self.last_checked_nodes = cur.copy()
        if len(self.changed_nodes) <= 1:
            return
        var changed = List[Int]()
        for i in range(len(cur)):
            if i in self.changed_nodes:
                if cur[i].trivial() or cur[i].kind() != INTEGER:
                    continue
                changed.append(i)
        if len(changed) == 0:
            return
        var dists = List[UInt128]()
        for i in changed:
            dists.append(
                _abs_diff(cur[i].value.i, cur[i].constraints.shrink_towards)
            )
        var offset = dists[0]
        for d in dists:
            offset = min(offset, d)
        for k in range(len(dists)):
            dists[k] -= offset
        var base = cur.copy()
        var signs = List[Int]()
        for i in changed:
            signs.append(
                1 if cur[i].value.i >= cur[i].constraints.shrink_towards else -1
            )

        def consider_offset(
            n: UInt128,
        ) raises {mut self, base, changed, dists, signs} -> Bool:
            var attempt = base.copy()
            for k in range(len(changed)):
                var i = changed[k]
                var st = base[i].constraints.shrink_towards
                var d = Int128(n + dists[k])
                attempt[i] = base[i].with_value(
                    ChoiceValue(integer=st + d if signs[k] > 0 else st - d)
                )
            return self.consider(attempt^)

        _ = shrink_integer(offset, consider_offset)
        self.changed_nodes = Set[Int]()

    def redistribute_numeric_pairs_at(mut self, i: Int) raises:
        """Move value from numeric choice `i` to one of the next four."""
        if i >= self.num_nodes():
            return
        if (
            not self._numeric(self.target[].nodes[i])
            or self.target[].nodes[i].trivial()
        ):
            return
        for j in range(i + 1, min(i + 5, self.num_nodes())):
            if j >= self.num_nodes() or i >= self.num_nodes():
                return
            ref n2 = self.target[].nodes[j]
            if not self._numeric(n2) or n2.was_forced:
                continue
            self._boost(i, j)

    def _numeric(self, node: ChoiceNode) -> Bool:
        if node.kind() == INTEGER:
            return True
        if node.kind() == FLOAT:
            return (
                not isnan(node.value.f)
                and abs(node.value.f) < MAX_PRECISE_INTEGER
            )
        return False

    def _boost(mut self, i: Int, j: Int) raises:
        var base = self.nodes()
        var a = base[i].copy()
        var b = base[j].copy()

        def boost(k: Int) raises {mut self, base, a, b, i, j} -> Bool:
            var v1 = a.value.copy()
            var v2 = b.value.copy()
            if a.kind() == INTEGER:
                var st = a.constraints.shrink_towards
                if UInt128(k) > _abs_diff(v1.i, st):
                    return False
                var kk = Int128(k) if v1.i >= st else Int128(-k)
                v1.i -= kk
                if v2.kind == INTEGER:
                    v2.i += kk
                else:
                    v2.f += Float64(kk)
            else:
                if Float64(k) > abs(v1.f):
                    return False
                var kf = Float64(k) if v1.f >= 0 else -Float64(k)
                v1.f -= kf
                if v2.kind == INTEGER:
                    v2.i += Int128(Int(kf))
                else:
                    v2.f += kf
                    if abs(v2.f) >= MAX_PRECISE_INTEGER:
                        return False
            var attempt = base.copy()
            attempt[i] = a.with_value(v1^)
            attempt[j] = b.with_value(v2^)
            return self.consider(attempt^)

        _ = find_integer(boost)

    def lower_integers_together_at(mut self, i: Int) raises:
        """Lower integer choice `i` and one of the next three by the same
        amount."""
        if i >= self.num_nodes():
            return
        ref n1 = self.target[].nodes[i]
        if n1.kind() != INTEGER or n1.trivial():
            return
        for j in range(i + 1, min(i + 4, self.num_nodes())):
            if j >= self.num_nodes() or i >= self.num_nodes():
                break
            ref n2 = self.target[].nodes[j]
            if n2.kind() != INTEGER or n2.was_forced:
                continue
            var base = self.nodes()
            var st = base[i].constraints.shrink_towards

            def lower(n: Int) raises {mut self, base, i, j} -> Bool:
                var attempt = base.copy()
                var v1 = base[i].value.copy()
                var v2 = base[j].value.copy()
                v1.i -= Int128(n)
                v2.i -= Int128(n)
                attempt[i] = base[i].with_value(v1^)
                attempt[j] = base[j].with_value(v2^)
                return self.consider(attempt^)

            def raise_(n: Int) raises {mut self, base, i, j} -> Bool:
                var attempt = base.copy()
                var v1 = base[i].value.copy()
                var v2 = base[j].value.copy()
                v1.i += Int128(n)
                v2.i += Int128(n)
                attempt[i] = base[i].with_value(v1^)
                attempt[j] = base[j].with_value(v2^)
                return self.consider(attempt^)

            if base[i].value.i > st:
                _ = find_integer(lower)
            else:
                _ = find_integer(raise_)

    def lower_duplicated_characters_at(mut self, i: Int) raises:
        """Lower a character shared by string choice `i` and one of the next
        four, in both."""
        if i >= self.num_nodes():
            return
        ref n1 = self.target[].nodes[i]
        if n1.kind() != STRING or n1.trivial():
            return
        for j in range(i + 1, min(i + 5, self.num_nodes())):
            if j >= self.num_nodes() or i >= self.num_nodes():
                break
            ref n2 = self.target[].nodes[j]
            if n2.kind() != STRING or n2.trivial():
                continue
            # characters common to both strings
            var common = List[UInt32]()
            for x in self.target[].nodes[i].value.seq:
                var in2 = False
                for y in self.target[].nodes[j].value.seq:
                    if x == y:
                        in2 = True
                        break
                var dup = False
                for z in common:
                    if z == x:
                        dup = True
                if in2 and not dup:
                    common.append(x)
            for ch in common:
                var base = self.nodes()
                var c = base[i].constraints.copy()
                if ch not in c.alphabet():
                    continue
                var start = c.alphabet().index_from_char_in_shrink_order(ch)

                def replace(
                    n: UInt128,
                ) raises {mut self, base, i, j, ch, c} -> Bool:
                    if Int(n) >= c.alphabet_size():
                        return False
                    var newc = c.alphabet().char_in_shrink_order(Int(n))
                    var attempt = base.copy()
                    for idx in [i, j]:
                        var v = base[idx].value.copy()
                        for k in range(len(v.seq)):
                            if v.seq[k] == ch:
                                v.seq[k] = newc
                        attempt[idx] = base[idx].with_value(v^)
                    return self.consider(attempt^)

                _ = shrink_integer(UInt128(start), replace)
                if i >= self.num_nodes() or j >= self.num_nodes():
                    break

    def normalize_unicode_chars_at(mut self, i: Int) raises:
        """Replace characters of string choice `i` by simpler related
        characters, e.g. a lowercase letter by its uppercase form, which comes
        earlier in the default shrink order (`0`-`9`, then punctuation and
        `A`-`Z`), or `é` by `e`.

        Port of Hypothesis's pass of the same name: candidates come from
        case mapping, Unicode decomposition (NFD and NFKD, so an accented
        letter can become its base letter and a ligature or mathematical
        letter its ASCII form) and casefolding."""
        if i >= self.num_nodes():
            return
        if (
            self.target[].nodes[i].kind() != STRING
            or self.target[].nodes[i].was_forced
        ):
            return
        var j = 0
        while (
            i < self.num_nodes()
            and self.target[].nodes[i].kind() == STRING
            and j < len(self.target[].nodes[i].value.seq)
        ):
            var node = self.target[].nodes[i].copy()
            var ch = node.value.seq[j]
            if ch >= 128 and not self.decompositions:
                self.decompositions = Decompositions()
            var candidates = _simpler_case_chars(
                ch, node.constraints.alphabet(), self.decompositions
            )
            for cand in candidates:
                var v = node.value.copy()
                v.seq[j] = cand
                if self.consider(self.replace_node(i, v^)):
                    break
            j += 1

    def reduce_each_alternative(mut self) raises:
        """Try lowering choices that look like `one_of` branch selectors,
        re-generating what follows when the shape changes."""
        var i = 0
        while i < self.num_nodes():
            var nodes = self.nodes()
            ref node = nodes[i]
            if (
                node.kind() == INTEGER
                and not node.was_forced
                and node.value.i <= 10
                and node.value.i > 0
                and node.constraints.has_min
                and node.constraints.min_value == 0
            ):
                var res = self.run_nodes(
                    self.replace_node(i, ChoiceValue(integer=0))
                )
                if res[1] and res[1].value()[].id != self.target[].id:
                    var zero = res[1].value()
                    if zero[].status >= Status.VALID:
                        var changed_shape = len(zero[].nodes) != len(nodes)
                        if not changed_shape:
                            for j in range(i + 1, len(nodes)):
                                if zero[].nodes[j].kind() != nodes[
                                    j
                                ].kind() or not choice_permitted(
                                    nodes[j].value, zero[].nodes[j].constraints
                                ):
                                    changed_shape = True
                                    break
                        if changed_shape:
                            for v in range(Int(node.value.i)):
                                if self.try_lower_node_as_alternative(i, v):
                                    break
            i += 1

    def try_lower_node_as_alternative(mut self, i: Int, v: Int) raises -> Bool:
        var nodes = self.nodes()
        if i >= len(nodes):
            return False
        if self.consider(self.replace_node(i, ChoiceValue(integer=Int128(v)))):
            return True
        var prefix = _slice(nodes, 0, i)
        prefix.append(nodes[i].with_value(ChoiceValue(integer=Int128(v))))
        var initial = self.target
        var span_ids = List[Int]()
        for s in range(len(initial[].spans)):
            if initial[].spans[s].start == i:
                span_ids.append(s)
        for _ in range(3):
            var r = self.runner.cached_test_function(
                _values(prefix), extend=len(nodes)
            )
            if r[].status < Status.VALID:
                continue
            self.incorporate(r)
            for s in span_ids:
                if s >= len(r[].spans):
                    continue
                var init_span = initial[].spans[s].copy()
                var att_span = r[].spans[s].copy()
                var contents = _slice(r[].nodes, att_span.start, att_span.end)
                _ = self.consider(
                    _concat(
                        _slice(nodes, 0, i),
                        contents,
                        _slice(nodes, init_span.end, len(nodes)),
                    )
                )
                if initial[].id != self.target[].id:
                    return True
        return False
