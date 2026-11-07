# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The Pareto front of test cases, for multi-objective targeting.

Port of `hypothesis.internal.conjecture.pareto`. A test case *dominates*
another if it is at least as good in every way -- simpler (by `sort_key`),
at least as good a status, the same bug if both fail, and at least as high a
score for every `target()` label -- and better in one. The engine keeps an
approximate front of non-dominated valid test cases, saves it in the example
database so the next run starts from the best inputs found so far, and at
the end of the target phase shrinks each member of the front while keeping
it non-dominated.

Hypothesis also compares structural-coverage tags, which proptest doesn't
record.
"""

from std.collections import Set
from std.math import inf

from proptest.internal.choice import ChoiceValue, sort_key_less
from proptest.internal.data import ConjectureResult, Result, Status
from proptest.internal.random import Random

comptime NO_DOMINANCE = 0
comptime EQUAL = 1
comptime LEFT_DOMINATES = 2
comptime RIGHT_DOMINATES = 3


def _same_key(a: ConjectureResult, b: ConjectureResult) -> Bool:
    return not sort_key_less(a.nodes, b.nodes) and not sort_key_less(
        b.nodes, a.nodes
    )


def _score(r: ConjectureResult, label: String) -> Float64:
    try:
        if label in r.target_observations:
            return r.target_observations[label]
    except:
        pass
    return -inf[DType.float64]()


def _left_dominates_if_simpler(
    left: ConjectureResult, right: ConjectureResult
) -> Bool:
    """Assuming `left` is simpler, whether it dominates `right`."""
    if left.status < right.status:
        return False
    if (
        left.status == Status.INTERESTING
        and right.interesting_origin.byte_length() > 0
        and left.interesting_origin != right.interesting_origin
    ):
        return False
    for label in left.target_observations.keys():
        if _score(right, label) > _score(left, label):
            return False
    for label in right.target_observations.keys():
        if _score(right, label) > _score(left, label):
            return False
    return True


def dominance(left: ConjectureResult, right: ConjectureResult) -> Int:
    """`LEFT_DOMINATES`, `RIGHT_DOMINATES`, `EQUAL` or `NO_DOMINANCE`."""
    if _same_key(left, right):
        return EQUAL
    if sort_key_less(right.nodes, left.nodes):
        return RIGHT_DOMINATES if _left_dominates_if_simpler(
            right, left
        ) else NO_DOMINANCE
    return LEFT_DOMINATES if _left_dominates_if_simpler(
        left, right
    ) else NO_DOMINANCE


struct ParetoFront(Movable, Sized):
    """An approximate Pareto front of valid test cases, kept sorted by
    `sort_key`. Like Hypothesis's, it is approximate: adding checks a random
    sample of the front for dominance, not all of it."""

    var front: List[Result]
    var random: Random
    var evicted: List[List[ChoiceValue]]
    """Choices of members removed since the engine last looked (so it can
    delete them from the database)."""

    def __init__(out self, var random: Random):
        self.front = List[Result]()
        self.random = random^
        self.evicted = List[List[ChoiceValue]]()

    def __len__(self) -> Int:
        return len(self.front)

    def index_of(self, r: Result) -> Int:
        for i in range(len(self.front)):
            if self.front[i][].id == r[].id:
                return i
        return -1

    def contains(self, r: Result) -> Bool:
        return self.index_of(r) >= 0

    def bisect_left(self, r: Result) -> Int:
        """The first position whose member is not simpler than `r`."""
        var lo = 0
        var hi = len(self.front)
        while lo < hi:
            var mid = (lo + hi) // 2
            if sort_key_less(self.front[mid][].nodes, r[].nodes):
                lo = mid + 1
            else:
                hi = mid
        return lo

    def remove(mut self, r: Result):
        var i = self.index_of(r)
        if i >= 0:
            self.evicted.append(self.front[i][].choices())
            _ = self.front.pop(i)

    def add(mut self, r: Result) -> Bool:
        """Try to add `r`; True if it is in the front afterwards (port of
        `ParetoFront.add`)."""
        if r[].status < Status.VALID:
            return False
        if len(self.front) == 0:
            self.front.append(r)
            return True
        for m in self.front:
            if _same_key(m[], r[]):
                return m[].id == r[].id
        var i = self.bisect_left(r)
        self.front.insert(i, r)
        var to_remove = List[Int]()  # ids
        # Simpler members can't be dominated by r; sample the more complex
        # ones until 10 in a row aren't dominated.
        var later = List[Int]()
        for j in range(i + 1, len(self.front)):
            later.append(j)
        var failures = 0
        while len(later) > 0 and failures < 10:
            var k = Int(self.random.below(UInt64(len(later))))
            var j = later.pop(k)
            var d = dominance(r[], self.front[j][])
            if d == LEFT_DOMINATES:
                to_remove.append(self.front[j][].id)
                failures = 0
            else:
                failures += 1
        # Then check whether a sample of the simpler members dominates r (or
        # each other), keeping up to 10 mutually non-dominated "dominators".
        var dominators = List[Result]()
        dominators.append(r)
        var earlier = List[Int]()
        for j in range(i):
            earlier.append(j)
        var r_removed = False
        while len(earlier) > 0 and len(dominators) < 10:
            var k = Int(self.random.below(UInt64(len(earlier))))
            var cand = self.front[earlier.pop(k)]
            var replaced = False
            var j = 0
            var keep = True
            while j < len(dominators):
                var d = dominance(cand[], dominators[j][])
                if d == LEFT_DOMINATES:
                    to_remove.append(dominators[j][].id)
                    if dominators[j][].id == r[].id:
                        r_removed = True
                    if not replaced:
                        replaced = True
                        dominators[j] = cand
                        j += 1
                    else:
                        _ = dominators.pop(j)
                    keep = False
                elif d == RIGHT_DOMINATES:
                    to_remove.append(cand[].id)
                    keep = False
                    break
                elif d == EQUAL:
                    keep = False
                    break
                else:
                    j += 1
            if keep:
                dominators.append(cand)
        for id in to_remove:
            for j in range(len(self.front)):
                if self.front[j][].id == id:
                    if id != r[].id:
                        self.evicted.append(self.front[j][].choices())
                    _ = self.front.pop(j)
                    break
        return not r_removed and self.contains(r)
