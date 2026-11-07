# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""A trie of every choice sequence the test has been run on.

Simplified port of `hypothesis.internal.conjecture.datatree.DataTree`. The
engine records each finished test case in the tree, and asks it for a
*novel prefix* -- a sequence of choices that no previous test case started
with -- before generating a new one. That avoids running the same input
twice, and when every branch of the tree has been fully explored (the tree
is *exhausted*, which happens for small finite search spaces such as
`booleans()` or `integers(0, 9)`), generation stops early.

Unlike Hypothesis's version this does not compress linear runs of nodes,
and it does not detect flaky (non-deterministic) strategies.
"""

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
    choice_from_index,
    choice_permitted,
)
from proptest.internal.floats import float_to_int, is_negative
from proptest.internal.provider import Provider

comptime _MANY = UInt128(1) << 120
"""Stands for "too many children to ever exhaust"."""


def _count_strings(alphabet: Int, min_size: Int, max_size: Int) -> UInt128:
    if alphabet == 0:
        return 1
    if alphabet == 1:
        return UInt128(max_size - min_size + 1)
    var total = UInt128(0)
    var power = UInt128(1)
    for _ in range(min_size):
        power *= UInt128(alphabet)
        if power > _MANY:
            return _MANY
    for _ in range(min_size, max_size + 1):
        total += power
        if total > _MANY:
            return _MANY
        power *= UInt128(alphabet)
        if power > _MANY:
            return _MANY
    return total


def _count_floats(lo: Float64, hi: Float64) -> UInt128:
    """Number of floats in [lo, hi] (plus NaN), counting -0.0 and 0.0."""
    if is_negative(lo) == is_negative(hi):
        var a = float_to_int(lo)
        var b = float_to_int(hi)
        return UInt128(b - a + 1) if b >= a else UInt128(a - b + 1)
    # spans zero: [lo, -0.0] and [0.0, hi]
    return UInt128(float_to_int(lo) - float_to_int(-0.0) + 1) + UInt128(
        float_to_int(hi) - float_to_int(0.0) + 1
    )


def compute_max_children(c: Constraints) -> UInt128:
    """How many distinct choices `c` allows (capped at a huge number)."""
    if c.kind == INTEGER:
        if c.has_min and c.has_max:
            return UInt128(c.max_value - c.min_value) + 1
        return _MANY
    if c.kind == BOOLEAN:
        if c.p <= 5.421010862427522e-20 or c.p >= 1 - 5.421010862427522e-20:
            return 1
        return 2
    if c.kind == BYTES:
        return _count_strings(256, c.min_size, c.max_size)
    if c.kind == STRING:
        return _count_strings(c.alphabet_size(), c.min_size, c.max_size)
    # floats
    if isnan(c.fmin) or isnan(c.fmax):
        return _MANY
    var n = _count_floats(c.fmin, c.fmax)
    if c.allow_nan:
        n += 1
    return n


struct TreeNode(Copyable):
    var constraints: Optional[Constraints]
    """The constraints of the choice made at this node, once known."""
    var forced: Bool
    var children: Dict[ChoiceValue, Int]
    var conclusion: Bool
    """A test case finished here (no further choices were made)."""
    var exhausted: Bool

    def __init__(out self):
        self.constraints = None
        self.forced = False
        self.children = Dict[ChoiceValue, Int]()
        self.conclusion = False
        self.exhausted = False


struct DataTree(Movable):
    """The tree of choice sequences tried so far."""

    var nodes: List[TreeNode]

    def __init__(out self):
        self.nodes = List[TreeNode]()
        self.nodes.append(TreeNode())

    def is_exhausted(self) -> Bool:
        return self.nodes[0].exhausted

    def record(mut self, nodes: List[ChoiceNode], complete: Bool) -> String:
        """Add a test case's choices. `complete` is false for test cases that
        were cut short (overruns), whose endpoint is not a real conclusion.

        Returns a description of the inconsistency if the test case shows
        that data generation is not deterministic (Hypothesis's
        `FlakyStrategyDefinition`), else an empty string."""
        var path = List[Int]()
        var cur = 0
        path.append(cur)
        for k in range(len(nodes)):
            ref n = nodes[k]
            if self.nodes[cur].conclusion:
                return String(
                    "a run drew more data after choice ",
                    k,
                    (
                        " than an earlier run with the same choices, which"
                        " stopped there"
                    ),
                )
            if not self.nodes[cur].constraints:
                self.nodes[cur].constraints = n.constraints.copy()
                self.nodes[cur].forced = n.was_forced
            elif not (self.nodes[cur].constraints.value() == n.constraints):
                return String(
                    "choice ",
                    k,
                    " was drawn under ",
                    n.constraints,
                    (
                        " but an earlier run with the same preceding choices"
                        " drew it under "
                    ),
                    self.nodes[cur].constraints.value(),
                )
            elif n.was_forced and not self.nodes[cur].forced:
                return String(
                    "choice ",
                    k,
                    " was forced, but was not forced in an earlier run",
                )
            var nxt: Int
            try:
                if n.value in self.nodes[cur].children:
                    nxt = self.nodes[cur].children[n.value]
                else:
                    nxt = len(self.nodes)
                    self.nodes.append(TreeNode())
                    self.nodes[cur].children[n.value.copy()] = nxt
            except:
                return String()
            cur = nxt
            path.append(cur)
        if complete:
            if len(self.nodes[cur].children) > 0:
                return String(
                    "a run stopped after ",
                    len(nodes),
                    (
                        " choices, but an earlier run with the same choices"
                        " continued to draw more"
                    ),
                )
            self.nodes[cur].conclusion = True
        # propagate exhaustion upwards
        for k in range(len(path) - 1, -1, -1):
            if not self._check_exhausted(path[k]):
                break
        return String()

    def _check_exhausted(mut self, i: Int) -> Bool:
        ref node = self.nodes[i]
        if node.exhausted:
            return True
        if node.conclusion:
            node.exhausted = True
            return True
        if not node.constraints:
            return False
        var limit = UInt128(1) if node.forced else compute_max_children(
            node.constraints.value()
        )
        if UInt128(len(node.children)) < limit:
            return False
        for child in node.children.values():
            if not self.nodes[child].exhausted:
                return False
        self.nodes[i].exhausted = True
        return True

    def simulate(
        self, choices: List[ChoiceValue]
    ) -> Optional[List[ChoiceValue]]:
        """If running the test on `choices` is known to end exactly as a
        recorded test case did, the choices that test case actually used
        (a prefix of `choices`, with forced values substituted)."""
        var used = List[ChoiceValue]()
        var cur = 0
        var k = 0
        while True:
            ref node = self.nodes[cur]
            if node.conclusion:
                return used^
            if not node.constraints or k >= len(choices):
                return None
            var nxt = -1
            if node.forced:
                for item in node.children.items():
                    used.append(item.key.copy())
                    nxt = item.value
                    break
            else:
                ref v = choices[k]
                if not choice_permitted(v, node.constraints.value()):
                    return None
                try:
                    if v in node.children:
                        nxt = node.children[v]
                        used.append(v.copy())
                except:
                    return None
            if nxt < 0:
                return None
            cur = nxt
            k += 1

    def extend_randomly(
        self,
        prefix: List[ChoiceValue],
        mut provider: Provider,
        max_choices: Int,
    ) -> Optional[List[ChoiceValue]]:
        """Follow `prefix` through the tree, then continue with random choices
        until reaching a part of the tree not yet explored. Returns the
        choices up to and including the first new one, or None if the walk
        ends at a recorded test case (running it would repeat that case)."""
        var out = List[ChoiceValue]()
        var cur = 0
        for v in prefix:
            ref node = self.nodes[cur]
            if node.conclusion:
                return None
            if not node.constraints:
                return prefix.copy()
            try:
                if v not in node.children:
                    return prefix.copy()
                cur = node.children[v]
            except:
                return prefix.copy()
            out.append(v.copy())
        while len(out) < max_choices:
            ref node = self.nodes[cur]
            if node.conclusion:
                return None
            if not node.constraints:
                return out^
            var v: ChoiceValue
            if node.forced:
                var found = False
                v = ChoiceValue(integer=0)
                for item in node.children.items():
                    v = item.key.copy()
                    found = True
                    break
                if not found:
                    return out^
            else:
                v = provider.draw(node.constraints.value())
                if not choice_permitted(v, node.constraints.value()):
                    return out^
            try:
                if v not in node.children:
                    out.append(v^)
                    return out^
                cur = node.children[v]
            except:
                return out^
            out.append(v^)
        return out^

    def generate_novel_prefix(
        mut self, mut provider: Provider
    ) -> List[ChoiceValue]:
        """A choice sequence that no recorded test case starts with (assuming
        the tree is not exhausted). The engine extends it randomly."""
        var prefix = List[ChoiceValue]()
        var cur = 0
        while True:
            if not self.nodes[cur].constraints or self.nodes[cur].conclusion:
                return prefix^
            var c = self.nodes[cur].constraints.value().copy()
            if self.nodes[cur].forced:
                var moved = False
                for item in self.nodes[cur].children.items():
                    prefix.append(item.key.copy())
                    cur = item.value
                    moved = True
                    break
                if not moved:
                    return prefix^
                continue
            var next_node = -1
            # random draws first: in big spaces they are almost always novel
            for _ in range(8):
                var v = provider.draw(c)
                if not choice_permitted(v, c):
                    continue
                try:
                    if v not in self.nodes[cur].children:
                        prefix.append(v^)
                        return prefix^
                    var child = self.nodes[cur].children[v]
                    if not self.nodes[child].exhausted:
                        prefix.append(v^)
                        next_node = child
                        break
                except:
                    pass
            if next_node < 0:
                # enumerate small spaces for an unseen value
                var limit = compute_max_children(c)
                if (
                    UInt128(len(self.nodes[cur].children)) < limit
                    and limit <= 4096
                ):
                    for k in range(Int(limit)):
                        try:
                            var v = choice_from_index(UInt128(k), c)
                            if v not in self.nodes[cur].children:
                                prefix.append(v^)
                                return prefix^
                        except:
                            break
                # otherwise any non-exhausted child
                for item in self.nodes[cur].children.items():
                    if not self.nodes[item.value].exhausted:
                        prefix.append(item.key.copy())
                        next_node = item.value
                        break
            if next_node < 0:
                # everything below is exhausted (stale bookkeeping)
                _ = self._check_exhausted(cur)
                return prefix^
            cur = next_node
