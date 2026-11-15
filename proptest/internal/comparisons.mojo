# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The comparisons a test case made with `Traced` values.

A `Traced` value records each comparison it takes part in: where it was
made, its own value, the value it was compared with, and how close the
two were. The fuzz loop uses them as AFL++'s CmpLog and libFuzzer's value
profile use the operands of the program's comparison instructions:

- input-to-state replacement (Redqueen): a choice equal to the traced
  value is replaced by the value it was compared with (or one either side
  of it), which gets past checks like `x == 4242` that random mutation
  almost never satisfies;
- closeness as coverage: getting closer than before to equality at a
  comparison counts as a new feature, so the corpus keeps the steps
  toward it.

The engine also adds the compared-with values to the constants that
generation occasionally returns.
"""

from std.collections import Set
from std.hash import hash

from proptest.internal.choice import ChoiceValue, INTEGER

comptime MAX_COMPARISONS = 128
"""The most comparisons kept per test case (distinct ones; the first seen)."""


struct Comparison(Copyable):
    """One comparison made with a `Traced` value."""

    var site: UInt64
    """A hash of the comparison's source location."""
    var lhs: ChoiceValue
    """The traced value."""
    var rhs: ChoiceValue
    """The value it was compared with."""
    var closeness: Int
    """How close the two were: higher is closer (see `int_closeness` and
    `text_closeness`)."""

    def __init__(
        out self,
        site: UInt64,
        var lhs: ChoiceValue,
        var rhs: ChoiceValue,
        closeness: Int,
    ):
        self.site = site
        self.lhs = lhs^
        self.rhs = rhs^
        self.closeness = closeness


struct ComparisonLog(Movable):
    """The comparisons of one test case, shared by the test case and the
    `Traced` values drawn in it."""

    var entries: List[Comparison]
    var _seen: Set[UInt64]

    def __init__(out self):
        self.entries = List[Comparison]()
        self._seen = Set[UInt64]()

    def record(
        mut self,
        site: UInt64,
        var lhs: ChoiceValue,
        var rhs: ChoiceValue,
        closeness: Int,
    ):
        if len(self.entries) >= MAX_COMPARISONS:
            return
        var key = mix(mix(site, UInt64(hash(lhs))), UInt64(hash(rhs)))
        if key in self._seen:
            return
        self._seen.add(key)
        self.entries.append(Comparison(site, lhs^, rhs^, closeness))


def mix(a: UInt64, b: UInt64) -> UInt64:
    var z = (a ^ (b + 0x9E3779B97F4A7C15 + (a << 6) + (a >> 2))) * (
        0xBF58476D1CE4E5B9
    )
    return z ^ (z >> 31)


def int_closeness(a: Int128, b: Int128) -> Int:
    """128 minus the bit length of `|a - b|`: 128 when equal, and one more
    for each halving of the distance."""
    var d = UInt128(a - b) if a >= b else UInt128(b - a)
    var n = 128
    while d > 0:
        d >>= 1
        n -= 1
    return n


def text_closeness(a: List[UInt32], b: List[UInt32]) -> Int:
    """Twice the length of the common prefix, plus one if equal."""
    var n = 0
    while n < len(a) and n < len(b) and a[n] == b[n]:
        n += 1
    return 2 * n + (1 if n == len(a) and n == len(b) else 0)
