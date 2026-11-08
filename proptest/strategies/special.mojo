# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Special-purpose generated types: stand-ins for testing generic code,
and indices resolved later.

- `PolyA`, `PolyB`, `PolyC` (QuickCheck's `Test.QuickCheck.Poly`): opaque
  stand-in types for instantiating generic properties. Testing a generic
  `reverse[T]` with `Int` lets a property pass by arithmetic accident (or
  lets a test lean on `Int`-only behavior); with `PolyA` it can't.
- `Index` (Rust proptest's `sample::Index`): a position drawn before the
  collection it indexes is known, resolved with `index.get(len)`. Handy
  in typed state-machine transitions, which are drawn before the state
  they act on is inspected.
"""

from std.hash import Hasher

from proptest.internal.data import ConjectureData
from proptest.strategies.types import Arbitrary
from proptest.strategies.core import integers


struct Poly[tag: StaticString](
    Arbitrary,
    Comparable,
    Copyable,
    Hashable,
    TrivialRegisterPassable,
    Writable,
):
    """An opaque value for instantiating generic code in tests; see
    `PolyA`. Supports only equality, ordering, hashing and printing."""

    var value: Int

    def __init__(out self, value: Int):
        self.value = value

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers()))

    def __eq__(self, other: Self) -> Bool:
        return self.value == other.value

    def __lt__(self, other: Self) -> Bool:
        return self.value < other.value

    def __hash__[H: Hasher](self, mut hasher: H):
        self.value.__hash__(hasher)

    def write_to(self, mut writer: Some[Writer]):
        writer.write(Self.tag, "(", self.value, ")")


comptime PolyA = Poly["A"]
"""A stand-in type for a generic parameter (QuickCheck's `A`)."""
comptime PolyB = Poly["B"]
"""A second stand-in type, distinct from `PolyA`."""
comptime PolyC = Poly["C"]
"""A third stand-in type."""


struct Index(Arbitrary, Copyable, TrivialRegisterPassable, Writable):
    """A position in a collection whose length isn't known yet (Rust
    proptest's `sample::Index`). Shrinks towards the first element."""

    var raw: UInt64

    def __init__(out self, raw: UInt64):
        self.raw = raw

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        return Self(UInt64(data.draw_integer(Int128(0), Int128(UInt64.MAX))))

    def get(self, size: Int) raises -> Int:
        """The position this index picks in a collection of `size`
        elements (`size` must be positive)."""
        if size <= 0:
            raise Error("Index.get: the collection is empty")
        # the high bits, scaled: shrinking `raw` towards 0 moves the
        # position towards 0 for every size
        return Int((UInt128(self.raw) * UInt128(size)) >> 64)

    def write_to(self, mut writer: Some[Writer]):
        # as the fraction of the way through the collection
        writer.write("Index(", Float64(self.raw) / 18446744073709551616.0, ")")
