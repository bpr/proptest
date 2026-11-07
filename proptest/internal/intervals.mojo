# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Sets of Unicode codepoints as sorted disjoint intervals.

Port of `hypothesis.internal.intervalsets.IntervalSet`. Characters are
handled as codepoints (`UInt32`); strings drawn by the engine are lists of
codepoints until a strategy turns them into a `String`.
"""

from std.hash import Hasher

comptime MAX_CODEPOINT: UInt32 = 0x10FFFF
comptime SURROGATE_LO: UInt32 = 0xD800
comptime SURROGATE_HI: UInt32 = 0xDFFF


struct IntervalSet(Copyable, Equatable, Hashable, Sized, Writable):
    """A set of codepoints, stored as sorted, disjoint, non-adjacent closed
    intervals `[lo, hi]`."""

    var lows: List[UInt32]
    var highs: List[UInt32]
    var offsets: List[Int]
    """`offsets[i]` is the number of codepoints in the intervals before `i`."""
    var size: Int
    var idx_of_zero: Int
    var idx_of_Z: Int

    def __init__(out self):
        """The empty set."""
        self.lows = List[UInt32]()
        self.highs = List[UInt32]()
        self.offsets = List[Int]()
        self.size = 0
        self.idx_of_zero = 0
        self.idx_of_Z = -1

    def __init__(out self, var intervals: List[Tuple[UInt32, UInt32]]):
        """The union of the given closed intervals (in any order)."""
        sort_intervals(intervals)
        self.lows = List[UInt32]()
        self.highs = List[UInt32]()
        for iv in intervals:
            var lo = iv[0]
            var hi = iv[1]
            if hi < lo:
                continue
            if len(self.lows) > 0 and lo <= self.highs[len(self.highs) - 1] + 1:
                if hi > self.highs[len(self.highs) - 1]:
                    self.highs[len(self.highs) - 1] = hi
            else:
                self.lows.append(lo)
                self.highs.append(hi)
        self.offsets = List[Int]()
        self.size = 0
        self.idx_of_zero = 0
        self.idx_of_Z = -1
        self._finish()

    def _finish(mut self):
        self.offsets = List[Int](capacity=len(self.lows))
        var total = 0
        for i in range(len(self.lows)):
            self.offsets.append(total)
            total += Int(self.highs[i] - self.lows[i]) + 1
        self.size = total
        self.idx_of_zero = self.index_above(UInt32(ord("0")))
        self.idx_of_Z = min(self.index_above(UInt32(ord("Z"))), self.size - 1)

    @staticmethod
    def from_string(s: String) -> Self:
        """The set of codepoints occurring in `s`."""
        var ivs = List[Tuple[UInt32, UInt32]]()
        for c in s.codepoints():
            ivs.append((c.to_u32(), c.to_u32()))
        return Self(ivs^)

    @staticmethod
    def range(lo: UInt32, hi: UInt32) -> Self:
        """The codepoints in `[lo, hi]`."""
        var ivs = List[Tuple[UInt32, UInt32]]()
        ivs.append((lo, hi))
        return Self(ivs^)

    @staticmethod
    def default_text() -> Self:
        """All codepoints except surrogates (which UTF-8 cannot encode)."""
        var ivs = List[Tuple[UInt32, UInt32]]()
        ivs.append((UInt32(0), SURROGATE_LO - 1))
        ivs.append((SURROGATE_HI + 1, MAX_CODEPOINT))
        return Self(ivs^)

    def __len__(self) -> Int:
        return self.size

    def num_intervals(self) -> Int:
        return len(self.lows)

    def __getitem__(self, i: Int) -> UInt32:
        """The `i`-th smallest codepoint in the set."""
        # binary search over offsets
        var lo = 0
        var hi = len(self.offsets)
        while lo + 1 < hi:
            var mid = (lo + hi) // 2
            if self.offsets[mid] <= i:
                lo = mid
            else:
                hi = mid
        return self.lows[lo] + UInt32(i - self.offsets[lo])

    def __contains__(self, c: UInt32) -> Bool:
        var j = self._interval_at_or_before(c)
        return j >= 0 and c <= self.highs[j]

    def _interval_at_or_before(self, c: UInt32) -> Int:
        """Index of the last interval whose low end is <= c, or -1."""
        var lo = 0
        var hi = len(self.lows)
        if hi == 0 or c < self.lows[0]:
            return -1
        while lo + 1 < hi:
            var mid = (lo + hi) // 2
            if self.lows[mid] <= c:
                lo = mid
            else:
                hi = mid
        return lo

    def index(self, c: UInt32) -> Int:
        """The position of `c` in the set (which must contain it)."""
        var j = self._interval_at_or_before(c)
        return self.offsets[j] + Int(c - self.lows[j])

    def index_above(self, c: UInt32) -> Int:
        """The position of the smallest element >= c (or `len(self)`)."""
        var j = self._interval_at_or_before(c)
        if j < 0:
            return 0
        if c <= self.highs[j]:
            return self.offsets[j] + Int(c - self.lows[j])
        if j + 1 < len(self.lows):
            return self.offsets[j + 1]
        return self.size

    def char_in_shrink_order(self, i: Int) -> UInt32:
        """The `i`-th codepoint in shrink order, which puts `0`..`Z` (and the
        characters between) first, then the characters below `0` in reverse,
        then everything above `Z`."""
        var k = i
        if k <= self.idx_of_Z:
            var n = self.idx_of_Z - self.idx_of_zero
            if k <= n:
                k += self.idx_of_zero
            else:
                k = self.idx_of_zero - (k - n)
        return self[k]

    def index_from_char_in_shrink_order(self, c: UInt32) -> Int:
        """Inverse of `char_in_shrink_order`."""
        var i = self.index(c)
        if i <= self.idx_of_Z:
            var n = self.idx_of_Z - self.idx_of_zero
            if self.idx_of_zero <= i and i <= self.idx_of_Z:
                i -= self.idx_of_zero
            else:
                i = self.idx_of_zero - i + n
        return i

    def union(self, other: Self) -> Self:
        var ivs = self.intervals()
        ivs.extend(other.intervals())
        return Self(ivs^)

    def difference(self, other: Self) -> Self:
        var out = List[Tuple[UInt32, UInt32]]()
        for i in range(len(self.lows)):
            var lo = self.lows[i]
            var hi = self.highs[i]
            for j in range(len(other.lows)):
                var olo = other.lows[j]
                var ohi = other.highs[j]
                if ohi < lo or olo > hi:
                    continue
                if olo > lo:
                    out.append((lo, olo - 1))
                if ohi >= hi:
                    lo = 1
                    hi = 0
                    break
                lo = ohi + 1
            if lo <= hi:
                out.append((lo, hi))
        return Self(out^)

    def intersection(self, other: Self) -> Self:
        var out = List[Tuple[UInt32, UInt32]]()
        for i in range(len(self.lows)):
            for j in range(len(other.lows)):
                var lo = max(self.lows[i], other.lows[j])
                var hi = min(self.highs[i], other.highs[j])
                if lo <= hi:
                    out.append((lo, hi))
        return Self(out^)

    def intervals(self) -> List[Tuple[UInt32, UInt32]]:
        var out = List[Tuple[UInt32, UInt32]](capacity=len(self.lows))
        for i in range(len(self.lows)):
            out.append((self.lows[i], self.highs[i]))
        return out^

    def __eq__(self, other: Self) -> Bool:
        return self.lows == other.lows and self.highs == other.highs

    def __hash__[H: Hasher](self, mut hasher: H):
        (self.lows).__hash__(hasher)
        (self.highs).__hash__(hasher)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("IntervalSet([")
        for i in range(len(self.lows)):
            if i > 0:
                writer.write(", ")
            writer.write("(", self.lows[i], ", ", self.highs[i], ")")
        writer.write("])")


def sort_intervals(mut ivs: List[Tuple[UInt32, UInt32]]):
    """Insertion sort by low end (interval lists are short)."""
    for i in range(1, len(ivs)):
        var j = i
        while j > 0 and ivs[j - 1][0] > ivs[j][0]:
            var t = ivs[j - 1]
            ivs[j - 1] = ivs[j]
            ivs[j] = t
            j -= 1


def codepoints_to_string(cps: List[UInt32]) -> String:
    """Encode codepoints as a UTF-8 `String`."""
    var s = String()
    for c in cps:
        var cp = Codepoint.from_u32(c)
        if cp:
            s += String(cp.value())
    return s^


def string_to_codepoints(s: String) -> List[UInt32]:
    """Decode a `String` into codepoints."""
    var out = List[UInt32]()
    for c in s.codepoints():
        out.append(c.to_u32())
    return out^
