# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Shrinkers for individual values.

Port of `hypothesis.internal.conjecture.shrinking` (`common.py`,
`integer.py`, `floats.py`, `ordering.py`, `collection.py`) and of
`find_integer` from `junkdrawer.py`.

Each shrinker takes an initial value and a predicate `consider(v) -> Bool`
that reports whether `v` (which is simpler than the current value) still
has the property being shrunk for. It calls the predicate on a series of
progressively simpler candidates and returns the simplest one accepted.
Candidates already tried are not retried.
"""

from std.collections import Set
from std.math import isnan, isinf, floor, ceil

from proptest.internal.floats import (
    float_to_lex,
    float_to_int,
    int_to_float,
    MAX_PRECISE_INTEGER,
    FLOAT_MAX,
    pos_inf,
    float_nan,
)


def find_integer[P: def(Int) raises -> Bool](f: P) raises -> Int:
    """The largest `n` with `f(n)` true, assuming `f(0)` is true and `f` is
    (roughly) monotone. Uses O(log n) calls: a linear scan of 1..4, then
    exponential probing and binary search."""
    for i in range(1, 5):
        if not f(i):
            return i - 1
    var lo = 4
    var hi = 5
    while f(hi):
        lo = hi
        hi *= 2
    while lo + 1 < hi:
        var mid = (lo + hi) // 2
        if f(mid):
            lo = mid
        else:
            hi = mid
    return lo


def _bit_length(x: UInt128) -> Int:
    var n = 0
    var y = x
    while y != 0:
        y >>= 1
        n += 1
    return n


# ===----------------------------------------------------------------------=== #
# Integers
# ===----------------------------------------------------------------------=== #


struct IntegerShrinker(Movable):
    """Shrinks a non-negative integer towards zero. Guaranteed to try `0`,
    `1`, `n - 1` and `n - 2`."""

    var current: UInt128
    var seen: Set[UInt128]

    def __init__(out self, initial: UInt128):
        self.current = initial
        self.seen = Set[UInt128]()
        self.seen.add(initial)

    def consider[
        P: def(UInt128) raises -> Bool
    ](mut self, v: UInt128, pred: P) raises -> Bool:
        if v == self.current:
            return True
        if v in self.seen:
            return False
        self.seen.add(v)
        if not (v < self.current):
            return False
        if pred(v):
            self.current = v
            return True
        return False

    def run[P: def(UInt128) raises -> Bool](mut self, pred: P) raises:
        # short_circuit
        for i in range(2):
            if self.consider(UInt128(i), pred):
                return
        self.mask_high_bits(pred)
        var size = _bit_length(self.current)
        if size > 8:
            _ = self.consider(self.current >> UInt128(size - 8), pred)
            _ = self.consider(self.current & 0xFF, pred)
        if self.current == 2:
            return
        # run_step
        self.shift_right(pred)
        self.shrink_by_multiples(2, pred)
        self.shrink_by_multiples(1, pred)

    def mask_high_bits[
        P: def(UInt128) raises -> Bool
    ](mut self, pred: P) raises:
        var base = self.current
        var n = _bit_length(base)

        def try_mask(k: Int) raises {mut self, pred, base, n} -> Bool:
            if k >= n:
                return False
            var mask = (UInt128(1) << UInt128(n - k)) - 1
            return self.consider(mask & base, pred)

        _ = find_integer(try_mask)

    def shift_right[P: def(UInt128) raises -> Bool](mut self, pred: P) raises:
        var base = self.current

        def try_shift(k: Int) raises {mut self, pred, base} -> Bool:
            if k > _bit_length(self.current) or k >= 128:
                return False
            return self.consider(base >> UInt128(k), pred)

        _ = find_integer(try_shift)

    def shrink_by_multiples[
        P: def(UInt128) raises -> Bool
    ](mut self, k: Int, pred: P) raises:
        var base = self.current

        def shrunk(n: Int) raises {mut self, pred, base, k} -> Bool:
            var d = UInt128(n) * UInt128(k)
            if d > base:
                return False
            return self.consider(base - d, pred)

        _ = find_integer(shrunk)


def shrink_integer[
    P: def(UInt128) raises -> Bool
](initial: UInt128, pred: P) raises -> UInt128:
    """Shrink the non-negative integer `initial` subject to `pred`."""
    var s = IntegerShrinker(initial)
    s.run(pred)
    return s.current


# ===----------------------------------------------------------------------=== #
# Floats
# ===----------------------------------------------------------------------=== #


struct FloatShrinker(Movable):
    """Shrinks a non-negative float in the lex order of `float_to_lex`:
    towards integers, then fractions with small denominators."""

    var current: Float64
    var seen: Set[UInt64]

    def __init__(out self, initial: Float64):
        self.current = initial
        self.seen = Set[UInt64]()
        self.seen.add(float_to_int(initial))

    def consider[
        P: def(Float64) raises -> Bool
    ](mut self, v: Float64, pred: P) raises -> Bool:
        var key = float_to_int(v)
        if key == float_to_int(self.current):
            return True
        if key in self.seen:
            return False
        self.seen.add(key)
        if v < 0:
            return False
        if not (float_to_lex(v) < float_to_lex(self.current)):
            return False
        if pred(v):
            self.current = v
            return True
        return False

    def run[P: def(Float64) raises -> Bool](mut self, pred: P) raises:
        # short_circuit
        for g in [FLOAT_MAX, pos_inf(), float_nan()]:
            _ = self.consider(g, pred)
        if isnan(self.current) or isinf(self.current):
            return
        # run_step (non-full: one step)
        if self.current > MAX_PRECISE_INTEGER:
            # delegate to integer shrinking of the float's position
            var start = _float_to_position(self.current)

            def via_position(n: UInt128) raises {mut self, pred} -> Bool:
                return self.consider(_position_to_float(n), pred)

            _ = shrink_integer(start, via_position)
            return
        for p in range(10):
            var scale = Float64(1 << p)
            var scaled = self.current * scale
            _ = self.consider(floor(scaled) / scale, pred)
            _ = self.consider(ceil(scaled) / scale, pred)
        if self.consider(floor(self.current), pred):
            var start = UInt128(Int(self.current))

            def as_integer(n: UInt128) raises {mut self, pred} -> Bool:
                return self.consider(Float64(n), pred)

            _ = shrink_integer(start, as_integer)
            return
        # shrink the integer part, keeping the fractional part
        var whole = floor(self.current)
        var frac = self.current - whole

        def integer_part(n: UInt128) raises {mut self, pred, frac} -> Bool:
            return self.consider(Float64(n) + frac, pred)

        _ = shrink_integer(UInt128(Int(whole)), integer_part)


def _float_to_position(f: Float64) -> UInt128:
    if f <= MAX_PRECISE_INTEGER:
        return UInt128(Int(f))
    return UInt128(Int(MAX_PRECISE_INTEGER)) + UInt128(
        float_to_int(f) - float_to_int(MAX_PRECISE_INTEGER)
    )


def _position_to_float(n: UInt128) -> Float64:
    var boundary = UInt128(Int(MAX_PRECISE_INTEGER))
    if n <= boundary:
        return Float64(n)
    var bits = UInt128(float_to_int(MAX_PRECISE_INTEGER)) + (n - boundary)
    if bits > UInt128(float_to_int(FLOAT_MAX)):
        return pos_inf()
    return int_to_float(UInt64(bits))


def shrink_float[
    P: def(Float64) raises -> Bool
](initial: Float64, pred: P) raises -> Float64:
    """Shrink the non-negative float `initial` subject to `pred`."""
    var s = FloatShrinker(initial)
    s.run(pred)
    return s.current


# ===----------------------------------------------------------------------=== #
# Orderings
# ===----------------------------------------------------------------------=== #


def _keys_less(a: List[Int], b: List[Int], keys: List[Int]) -> Bool:
    for i in range(len(a)):
        var ka = keys[a[i]]
        var kb = keys[b[i]]
        if ka != kb:
            return ka < kb
    return False


def _sorted_by_key(items: List[Int], keys: List[Int]) -> List[Int]:
    var out = items.copy()
    for i in range(1, len(out)):
        var j = i
        while j > 0 and keys[out[j - 1]] > keys[out[j]]:
            out.swap_elements(j, j - 1)
            j -= 1
    return out^


struct OrderingShrinker(Movable):
    """Tries to make a sequence of items more sorted by key, without
    changing its contents. Items are integer ids; `keys[id]` orders them."""

    var current: List[Int]
    var keys: List[Int]
    var seen: Set[List[Int]]

    def __init__(out self, var initial: List[Int], var keys: List[Int]):
        self.current = initial^
        self.keys = keys^
        self.seen = Set[List[Int]]()
        self.seen.add(self.current.copy())

    def consider[
        P: def(List[Int]) raises -> Bool
    ](mut self, v: List[Int], pred: P) raises -> Bool:
        if v == self.current:
            return True
        if v in self.seen:
            return False
        self.seen.add(v.copy())
        if not _keys_less(v, self.current, self.keys):
            return False
        if pred(v):
            self.current = v.copy()
            return True
        return False

    def run[P: def(List[Int]) raises -> Bool](mut self, pred: P) raises:
        if self.consider(_sorted_by_key(self.current, self.keys), pred):
            return
        self.sort_regions(pred)
        self.sort_regions_with_gaps(pred)

    def sort_regions[
        P: def(List[Int]) raises -> Bool
    ](mut self, pred: P) raises:
        var i = 0
        while i + 1 < len(self.current):

            def try_sort(k: Int) raises {mut self, pred, i} -> Bool:
                if i + k > len(self.current):
                    return False
                var region = List[Int]()
                for j in range(i, i + k):
                    region.append(self.current[j])
                var sorted_region = _sorted_by_key(region, self.keys)
                var attempt = List[Int]()
                for j in range(i):
                    attempt.append(self.current[j])
                for x in sorted_region:
                    attempt.append(x)
                for j in range(i + k, len(self.current)):
                    attempt.append(self.current[j])
                return self.consider(attempt, pred)

            var k = find_integer(try_sort)
            i += max(k, 1)

    def sort_regions_with_gaps[
        P: def(List[Int]) raises -> Bool
    ](mut self, pred: P) raises:
        for i in range(1, len(self.current) - 1):
            if i + 1 >= len(self.current):
                break
            var a0 = self.keys[self.current[i - 1]]
            var a1 = self.keys[self.current[i]]
            var a2 = self.keys[self.current[i + 1]]
            if a0 <= a1 and a1 <= a2:
                continue

            def can_sort(a: Int, b: Int) raises {mut self, pred, i} -> Bool:
                if a < 0 or b > len(self.current):
                    return False
                var split = i - a
                var vals = List[Int]()
                for j in range(a, i):
                    vals.append(self.current[j])
                for j in range(i + 1, b):
                    vals.append(self.current[j])
                vals = _sorted_by_key(vals, self.keys)
                var attempt = List[Int]()
                for j in range(a):
                    attempt.append(self.current[j])
                for j in range(split):
                    attempt.append(vals[j])
                attempt.append(self.current[i])
                for j in range(split, len(vals)):
                    attempt.append(vals[j])
                for j in range(b, len(self.current)):
                    attempt.append(self.current[j])
                return self.consider(attempt, pred)

            var left = i
            var right = i + 1

            def grow_right(k: Int) raises {mut can_sort, left, right} -> Bool:
                return can_sort(left, right + k)

            right += find_integer(grow_right)

            def grow_left(k: Int) raises {mut can_sort, left, right} -> Bool:
                return can_sort(left - k, right)

            _ = find_integer(grow_left)


def shrink_ordering[
    P: def(List[Int]) raises -> Bool
](var initial: List[Int], var keys: List[Int], pred: P) raises -> List[Int]:
    """Reorder `initial` (item ids) towards ascending `keys[id]`."""
    var s = OrderingShrinker(initial^, keys^)
    s.run(pred)
    return s.current.copy()


# ===----------------------------------------------------------------------=== #
# Collections
# ===----------------------------------------------------------------------=== #


def _collection_less(a: List[Int], b: List[Int]) -> Bool:
    if len(a) != len(b):
        return len(a) < len(b)
    for i in range(len(a)):
        if a[i] != b[i]:
            return a[i] < b[i]
    return False


struct CollectionShrinker(Movable):
    """Shrinks a sequence of element orders (shortlex): deletes elements,
    sorts them, then shrinks duplicated and individual elements."""

    var current: List[Int]
    var min_size: Int
    var seen: Set[List[Int]]

    def __init__(out self, var initial: List[Int], min_size: Int):
        self.current = initial^
        self.min_size = min_size
        self.seen = Set[List[Int]]()
        self.seen.add(self.current.copy())

    def consider[
        P: def(List[Int]) raises -> Bool
    ](mut self, v: List[Int], pred: P) raises -> Bool:
        if v == self.current:
            return True
        if v in self.seen:
            return False
        self.seen.add(v.copy())
        if not _collection_less(v, self.current):
            return False
        if pred(v):
            self.current = v.copy()
            return True
        return False

    def run[P: def(List[Int]) raises -> Bool](mut self, pred: P) raises:
        # short_circuit: the minimal collection
        if self.consider(List[Int](length=self.min_size, fill=0), pred):
            return
        # all elements zero
        _ = self.consider(List[Int](length=len(self.current), fill=0), pred)
        # delete runs of elements, right to left
        var i = len(self.current) - 1
        while i >= 0:
            var base = self.current.copy()

            def delete_k(k: Int) raises {mut self, pred, base, i} -> Bool:
                if k > i + 1:
                    return False
                var attempt = List[Int]()
                for j in range(i - k + 1):
                    attempt.append(base[j])
                for j in range(i + 1, len(base)):
                    attempt.append(base[j])
                return self.consider(attempt, pred)

            i -= max(find_integer(delete_k), 1)
        # sort
        var n = len(self.current)
        var ids = List[Int]()
        for j in range(n):
            ids.append(j)
        var snapshot = self.current.copy()

        def reorder(perm: List[Int]) raises {mut self, pred, snapshot} -> Bool:
            if len(snapshot) != len(self.current):
                return False
            var attempt = List[Int]()
            for p in perm:
                attempt.append(snapshot[p])
            return self.consider(attempt, pred)

        _ = shrink_ordering(ids^, snapshot.copy(), reorder)
        # shrink duplicated elements together
        var dups = List[Int]()
        for a in range(len(self.current)):
            for b in range(a + 1, len(self.current)):
                if self.current[a] == self.current[b]:
                    var v = self.current[a]
                    var found = False
                    for d in dups:
                        if d == v:
                            found = True
                    if not found:
                        dups.append(v)
        for val in dups:

            def replace_all(n: UInt128) raises {mut self, pred, val} -> Bool:
                var attempt = self.current.copy()
                for j in range(len(attempt)):
                    if attempt[j] == val:
                        attempt[j] = Int(n)
                return self.consider(attempt, pred)

            _ = shrink_integer(UInt128(val), replace_all)
        # shrink each element
        for j in range(len(self.current)):
            if j >= len(self.current):
                break

            def replace_one(n: UInt128) raises {mut self, pred, j} -> Bool:
                if j >= len(self.current):
                    return False
                var attempt = self.current.copy()
                attempt[j] = Int(n)
                return self.consider(attempt, pred)

            _ = shrink_integer(UInt128(self.current[j]), replace_one)


def shrink_collection[
    P: def(List[Int]) raises -> Bool
](var initial: List[Int], min_size: Int, pred: P) raises -> List[Int]:
    """Shrink a sequence of element orders subject to `pred`."""
    var s = CollectionShrinker(initial^, min_size)
    s.run(pred)
    return s.current.copy()
