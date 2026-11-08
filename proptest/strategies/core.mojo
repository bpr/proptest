# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The core strategies: numbers, booleans, strings, collections and the
combinators that build new strategies out of old ones.

Port of `hypothesis.strategies` (`numbers.py`, `collections.py`,
`strings.py`, `misc.py`, `strategies.py`, `core.py`, `recursive.py`,
`flatmapped.py`).
"""

from std.memory import ArcPointer
from std.memory.alloc import unsafe_alloc
from std.collections import Dict, Set
from std.math import isnan, isinf

from std.reflection import call_location, SourceLocation

from proptest.internal.data import (
    ConjectureData,
    ErasedValue,
    calc_label_from_name,
    combine_labels,
    FILTER_LABEL,
    ONE_OF_LABEL,
    UNIQUE_LABEL,
)
from proptest.internal.choice import COLLECTION_DEFAULT_MAX_SIZE
from proptest.internal.floats import (
    next_up,
    next_down,
    pos_inf,
    neg_inf,
    smallest_subnormal,
    FLOAT_MAX,
    FLOAT_MIN_NORMAL,
    is_negative,
)
from proptest.internal.intervals import (
    IntervalSet,
    codepoints_to_string,
    MAX_CODEPOINT,
)
from proptest.strategies.strategy import Strategy, Drawable, Many, draw
from proptest.internal.charmap import as_general_categories, category_intervals


# ===----------------------------------------------------------------------=== #
# Integers
# ===----------------------------------------------------------------------=== #


struct Integers(Copyable, Strategy):
    """Integers (`Int`) in `[min_value, max_value]`; see `integers()`."""

    comptime Value = Int
    var min_value: Int
    var max_value: Int

    def __init__(out self, min_value: Int, max_value: Int):
        self.min_value = min_value
        self.max_value = max_value

    def do_draw(self, mut data: ConjectureData) raises -> Int:
        return Int(
            data.draw_integer(Int128(self.min_value), Int128(self.max_value))
        )


def integers(
    min_value: Optional[Int] = None, max_value: Optional[Int] = None
) raises -> Integers:
    """Integers between `min_value` and `max_value` inclusive. Omitted bounds
    are the limits of `Int`. Shrinks towards zero (or the bound nearest zero).
    """
    var lo = min_value.value() if min_value else Int.MIN
    var hi = max_value.value() if max_value else Int.MAX
    if lo > hi:
        raise Error(
            String(
                "InvalidArgument: integers(min_value=",
                lo,
                ", max_value=",
                hi,
                "): min_value > max_value",
            )
        )
    return Integers(lo, hi)


struct ScalarIntegers[dtype: DType](Copyable, Strategy):
    """Integers of a fixed-width integral `dtype`; see `integers_of()`."""

    comptime Value = Scalar[Self.dtype]
    var min_value: Int128
    var max_value: Int128

    def __init__(out self, min_value: Int128, max_value: Int128):
        self.min_value = min_value
        self.max_value = max_value

    def do_draw(self, mut data: ConjectureData) raises -> Scalar[Self.dtype]:
        var v = data.draw_integer(self.min_value, self.max_value)
        return Scalar[Self.dtype](v)


def integers_of[
    dtype: DType
](
    min_value: Optional[Scalar[dtype]] = None,
    max_value: Optional[Scalar[dtype]] = None,
) raises -> ScalarIntegers[dtype]:
    """Integers of type `Scalar[dtype]` (e.g. `UInt8`, `Int32`, `UInt64`),
    defaulting to the full range of the type."""
    comptime assert dtype.is_integral(), "integers_of needs an integer dtype"
    var lo = Int128(min_value.value()) if min_value else Int128(
        Scalar[dtype].MIN
    )
    var hi = Int128(max_value.value()) if max_value else Int128(
        Scalar[dtype].MAX
    )
    if lo > hi:
        raise Error("InvalidArgument: integers_of: min_value > max_value")
    return ScalarIntegers[dtype](lo, hi)


# ===----------------------------------------------------------------------=== #
# Booleans
# ===----------------------------------------------------------------------=== #


struct Booleans(Copyable, Strategy):
    """`True` or `False`, shrinking to `False`."""

    comptime Value = Bool

    def __init__(out self):
        pass

    def do_draw(self, mut data: ConjectureData) raises -> Bool:
        return data.draw_boolean(0.5)


def booleans() -> Booleans:
    """Booleans, shrinking towards `False`."""
    return Booleans()


# ===----------------------------------------------------------------------=== #
# Floats
# ===----------------------------------------------------------------------=== #


struct Floats(Copyable, Strategy):
    """Floats; see `floats()`."""

    comptime Value = Float64
    var min_value: Float64
    var max_value: Float64
    var allow_nan: Bool
    var smallest_nonzero_magnitude: Float64

    def __init__(
        out self,
        min_value: Float64,
        max_value: Float64,
        allow_nan: Bool,
        smallest_nonzero_magnitude: Float64,
    ):
        self.min_value = min_value
        self.max_value = max_value
        self.allow_nan = allow_nan
        self.smallest_nonzero_magnitude = smallest_nonzero_magnitude

    def do_draw(self, mut data: ConjectureData) raises -> Float64:
        return data.draw_float(
            self.min_value,
            self.max_value,
            allow_nan=self.allow_nan,
            smallest_nonzero_magnitude=self.smallest_nonzero_magnitude,
        )


def floats(
    min_value: Optional[Float64] = None,
    max_value: Optional[Float64] = None,
    *,
    allow_nan: Optional[Bool] = None,
    allow_infinity: Optional[Bool] = None,
    allow_subnormal: Bool = True,
    exclude_min: Bool = False,
    exclude_max: Bool = False,
) raises -> Floats:
    """Floats between `min_value` and `max_value`.

    As in Hypothesis: NaN is allowed only when neither bound is given (by
    default), infinities only when a side is unbounded, and shrinking
    prefers integers, then simple fractions, then everything else.
    """
    var nan_ok = allow_nan.value() if allow_nan else (
        not min_value and not max_value
    )
    if nan_ok and (min_value or max_value):
        raise Error("InvalidArgument: cannot have allow_nan=True with bounds")
    var inf_ok = allow_infinity.value() if allow_infinity else (
        not min_value or not max_value
    )
    var lo = min_value.value() if min_value else neg_inf()
    var hi = max_value.value() if max_value else pos_inf()
    if isnan(lo) or isnan(hi):
        raise Error("InvalidArgument: NaN bound for floats()")
    if exclude_min:
        if not min_value:
            raise Error("InvalidArgument: exclude_min needs a min_value")
        lo = next_up(lo)
    if exclude_max:
        if not max_value:
            raise Error("InvalidArgument: exclude_max needs a max_value")
        hi = next_down(hi)
    if not inf_ok:
        if isinf(lo) and lo < 0:
            lo = -FLOAT_MAX
        if isinf(hi) and hi > 0:
            hi = FLOAT_MAX
        if isinf(lo) or isinf(hi):
            raise Error(
                "InvalidArgument: infinite bound with allow_infinity=False"
            )
    if lo > hi:
        raise Error("InvalidArgument: floats(): min_value > max_value")
    var smallest = smallest_subnormal() if allow_subnormal else FLOAT_MIN_NORMAL
    return Floats(lo, hi, nan_ok, smallest)


struct Floats32(Copyable, Strategy):
    """`Float32` values; see `floats32()`."""

    comptime Value = Float32
    var inner: Floats

    def __init__(out self, var inner: Floats):
        self.inner = inner^

    def do_draw(self, mut data: ConjectureData) raises -> Float32:
        var f = self.inner.do_draw(data)
        var g = Float32(f)
        # rounding to 32 bits can step outside the requested bounds
        if Float64(g) < self.inner.min_value:
            g = Float32(next_up(self.inner.min_value))
        if Float64(g) > self.inner.max_value:
            g = Float32(next_down(self.inner.max_value))
        return g


def floats32(
    min_value: Optional[Float64] = None,
    max_value: Optional[Float64] = None,
    *,
    allow_nan: Optional[Bool] = None,
    allow_infinity: Optional[Bool] = None,
) raises -> Floats32:
    """`Float32` floats (Hypothesis's `floats(width=32)`)."""
    comptime F32_MAX = 3.4028234663852886e38
    var lo = min_value.value() if min_value else -F32_MAX
    var hi = max_value.value() if max_value else F32_MAX
    var inf_ok = allow_infinity.value() if allow_infinity else (
        not min_value or not max_value
    )
    var nan_ok = allow_nan.value() if allow_nan else (
        not min_value and not max_value
    )
    var f = Floats(lo, hi, nan_ok, 1.401298464324817e-45)
    if inf_ok:
        if not min_value:
            f.min_value = neg_inf()
        if not max_value:
            f.max_value = pos_inf()
    return Floats32(f^)


# ===----------------------------------------------------------------------=== #
# Constants and sampling
# ===----------------------------------------------------------------------=== #


struct Just[T: Copyable & Drawable](Copyable, Strategy):
    """Always the same value; see `just()`."""

    comptime Value = Self.T
    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        return self.value.copy()


def just[T: Copyable & Drawable](var value: T) -> Just[T]:
    """Always `value` (no choices are made)."""
    return Just[T](value^)


struct LazyJust[T: Drawable, F: def() raises -> T](
    Copyable where conforms_to(F, Copyable), Strategy
):
    """A fresh `f()` on every draw; see `lazy_just()`."""

    comptime Value = Self.T
    var f: Self.F

    def __init__(out self, var f: Self.F):
        self.f = f^

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        return self.f()


def lazy_just[
    T: Drawable, //, F: def() raises -> T
](var f: F) -> LazyJust[T, F]:
    """The value `f()`, made afresh for every test case (no choices are
    made). Like `just`, for values that can't or shouldn't be copied, such
    as unique handles (Rust proptest's `LazyJust`)."""
    return LazyJust[T, F](f^)


struct SampledFrom[T: Copyable & Drawable](Copyable, Strategy):
    """One of a fixed list of values; see `sampled_from()`."""

    comptime Value = Self.T
    var elements: List[Self.T]
    var weights: Optional[ArcPointer[List[Float64]]]

    def __init__(
        out self,
        var elements: List[Self.T],
        var weights: Optional[ArcPointer[List[Float64]]] = None,
    ):
        self.elements = elements^
        self.weights = weights^

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        var i = data.draw_integer(
            Int128(0), Int128(len(self.elements) - 1), weights=self.weights
        )
        return self.elements[Int(i)].copy()


def sampled_from[
    T: Copyable & Drawable
](var elements: List[T]) raises -> SampledFrom[T]:
    """One of `elements`, shrinking towards the first."""
    if len(elements) == 0:
        raise Error(
            "InvalidArgument: sampled_from() needs at least one element"
        )
    return SampledFrom[T](elements^)


def sampled_from[
    T: Copyable & Drawable
](var elements: List[T], *, weights: List[Int]) raises -> SampledFrom[T]:
    """One of `elements`, each chosen in proportion to its (positive)
    weight (RapidCheck's `weightedElement`). Still shrinks towards the
    first element."""
    if len(elements) == 0:
        raise Error(
            "InvalidArgument: sampled_from() needs at least one element"
        )
    var ws = _normalize_weights(
        weights, len(elements), "sampled_from", "elements"
    )
    return SampledFrom[T](elements^, ws^)


# ===----------------------------------------------------------------------=== #
# Type erasure
# ===----------------------------------------------------------------------=== #

comptime _ErasedPtr = MutOpaquePointer[MutUntrackedOrigin]


struct BoxedStrategy[T: Drawable](Copyable, Strategy):
    """A strategy for `T` whose concrete type has been erased.

    Lets strategies of different types but the same `Value` be stored
    together (as in `one_of`) or passed around without spelling out their
    (often long) types. Copying a box deep-copies the strategy inside.
    """

    comptime Value = Self.T
    var _ptr: _ErasedPtr
    var _draw: def(_ErasedPtr, mut ConjectureData) thin raises -> Self.T
    var _clone: def(_ErasedPtr) thin -> _ErasedPtr
    var _free: def(_ErasedPtr) thin
    var _label: UInt64

    def __init__[S: Strategy & Copyable](out self, var strategy: S):
        def draw_(p: _ErasedPtr, mut data: ConjectureData) raises -> Self.T:
            return rebind_var[Self.T](draw(data, p.unsafe_bitcast[S]()[]))

        def clone_(p: _ErasedPtr) -> _ErasedPtr:
            var q = unsafe_alloc[S](1)
            q.unsafe_write(p.unsafe_bitcast[S]()[].copy())
            return q.unsafe_bitcast[NoneType]()

        def free_(p: _ErasedPtr):
            var q = p.unsafe_bitcast[S]()
            _ = q.unsafe_take_pointee()
            q.unsafe_free()

        self._label = strategy.label()
        var q = unsafe_alloc[S](1)
        q.unsafe_write(strategy^)
        self._ptr = q.unsafe_bitcast[NoneType]()
        self._draw = draw_
        self._clone = clone_
        self._free = free_

    def __init__(out self, *, copy: Self):
        self._ptr = copy._clone(copy._ptr)
        self._draw = copy._draw
        self._clone = copy._clone
        self._free = copy._free
        self._label = copy._label

    def __deinit__(deinit self):
        self._free(self._ptr)

    def label(self) -> UInt64:
        return self._label

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        # The inner strategy's own span is opened by `draw_`.
        return self._draw(self._ptr, data)


def boxed[S: Strategy & Copyable](var strategy: S) -> BoxedStrategy[S.Value]:
    """Erase the concrete type of `strategy`."""
    return BoxedStrategy[S.Value](strategy^)


# ===----------------------------------------------------------------------=== #
# one_of
# ===----------------------------------------------------------------------=== #


def _normalize_weights(
    weights: List[Int],
    n: Int,
    name: String = "one_of",
    what: String = "strategies",
) raises -> ArcPointer[List[Float64]]:
    """`weights` as probabilities, checking there is one positive weight for
    each of `n` alternatives (`name` and `what` are for the messages)."""
    if len(weights) != n:
        raise Error(
            String(
                "InvalidArgument: ",
                name,
                "() got ",
                len(weights),
                " weights for ",
                n,
                " ",
                what,
            )
        )
    var total = 0
    for w in weights:
        if w <= 0:
            raise Error(
                String("InvalidArgument: ", name, "() weights must be positive")
            )
        total += w
    var p = List[Float64](capacity=n)
    for w in weights:
        p.append(Float64(w) / Float64(total))
    return ArcPointer(p^)


struct Alternatives[*Ss: Strategy](
    Copyable where Ss.all_conforms_to[Copyable](), Strategy
):
    """A choice between a fixed number of strategies, stored unboxed; see
    `one_of()`. Every alternative must produce the same type."""

    comptime Value = Self.Ss[0].Value
    var strategies: Tuple[*Self.Ss]
    var weights: Optional[ArcPointer[List[Float64]]]

    def __init__(
        out self,
        var strategies: Tuple[*Self.Ss],
        var weights: Optional[ArcPointer[List[Float64]]] = None,
    ):
        comptime for i in range(len(Self.Ss)):
            comptime assert (
                Self.Ss[i].Value == Self.Ss[0].Value
            ), "one_of: every strategy must produce the same type"
        self.strategies = strategies^
        self.weights = weights^

    def label(self) -> UInt64:
        var l = ONE_OF_LABEL
        comptime for i in range(len(Self.Ss)):
            l = combine_labels(l, self.strategies[i].label())
        return l

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        comptime n = len(Self.Ss)
        var k = Int(
            data.draw_integer(Int128(0), Int128(n - 1), weights=self.weights)
        )
        comptime for i in range(n):
            if i == k:
                return rebind_var[Self.Value](draw(data, self.strategies[i]))
        raise Error("unreachable")


def one_of[
    S1: Strategy, S2: Strategy
](var s1: S1, var s2: S2) -> Alternatives[S1, S2]:
    """A value from `s1` or `s2` (which must produce the same type),
    shrinking towards `s1`. Takes two to six strategies; a list of
    `BoxedStrategy` takes any number."""
    return Alternatives[S1, S2](Tuple(s1^, s2^))


def one_of[
    S1: Strategy, S2: Strategy
](var s1: S1, var s2: S2, *, weights: List[Int]) raises -> Alternatives[S1, S2]:
    """Like `one_of(s1, s2)`, choosing each strategy in proportion to its
    (positive) weight. Still shrinks towards `s1`."""
    return Alternatives[S1, S2](Tuple(s1^, s2^), _normalize_weights(weights, 2))


def one_of[
    S1: Strategy, S2: Strategy, S3: Strategy
](var s1: S1, var s2: S2, var s3: S3) -> Alternatives[S1, S2, S3]:
    """A value from one of three strategies, shrinking towards the first."""
    return Alternatives[S1, S2, S3](Tuple(s1^, s2^, s3^))


def one_of[
    S1: Strategy, S2: Strategy, S3: Strategy
](
    var s1: S1, var s2: S2, var s3: S3, *, weights: List[Int]
) raises -> Alternatives[S1, S2, S3]:
    """Weighted `one_of` of three strategies."""
    return Alternatives[S1, S2, S3](
        Tuple(s1^, s2^, s3^), _normalize_weights(weights, 3)
    )


def one_of[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy
](var s1: S1, var s2: S2, var s3: S3, var s4: S4) -> Alternatives[
    S1, S2, S3, S4
]:
    """A value from one of four strategies, shrinking towards the first."""
    return Alternatives[S1, S2, S3, S4](Tuple(s1^, s2^, s3^, s4^))


def one_of[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy
](
    var s1: S1, var s2: S2, var s3: S3, var s4: S4, *, weights: List[Int]
) raises -> Alternatives[S1, S2, S3, S4]:
    """Weighted `one_of` of four strategies."""
    return Alternatives[S1, S2, S3, S4](
        Tuple(s1^, s2^, s3^, s4^), _normalize_weights(weights, 4)
    )


def one_of[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy, S5: Strategy
](var s1: S1, var s2: S2, var s3: S3, var s4: S4, var s5: S5) -> Alternatives[
    S1, S2, S3, S4, S5
]:
    """A value from one of five strategies, shrinking towards the first."""
    return Alternatives[S1, S2, S3, S4, S5](Tuple(s1^, s2^, s3^, s4^, s5^))


def one_of[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy, S5: Strategy
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var s4: S4,
    var s5: S5,
    *,
    weights: List[Int],
) raises -> Alternatives[S1, S2, S3, S4, S5]:
    """Weighted `one_of` of five strategies."""
    return Alternatives[S1, S2, S3, S4, S5](
        Tuple(s1^, s2^, s3^, s4^, s5^), _normalize_weights(weights, 5)
    )


def one_of[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
](
    var s1: S1, var s2: S2, var s3: S3, var s4: S4, var s5: S5, var s6: S6
) -> Alternatives[S1, S2, S3, S4, S5, S6]:
    """A value from one of six strategies, shrinking towards the first."""
    return Alternatives[S1, S2, S3, S4, S5, S6](
        Tuple(s1^, s2^, s3^, s4^, s5^, s6^)
    )


def one_of[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var s4: S4,
    var s5: S5,
    var s6: S6,
    *,
    weights: List[Int],
) raises -> Alternatives[S1, S2, S3, S4, S5, S6]:
    """Weighted `one_of` of six strategies."""
    return Alternatives[S1, S2, S3, S4, S5, S6](
        Tuple(s1^, s2^, s3^, s4^, s5^, s6^), _normalize_weights(weights, 6)
    )


struct OneOf[T: Drawable](Copyable, Strategy):
    """A choice between any number of boxed strategies; see `one_of()`."""

    comptime Value = Self.T
    var strategies: List[BoxedStrategy[Self.T]]
    var weights: Optional[ArcPointer[List[Float64]]]

    def __init__(
        out self,
        var strategies: List[BoxedStrategy[Self.T]],
        var weights: Optional[ArcPointer[List[Float64]]] = None,
    ):
        self.strategies = strategies^
        self.weights = weights^

    def label(self) -> UInt64:
        var l = ONE_OF_LABEL
        for s in self.strategies:
            l = combine_labels(l, s.label())
        return l

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        var i = data.draw_integer(
            Int128(0), Int128(len(self.strategies) - 1), weights=self.weights
        )
        return draw(data, self.strategies[Int(i)])


def one_of[
    T: Drawable
](var strategies: List[BoxedStrategy[T]]) raises -> OneOf[T]:
    """A value from any of `strategies`, shrinking towards the first."""
    if len(strategies) == 0:
        raise Error("InvalidArgument: one_of() needs at least one strategy")
    return OneOf[T](strategies^)


def one_of[
    T: Drawable
](
    var strategies: List[BoxedStrategy[T]], *, weights: List[Int]
) raises -> OneOf[T]:
    """Like `one_of(strategies)`, choosing each strategy in proportion to
    its (positive) weight."""
    if len(strategies) == 0:
        raise Error("InvalidArgument: one_of() needs at least one strategy")
    var w = _normalize_weights(weights, len(strategies))
    return OneOf[T](strategies^, w^)


# ===----------------------------------------------------------------------=== #
# map / filter / flatmap
# ===----------------------------------------------------------------------=== #


struct Mapped[S: Strategy, R: Drawable, F: def(S.Value) raises -> R](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """`f(x)` for `x` drawn from a strategy; see `map()`."""

    comptime Value = Self.R
    var inner: Self.S
    var f: Self.F

    def __init__(out self, var inner: Self.S, var f: Self.F):
        self.inner = inner^
        self.f = f^

    def label(self) -> UInt64:
        return combine_labels(calc_label_from_name("map"), self.inner.label())

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        return self.f(draw(data, self.inner))


def map[
    S: Strategy, R: Drawable, //, F: def(S.Value) raises -> R
](var strategy: S, var f: F) -> Mapped[S, R, F]:
    """Values `f(x)` for `x` drawn from `strategy` (Hypothesis's
    `strategy.map(f)`). Shrinking happens on `x`."""
    return Mapped[S, R, F](strategy^, f^)


# ===----------------------------------------------------------------------=== #
# apply(s1, ..., sN, f): a function of N arguments over N strategies
# ===----------------------------------------------------------------------=== #


struct Applied2[
    S1: Strategy,
    S2: Strategy,
    R: Drawable,
    F: def(S1.Value, S2.Value) raises -> R,
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(F, Copyable)
    ),
    Strategy,
):
    """`f(a1, ...)` with each argument drawn from its strategy; see
    `apply()`."""

    comptime Value = Self.R
    var s1: Self.S1
    var s2: Self.S2
    var f: Self.F

    def __init__(out self, var f: Self.F, var s1: Self.S1, var s2: Self.S2):
        self.f = f^
        self.s1 = s1^
        self.s2 = s2^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("apply"),
            combine_labels(self.s1.label(), self.s2.label()),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        var a1 = draw(data, self.s1)
        var a2 = draw(data, self.s2)
        return self.f(a1, a2)


def apply[
    S1: Strategy,
    S2: Strategy,
    R: Drawable,
    //,
    F: def(S1.Value, S2.Value) raises -> R,
](var s1: S1, var s2: S2, var f: F) -> Applied2[S1, S2, R, F]:
    """Values `f(a, b)` with `a` from `s1` and `b` from `s2` (RapidCheck's
    `gen::apply`; Hypothesis's `builds` with a function). Shrinking
    happens on the arguments."""
    return Applied2[S1, S2, R, F](f^, s1^, s2^)


struct Applied3[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    R: Drawable,
    F: def(S1.Value, S2.Value, S3.Value) raises -> R,
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(F, Copyable)
    ),
    Strategy,
):
    """`f(a1, ...)` with each argument drawn from its strategy; see
    `apply()`."""

    comptime Value = Self.R
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var f: Self.F

    def __init__(
        out self,
        var f: Self.F,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
    ):
        self.f = f^
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("apply"),
            combine_labels(
                combine_labels(self.s1.label(), self.s2.label()),
                self.s3.label(),
            ),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        var a1 = draw(data, self.s1)
        var a2 = draw(data, self.s2)
        var a3 = draw(data, self.s3)
        return self.f(a1, a2, a3)


def apply[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    R: Drawable,
    //,
    F: def(S1.Value, S2.Value, S3.Value) raises -> R,
](var s1: S1, var s2: S2, var s3: S3, var f: F) -> Applied3[S1, S2, S3, R, F]:
    """`f` applied to values drawn from three strategies (RapidCheck's
    `gen::apply`; Hypothesis's `builds` with a function). Shrinking
    happens on the arguments."""
    return Applied3[S1, S2, S3, R, F](f^, s1^, s2^, s3^)


struct Applied4[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    R: Drawable,
    F: def(S1.Value, S2.Value, S3.Value, S4.Value) raises -> R,
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(S4, Copyable)
        and conforms_to(F, Copyable)
    ),
    Strategy,
):
    """`f(a1, ...)` with each argument drawn from its strategy; see
    `apply()`."""

    comptime Value = Self.R
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var s4: Self.S4
    var f: Self.F

    def __init__(
        out self,
        var f: Self.F,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
        var s4: Self.S4,
    ):
        self.f = f^
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^
        self.s4 = s4^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("apply"),
            combine_labels(
                combine_labels(
                    combine_labels(self.s1.label(), self.s2.label()),
                    self.s3.label(),
                ),
                self.s4.label(),
            ),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        var a1 = draw(data, self.s1)
        var a2 = draw(data, self.s2)
        var a3 = draw(data, self.s3)
        var a4 = draw(data, self.s4)
        return self.f(a1, a2, a3, a4)


def apply[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    R: Drawable,
    //,
    F: def(S1.Value, S2.Value, S3.Value, S4.Value) raises -> R,
](var s1: S1, var s2: S2, var s3: S3, var s4: S4, var f: F) -> Applied4[
    S1, S2, S3, S4, R, F
]:
    """`f` applied to values drawn from four strategies (RapidCheck's
    `gen::apply`; Hypothesis's `builds` with a function). Shrinking
    happens on the arguments."""
    return Applied4[S1, S2, S3, S4, R, F](f^, s1^, s2^, s3^, s4^)


struct Applied5[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    R: Drawable,
    F: def(S1.Value, S2.Value, S3.Value, S4.Value, S5.Value) raises -> R,
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(S4, Copyable)
        and conforms_to(S5, Copyable)
        and conforms_to(F, Copyable)
    ),
    Strategy,
):
    """`f(a1, ...)` with each argument drawn from its strategy; see
    `apply()`."""

    comptime Value = Self.R
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var s4: Self.S4
    var s5: Self.S5
    var f: Self.F

    def __init__(
        out self,
        var f: Self.F,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
        var s4: Self.S4,
        var s5: Self.S5,
    ):
        self.f = f^
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^
        self.s4 = s4^
        self.s5 = s5^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("apply"),
            combine_labels(
                combine_labels(
                    combine_labels(
                        combine_labels(self.s1.label(), self.s2.label()),
                        self.s3.label(),
                    ),
                    self.s4.label(),
                ),
                self.s5.label(),
            ),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        var a1 = draw(data, self.s1)
        var a2 = draw(data, self.s2)
        var a3 = draw(data, self.s3)
        var a4 = draw(data, self.s4)
        var a5 = draw(data, self.s5)
        return self.f(a1, a2, a3, a4, a5)


def apply[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    R: Drawable,
    //,
    F: def(S1.Value, S2.Value, S3.Value, S4.Value, S5.Value) raises -> R,
](
    var s1: S1, var s2: S2, var s3: S3, var s4: S4, var s5: S5, var f: F
) -> Applied5[S1, S2, S3, S4, S5, R, F]:
    """`f` applied to values drawn from five strategies (RapidCheck's
    `gen::apply`; Hypothesis's `builds` with a function). Shrinking
    happens on the arguments."""
    return Applied5[S1, S2, S3, S4, S5, R, F](f^, s1^, s2^, s3^, s4^, s5^)


struct Applied6[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
    R: Drawable,
    F: def(
        S1.Value, S2.Value, S3.Value, S4.Value, S5.Value, S6.Value
    ) raises -> R,
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(S4, Copyable)
        and conforms_to(S5, Copyable)
        and conforms_to(S6, Copyable)
        and conforms_to(F, Copyable)
    ),
    Strategy,
):
    """`f(a1, ...)` with each argument drawn from its strategy; see
    `apply()`."""

    comptime Value = Self.R
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var s4: Self.S4
    var s5: Self.S5
    var s6: Self.S6
    var f: Self.F

    def __init__(
        out self,
        var f: Self.F,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
        var s4: Self.S4,
        var s5: Self.S5,
        var s6: Self.S6,
    ):
        self.f = f^
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^
        self.s4 = s4^
        self.s5 = s5^
        self.s6 = s6^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("apply"),
            combine_labels(
                combine_labels(
                    combine_labels(
                        combine_labels(
                            combine_labels(self.s1.label(), self.s2.label()),
                            self.s3.label(),
                        ),
                        self.s4.label(),
                    ),
                    self.s5.label(),
                ),
                self.s6.label(),
            ),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        var a1 = draw(data, self.s1)
        var a2 = draw(data, self.s2)
        var a3 = draw(data, self.s3)
        var a4 = draw(data, self.s4)
        var a5 = draw(data, self.s5)
        var a6 = draw(data, self.s6)
        return self.f(a1, a2, a3, a4, a5, a6)


def apply[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
    R: Drawable,
    //,
    F: def(
        S1.Value, S2.Value, S3.Value, S4.Value, S5.Value, S6.Value
    ) raises -> R,
](
    var s1: S1,
    var s2: S2,
    var s3: S3,
    var s4: S4,
    var s5: S5,
    var s6: S6,
    var f: F,
) -> Applied6[S1, S2, S3, S4, S5, S6, R, F]:
    """`f` applied to values drawn from six strategies (RapidCheck's
    `gen::apply`; Hypothesis's `builds` with a function). Shrinking
    happens on the arguments."""
    return Applied6[S1, S2, S3, S4, S5, S6, R, F](
        f^, s1^, s2^, s3^, s4^, s5^, s6^
    )


struct Filtered[S: Strategy, F: def(S.Value) raises -> Bool](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """Values from a strategy satisfying a predicate; see `filter()`."""

    comptime Value = Self.S.Value
    var inner: Self.S
    var predicate: Self.F
    var reason: String

    def __init__(
        out self, var inner: Self.S, var predicate: Self.F, reason: String = ""
    ):
        self.inner = inner^
        self.predicate = predicate^
        self.reason = reason

    def label(self) -> UInt64:
        return combine_labels(FILTER_LABEL, self.inner.label())

    def do_draw(self, mut data: ConjectureData) raises -> Self.S.Value:
        for _ in range(3):
            data.start_span(FILTER_LABEL)
            var v = draw(data, self.inner)
            if self.predicate(v):
                data.stop_span()
                return v^
            data.stop_span(discard=True)
        data.mark_invalid(
            self.reason if self.reason.byte_length()
            > 0 else "filter rejected three draws"
        )
        raise Error("unreachable")


def filter[
    S: Strategy, //, F: def(S.Value) raises -> Bool
](var strategy: S, var predicate: F, *, reason: String = "") -> Filtered[S, F]:
    """Values from `strategy` for which `predicate` holds (Hypothesis's
    `strategy.filter(predicate)`). Prefer constructing values that satisfy
    the condition: each test case gives up after three rejections.

    `reason` names the condition in the `filter_too_much` health check and
    in run statistics (Rust proptest's `prop_filter(whence, f)`)."""
    return Filtered[S, F](strategy^, predicate^, reason)


struct FilterMapped[
    S: Strategy, R: Drawable, F: def(S.Value) raises -> Optional[R]
](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """Values from a strategy, transformed where possible; see
    `filter_map()`."""

    comptime Value = Self.R
    var inner: Self.S
    var f: Self.F
    var reason: String

    def __init__(out self, var inner: Self.S, var f: Self.F, reason: String):
        self.inner = inner^
        self.f = f^
        self.reason = reason

    def label(self) -> UInt64:
        return combine_labels(FILTER_LABEL, self.inner.label())

    def do_draw(self, mut data: ConjectureData) raises -> Self.R:
        for _ in range(3):
            data.start_span(FILTER_LABEL)
            var v = draw(data, self.inner)
            var r = self.f(v)
            if r:
                data.stop_span()
                return r.take()
            data.stop_span(discard=True)
        data.mark_invalid(
            self.reason if self.reason.byte_length()
            > 0 else "filter_map rejected three draws"
        )
        raise Error("unreachable")


def filter_map[
    S: Strategy, R: Drawable, //, F: def(S.Value) raises -> Optional[R]
](var strategy: S, var f: F, *, reason: String = "") -> FilterMapped[S, R, F]:
    """`f(x)` for values `x` from `strategy`, skipping those where `f`
    returns `None` (Rust proptest's `prop_filter_map`): a `filter` and a
    `map` in one step, for when checking and converting are the same work.
    Each test case gives up after three rejections."""
    return FilterMapped[S, R, F](strategy^, f^, reason)


struct Covered[S: Strategy, F: def(S.Value) raises -> Bool](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """Values from a strategy, with a coverage requirement; see `cover()`."""

    comptime Value = Self.S.Value
    var inner: Self.S
    var percent: Float64
    var label_: String
    var condition: Self.F

    def __init__(
        out self,
        var inner: Self.S,
        percent: Float64,
        label: String,
        var condition: Self.F,
    ):
        self.inner = inner^
        self.percent = percent
        self.label_ = label
        self.condition = condition^

    def label(self) -> UInt64:
        return self.inner.label()

    def do_draw(self, mut data: ConjectureData) raises -> Self.S.Value:
        var v = self.inner.do_draw(data)
        data.cover(self.percent, self.condition(v), self.label_)
        return v^


def cover[
    S: Strategy, //, F: def(S.Value) raises -> Bool
](
    var strategy: S, percent: Float64, label: String, var condition: F
) -> Covered[S, F]:
    """Values from `strategy`, requiring that `condition` holds for at
    least `percent`% of passing test cases (QuickCheck's `cover`, attached
    to a strategy so that `given` and `check` tests can use it). See
    `ConjectureData.cover` for what happens when it doesn't."""
    return Covered[S, F](strategy^, percent, label, condition^)


struct Tabulated[S: Strategy, F: def(S.Value) raises -> String](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """Values from a strategy, tabulated; see `tabulate()`."""

    comptime Value = Self.S.Value
    var inner: Self.S
    var table: String
    var key: Self.F

    def __init__(out self, var inner: Self.S, table: String, var key: Self.F):
        self.inner = inner^
        self.table = table
        self.key = key^

    def label(self) -> UInt64:
        return self.inner.label()

    def do_draw(self, mut data: ConjectureData) raises -> Self.S.Value:
        var v = self.inner.do_draw(data)
        data.tabulate(self.table, self.key(v))
        return v^


def tabulate[
    S: Strategy, //, F: def(S.Value) raises -> String
](var strategy: S, table: String, var key: F) -> Tabulated[S, F]:
    """Values from `strategy`, recording `key(value)` in the table `table`
    of the run's statistics (QuickCheck's `tabulate`)."""
    return Tabulated[S, F](strategy^, table, key^)


struct FlatMapped[S: Strategy, S2: Strategy, F: def(S.Value) raises -> S2](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """Values from `f(x)` for `x` drawn from a strategy; see `flatmap()`."""

    comptime Value = Self.S2.Value
    var inner: Self.S
    var f: Self.F

    def __init__(out self, var inner: Self.S, var f: Self.F):
        self.inner = inner^
        self.f = f^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("flatmap"), self.inner.label()
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.S2.Value:
        var x = draw(data, self.inner)
        var s2 = self.f(x)
        return draw(data, s2)


def flatmap[
    S: Strategy, S2: Strategy, //, F: def(S.Value) raises -> S2
](var strategy: S, var f: F) -> FlatMapped[S, S2, F]:
    """Draw `x` from `strategy`, then a value from the strategy `f(x)`
    (Hypothesis's `strategy.flatmap(f)`)."""
    return FlatMapped[S, S2, F](strategy^, f^)


# ===----------------------------------------------------------------------=== #
# Composite and interactive draws
# ===----------------------------------------------------------------------=== #


struct Composite[T: Drawable, F: def(mut ConjectureData) raises -> T](
    Copyable where conforms_to(F, Copyable), Strategy
):
    """A strategy defined by a drawing function; see `composite()`."""

    comptime Value = Self.T
    var f: Self.F

    def __init__(out self, var f: Self.F):
        self.f = f^

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        return self.f(data)


def composite[
    T: Drawable, //, F: def(mut ConjectureData) raises -> T
](var f: F) -> Composite[T, F]:
    """A strategy from a function that draws from other strategies with
    `data.draw(...)` (Hypothesis's `@composite`).

    For example:

    ```mojo
    def sorted_pair(mut data: ConjectureData) raises -> Tuple[Int, Int]:
        var a = data.draw(integers(0, 100))
        var b = data.draw(integers(a, 100))
        return (a, b)

    var pairs = composite(sorted_pair)
    ```
    """
    return Composite[T, F](f^)


# ===----------------------------------------------------------------------=== #
# Collections
# ===----------------------------------------------------------------------=== #


struct Lists[S: Strategy](Copyable where conforms_to(S, Copyable), Strategy):
    """Lists of values from a strategy; see `lists()`."""

    comptime Value = List[Self.S.Value]
    var elements: Self.S
    var min_size: Int
    var max_size: Int

    def __init__(out self, var elements: Self.S, min_size: Int, max_size: Int):
        self.elements = elements^
        self.min_size = min_size
        self.max_size = max_size

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("lists"), self.elements.label()
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var result = Self.Value()
        var many = Many(self.min_size, self.max_size)
        while many.more(data):
            result.append(draw(data, self.elements))
        return result^


def _check_sizes(min_size: Int, max_size: Optional[Int]) raises -> Int:
    var hi = max_size.value() if max_size else COLLECTION_DEFAULT_MAX_SIZE
    if min_size < 0:
        raise Error("InvalidArgument: min_size must be non-negative")
    if hi < min_size:
        raise Error("InvalidArgument: max_size < min_size")
    return hi


def lists[
    S: Strategy
](
    var elements: S, *, min_size: Int = 0, max_size: Optional[Int] = None
) raises -> Lists[S]:
    """Lists of values drawn from `elements`, with length in
    `[min_size, max_size]`. Shrinks by deleting elements, then shrinking
    the remaining ones."""
    var hi = _check_sizes(min_size, max_size)
    return Lists[S](elements^, min_size, hi)


struct UniqueLists[
    S: Strategy, K: KeyElement & Deinitable, F: def(S.Value) raises -> K
](
    Copyable where conforms_to(S, Copyable) and conforms_to(F, Copyable),
    Strategy,
):
    """Lists whose elements have distinct keys; see `unique_lists()`."""

    comptime Value = List[Self.S.Value]
    var elements: Self.S
    var key: Self.F
    var min_size: Int
    var max_size: Int

    def __init__(
        out self,
        var elements: Self.S,
        var key: Self.F,
        min_size: Int,
        max_size: Int,
    ):
        self.elements = elements^
        self.key = key^
        self.min_size = min_size
        self.max_size = max_size

    def label(self) -> UInt64:
        return combine_labels(UNIQUE_LABEL, self.elements.label())

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var result = Self.Value()
        var seen = Set[Self.K]()
        var many = Many(self.min_size, self.max_size)
        while many.more(data):
            var v = draw(data, self.elements)
            var k = self.key(v)
            if k in seen:
                many.reject(data)
            else:
                seen.add(k^)
                result.append(v^)
        return result^


def unique_lists_by[
    S: Strategy, K: KeyElement & Deinitable, //, F: def(S.Value) raises -> K
](
    var elements: S,
    var key: F,
    *,
    min_size: Int = 0,
    max_size: Optional[Int] = None,
) raises -> UniqueLists[S, K, F]:
    """Lists of values from `elements` whose `key(x)` are all distinct
    (Hypothesis's `lists(elements, unique_by=key)`)."""
    var hi = _check_sizes(min_size, max_size)
    return UniqueLists[S, K, F](elements^, key^, min_size, hi)


struct UniqueValues[S: Strategy](
    Copyable where conforms_to(S, Copyable), Strategy
) where conforms_to(S.Value, KeyElement & Copyable):
    """Lists of distinct values; see `unique_lists()`."""

    comptime Value = List[Self.S.Value]
    var elements: Self.S
    var min_size: Int
    var max_size: Int

    def __init__(out self, var elements: Self.S, min_size: Int, max_size: Int):
        self.elements = elements^
        self.min_size = min_size
        self.max_size = max_size

    def label(self) -> UInt64:
        return combine_labels(UNIQUE_LABEL, self.elements.label())

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var result = Self.Value()
        var seen = Set[Self.S.Value]()
        var many = Many(self.min_size, self.max_size)
        while many.more(data):
            var v = draw(data, self.elements)
            if v in seen:
                many.reject(data)
            else:
                seen.add(v.copy())
                result.append(v^)
        return result^


def unique_lists[
    S: Strategy
](
    var elements: S, *, min_size: Int = 0, max_size: Optional[Int] = None
) raises -> UniqueValues[S] where conforms_to(S.Value, KeyElement & Copyable):
    """Lists of distinct values from `elements` (Hypothesis's
    `lists(elements, unique=True)`)."""
    var hi = _check_sizes(min_size, max_size)
    return UniqueValues[S](elements^, min_size, hi)


struct Sets[S: Strategy](
    Copyable where conforms_to(S, Copyable), Strategy
) where conforms_to(S.Value, KeyElement & Copyable):
    """Sets of values from a strategy; see `sets()`."""

    comptime Value = Set[Self.S.Value]
    var inner: UniqueValues[Self.S]

    def __init__(out self, var inner: UniqueValues[Self.S]):
        self.inner = inner^

    def label(self) -> UInt64:
        return self.inner.label()

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var l = self.inner.do_draw(data)
        var s = Self.Value()
        for x in l:
            s.add(x.copy())
        return s^


def sets[
    S: Strategy
](
    var elements: S, *, min_size: Int = 0, max_size: Optional[Int] = None
) raises -> Sets[S] where conforms_to(S.Value, KeyElement & Copyable):
    """Sets of values drawn from `elements`."""
    return Sets[S](
        unique_lists(elements^, min_size=min_size, max_size=max_size)
    )


struct Dictionaries[KS: Strategy, VS: Strategy](
    Copyable where conforms_to(KS, Copyable) and conforms_to(VS, Copyable),
    Strategy,
) where conforms_to(KS.Value, KeyElement & Copyable):
    """Dictionaries; see `dictionaries()`."""

    comptime Value = Dict[Self.KS.Value, Self.VS.Value]
    var keys: Self.KS
    var values: Self.VS
    var min_size: Int
    var max_size: Int

    def __init__(
        out self,
        var keys: Self.KS,
        var values: Self.VS,
        min_size: Int,
        max_size: Int,
    ):
        self.keys = keys^
        self.values = values^
        self.min_size = min_size
        self.max_size = max_size

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("dictionaries"),
            combine_labels(self.keys.label(), self.values.label()),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var result = Self.Value()
        var many = Many(self.min_size, self.max_size)
        while many.more(data):
            var k = draw(data, self.keys)
            if k in result:
                many.reject(data)
                continue
            var v = draw(data, self.values)
            result[k^] = v^
        return result^


def dictionaries[
    KS: Strategy, VS: Strategy
](
    var keys: KS,
    var values: VS,
    *,
    min_size: Int = 0,
    max_size: Optional[Int] = None,
) raises -> Dictionaries[KS, VS] where conforms_to(
    KS.Value, KeyElement & Copyable
):
    """Dictionaries with keys from `keys` and values from `values`."""
    var hi = _check_sizes(min_size, max_size)
    return Dictionaries[KS, VS](keys^, values^, min_size, hi)


struct Optionals[S: Strategy](
    Copyable where conforms_to(S, Copyable), Strategy
):
    """`None` or a value from a strategy; see `optionals()`."""

    comptime Value = Optional[Self.S.Value]
    var inner: Self.S

    def __init__(out self, var inner: Self.S):
        self.inner = inner^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("optionals"), self.inner.label()
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        # one_of(none(), inner): branch 0 is None
        if data.draw_integer(Int128(0), Int128(1)) == 0:
            return None
        return Self.Value(draw(data, self.inner))


def optionals[S: Strategy](var strategy: S) -> Optionals[S]:
    """`None` or a value from `strategy` (Hypothesis's
    `none() | strategy`), shrinking towards `None`."""
    return Optionals[S](strategy^)


struct Permutations[T: Copyable & Drawable](Copyable, Strategy):
    """Permutations of a list; see `permutations()`."""

    comptime Value = List[Self.T]
    var values: List[Self.T]

    def __init__(out self, var values: List[Self.T]):
        self.values = values^

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        # Fisher-Yates, as in Hypothesis: shrinks towards the original order.
        var result = self.values.copy()
        var n = len(result)
        for i in range(n - 1):
            var j = Int(data.draw_integer(Int128(i), Int128(n - 1)))
            if j != i:
                result.swap_elements(i, j)
        return result^


def permutations[
    T: Copyable & Drawable
](var values: List[T]) -> Permutations[T]:
    """Orderings of `values`, shrinking towards the given order."""
    return Permutations[T](values^)


struct Subsequences[T: Copyable & Drawable](Copyable, Strategy):
    """Order-preserving sublists of a list; see `subsequence()`."""

    comptime Value = List[Self.T]
    var values: List[Self.T]
    var min_size: Int
    var max_size: Int

    def __init__(
        out self, var values: List[Self.T], min_size: Int, max_size: Int
    ):
        self.values = values^
        self.min_size = min_size
        self.max_size = max_size

    def label(self) -> UInt64:
        return calc_label_from_name("subsequence")

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var result = Self.Value()
        var n = len(self.values)
        for i in range(n):
            var forced: Optional[Bool] = None
            if len(result) == self.max_size:
                forced = False
            elif n - i <= self.min_size - len(result):
                forced = True
            if data.draw_boolean(0.5, forced=forced):
                result.append(self.values[i].copy())
        return result^


def subsequence[
    T: Copyable & Drawable
](
    var values: List[T], *, min_size: Int = 0, max_size: Optional[Int] = None
) raises -> Subsequences[T]:
    """Sublists of `values` that keep their order, with length in
    `[min_size, max_size]` (Rust proptest's `sample::subsequence`).
    Shrinks by dropping elements, towards the first `min_size` values."""
    var hi = max_size.value() if max_size else len(values)
    if min_size < 0 or min_size > hi or min_size > len(values):
        raise Error(
            "InvalidArgument: subsequence() needs 0 <= min_size <= max_size"
            " and min_size <= len(values)"
        )
    return Subsequences[T](values^, min_size, hi)


# ===----------------------------------------------------------------------=== #
# Tuples
# ===----------------------------------------------------------------------=== #


struct Tuples2[S1: Strategy, S2: Strategy](
    Copyable where conforms_to(S1, Copyable) and conforms_to(S2, Copyable),
    Strategy,
):
    """Pairs; see `tuples()`."""

    comptime Value = Tuple[Self.S1.Value, Self.S2.Value]
    var s1: Self.S1
    var s2: Self.S2

    def __init__(out self, var s1: Self.S1, var s2: Self.S2):
        self.s1 = s1^
        self.s2 = s2^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("tuples"),
            combine_labels(self.s1.label(), self.s2.label()),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var a = draw(data, self.s1)
        var b = draw(data, self.s2)
        return (a^, b^)


struct Tuples3[S1: Strategy, S2: Strategy, S3: Strategy](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
    ),
    Strategy,
):
    """Triples; see `tuples()`."""

    comptime Value = Tuple[Self.S1.Value, Self.S2.Value, Self.S3.Value]
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3

    def __init__(out self, var s1: Self.S1, var s2: Self.S2, var s3: Self.S3):
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("tuples"),
            combine_labels(
                self.s1.label(),
                combine_labels(self.s2.label(), self.s3.label()),
            ),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var a = draw(data, self.s1)
        var b = draw(data, self.s2)
        var c = draw(data, self.s3)
        return (a^, b^, c^)


struct Tuples4[S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(S4, Copyable)
    ),
    Strategy,
):
    """Quadruples; see `tuples()`."""

    comptime Value = Tuple[
        Self.S1.Value, Self.S2.Value, Self.S3.Value, Self.S4.Value
    ]
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var s4: Self.S4

    def __init__(
        out self,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
        var s4: Self.S4,
    ):
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^
        self.s4 = s4^

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("tuples"),
            combine_labels(
                combine_labels(self.s1.label(), self.s2.label()),
                combine_labels(self.s3.label(), self.s4.label()),
            ),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var a = draw(data, self.s1)
        var b = draw(data, self.s2)
        var c = draw(data, self.s3)
        var d = draw(data, self.s4)
        return (a^, b^, c^, d^)


struct Tuples5[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy, S5: Strategy
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(S4, Copyable)
        and conforms_to(S5, Copyable)
    ),
    Strategy,
):
    """5-tuples; see `tuples()`."""

    comptime Value = Tuple[
        Self.S1.Value,
        Self.S2.Value,
        Self.S3.Value,
        Self.S4.Value,
        Self.S5.Value,
    ]
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var s4: Self.S4
    var s5: Self.S5

    def __init__(
        out self,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
        var s4: Self.S4,
        var s5: Self.S5,
    ):
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^
        self.s4 = s4^
        self.s5 = s5^

    def label(self) -> UInt64:
        return combine_labels(
            combine_labels(
                combine_labels(
                    combine_labels(
                        combine_labels(
                            calc_label_from_name("tuples"), self.s1.label()
                        ),
                        self.s2.label(),
                    ),
                    self.s3.label(),
                ),
                self.s4.label(),
            ),
            self.s5.label(),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var v1 = draw(data, self.s1)
        var v2 = draw(data, self.s2)
        var v3 = draw(data, self.s3)
        var v4 = draw(data, self.s4)
        var v5 = draw(data, self.s5)
        return (v1^, v2^, v3^, v4^, v5^)


struct Tuples6[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
](
    Copyable where (
        conforms_to(S1, Copyable)
        and conforms_to(S2, Copyable)
        and conforms_to(S3, Copyable)
        and conforms_to(S4, Copyable)
        and conforms_to(S5, Copyable)
        and conforms_to(S6, Copyable)
    ),
    Strategy,
):
    """6-tuples; see `tuples()`."""

    comptime Value = Tuple[
        Self.S1.Value,
        Self.S2.Value,
        Self.S3.Value,
        Self.S4.Value,
        Self.S5.Value,
        Self.S6.Value,
    ]
    var s1: Self.S1
    var s2: Self.S2
    var s3: Self.S3
    var s4: Self.S4
    var s5: Self.S5
    var s6: Self.S6

    def __init__(
        out self,
        var s1: Self.S1,
        var s2: Self.S2,
        var s3: Self.S3,
        var s4: Self.S4,
        var s5: Self.S5,
        var s6: Self.S6,
    ):
        self.s1 = s1^
        self.s2 = s2^
        self.s3 = s3^
        self.s4 = s4^
        self.s5 = s5^
        self.s6 = s6^

    def label(self) -> UInt64:
        return combine_labels(
            combine_labels(
                combine_labels(
                    combine_labels(
                        combine_labels(
                            combine_labels(
                                calc_label_from_name("tuples"), self.s1.label()
                            ),
                            self.s2.label(),
                        ),
                        self.s3.label(),
                    ),
                    self.s4.label(),
                ),
                self.s5.label(),
            ),
            self.s6.label(),
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var v1 = draw(data, self.s1)
        var v2 = draw(data, self.s2)
        var v3 = draw(data, self.s3)
        var v4 = draw(data, self.s4)
        var v5 = draw(data, self.s5)
        var v6 = draw(data, self.s6)
        return (v1^, v2^, v3^, v4^, v5^, v6^)


def tuples[
    S1: Strategy, S2: Strategy
](var s1: S1, var s2: S2) -> Tuples2[S1, S2]:
    """Pairs `(a, b)` with `a` from `s1` and `b` from `s2`."""
    return Tuples2[S1, S2](s1^, s2^)


def tuples[
    S1: Strategy, S2: Strategy, S3: Strategy
](var s1: S1, var s2: S2, var s3: S3) -> Tuples3[S1, S2, S3]:
    """Triples drawn from three strategies."""
    return Tuples3[S1, S2, S3](s1^, s2^, s3^)


def tuples[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy
](var s1: S1, var s2: S2, var s3: S3, var s4: S4) -> Tuples4[S1, S2, S3, S4]:
    """Quadruples drawn from four strategies."""
    return Tuples4[S1, S2, S3, S4](s1^, s2^, s3^, s4^)


def tuples[
    S1: Strategy, S2: Strategy, S3: Strategy, S4: Strategy, S5: Strategy
](var s1: S1, var s2: S2, var s3: S3, var s4: S4, var s5: S5) -> Tuples5[
    S1, S2, S3, S4, S5
]:
    """5-tuples drawn from 5 strategies."""
    return Tuples5[S1, S2, S3, S4, S5](s1^, s2^, s3^, s4^, s5^)


def tuples[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
](
    var s1: S1, var s2: S2, var s3: S3, var s4: S4, var s5: S5, var s6: S6
) -> Tuples6[S1, S2, S3, S4, S5, S6]:
    """6-tuples drawn from 6 strategies."""
    return Tuples6[S1, S2, S3, S4, S5, S6](s1^, s2^, s3^, s4^, s5^, s6^)


# ===----------------------------------------------------------------------=== #
# shared
# ===----------------------------------------------------------------------=== #


struct Shared[S: Strategy](
    Copyable where conforms_to(S, Copyable), Strategy
) where conforms_to(S.Value, Copyable):
    """One value per test case, shared by every draw with the same key;
    see `shared()`."""

    comptime Value = Self.S.Value
    var base: Self.S
    var key: String

    def __init__(out self, var base: Self.S, key: String):
        self.base = base^
        self.key = key

    def label(self) -> UInt64:
        return combine_labels(calc_label_from_name("shared"), self.base.label())

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        if self.key in data.shared_values:
            return data.shared_values[self.key].get[Self.S.Value]()
        var v = draw(data, self.base)
        data.shared_values[self.key] = ErasedValue(v.copy())
        return v^


@always_inline
def shared[
    S: Strategy
](
    var base: S,
    key: Optional[String] = None,
    *,
    location: Optional[SourceLocation] = None,
) -> Shared[S] where conforms_to(S.Value, Copyable):
    """A strategy that draws a single value from `base` per test case: every
    draw from a `shared` strategy with the same key returns that value.

    Without a key, Hypothesis shares by strategy identity; proptest uses the
    source location of the `shared(...)` call instead, so draws from one
    `var x = shared(...)` (and its copies) share a value, while two separate
    `shared(...)` calls do not. Shrinking works on the underlying `base`.
    """
    var k: String
    if key:
        k = key.value()
    else:
        var loc = location.value() if location else call_location()
        k = String("shared@", loc)
    return Shared[S](base^, k)


# ===----------------------------------------------------------------------=== #
# Strings and bytes
# ===----------------------------------------------------------------------=== #


struct Characters(Copyable, Strategy):
    """Single characters (as one-character `String`s); see `characters()`."""

    comptime Value = String
    var alphabet: ArcPointer[IntervalSet]

    def __init__(out self, var alphabet: IntervalSet):
        self.alphabet = ArcPointer(alphabet^)

    def do_draw(self, mut data: ConjectureData) raises -> String:
        return codepoints_to_string(data.draw_string(self.alphabet, 1, 1))


def _make_alphabet(
    min_codepoint: UInt32,
    max_codepoint: UInt32,
    include_characters: String,
    exclude_characters: String,
    categories: List[String] = [],
    exclude_categories: List[String] = [],
    codec: Optional[String] = None,
) raises -> IntervalSet:
    """Port of the alphabet logic of Hypothesis's `characters()`."""
    if min_codepoint > max_codepoint or max_codepoint > MAX_CODEPOINT:
        raise Error("InvalidArgument: bad codepoint range")
    if len(categories) > 0 and len(exclude_categories) > 0:
        raise Error(
            "InvalidArgument: pass at most one of categories and"
            " exclude_categories"
        )
    var inc = IntervalSet.from_string(include_characters)
    var exc = IntervalSet.from_string(exclude_characters)
    if len(inc.intersection(exc)) > 0:
        raise Error(
            "InvalidArgument: some characters are in both include_characters"
            " and exclude_characters"
        )
    var s = IntervalSet.range(min_codepoint, max_codepoint)
    if len(categories) > 0:
        var cats = as_general_categories(categories)
        s = s.intersection(category_intervals(cats))
    elif len(exclude_categories) > 0:
        var cats = as_general_categories(exclude_categories)
        s = s.difference(category_intervals(cats))
    # Mojo strings are UTF-8, which cannot encode surrogates (category Cs).
    s = s.difference(IntervalSet.range(0xD800, 0xDFFF))
    s = s.union(inc)
    s = s.difference(exc)
    if codec:
        var c = codec.value().lower()
        if c == "ascii":
            s = s.intersection(IntervalSet.range(0, 127))
        elif c == "latin-1" or c == "latin1" or c == "iso-8859-1":
            s = s.intersection(IntervalSet.range(0, 255))
        elif c != "utf-8" and c != "utf8":
            raise Error(
                String(
                    "InvalidArgument: codec ",
                    repr(codec.value()),
                    " is not supported (use 'ascii', 'latin-1' or 'utf-8')",
                )
            )
    return s^


def characters(
    *,
    min_codepoint: UInt32 = 0,
    max_codepoint: UInt32 = MAX_CODEPOINT,
    categories: List[String] = [],
    exclude_categories: List[String] = [],
    include_characters: String = "",
    exclude_characters: String = "",
    codec: Optional[String] = None,
) raises -> Characters:
    """Single Unicode characters (as one-character `String`s).

    As in Hypothesis: codepoints in `[min_codepoint, max_codepoint]`; if
    `categories` is given (e.g. `["Lu", "Nd"]`, or `["L"]` for all letters),
    only characters in those Unicode general categories, and with
    `exclude_categories`, none in those (an empty list means no
    restriction); then `include_characters` are
    added and `exclude_characters` removed, and `codec` (`"ascii"`,
    `"latin-1"` or `"utf-8"`) limits the result to what it can encode.
    Surrogates (category `Cs`) are always excluded, since UTF-8 cannot
    encode them. Shrinks towards `'0'`.
    """
    var s = _make_alphabet(
        min_codepoint,
        max_codepoint,
        include_characters,
        exclude_characters,
        categories,
        exclude_categories,
        codec,
    )
    if len(s) == 0:
        raise Error("InvalidArgument: characters(): empty alphabet")
    return Characters(s^)


struct Text(Copyable, Strategy):
    """Strings; see `text()`."""

    comptime Value = String
    var alphabet: ArcPointer[IntervalSet]
    var min_size: Int
    var max_size: Int

    def __init__(
        out self, var alphabet: IntervalSet, min_size: Int, max_size: Int
    ):
        self.alphabet = ArcPointer(alphabet^)
        self.min_size = min_size
        self.max_size = max_size

    def do_draw(self, mut data: ConjectureData) raises -> String:
        return codepoints_to_string(
            data.draw_string(self.alphabet, self.min_size, self.max_size)
        )


def text(
    alphabet: Optional[String] = None,
    *,
    min_size: Int = 0,
    max_size: Optional[Int] = None,
) raises -> Text:
    """Strings whose length in codepoints is in `[min_size, max_size]`, made
    of the characters in `alphabet` (default: every codepoint except
    surrogates). Shrinks towards shorter strings and towards `'0'`."""
    var hi = _check_sizes(min_size, max_size)
    var a = IntervalSet.from_string(
        alphabet.value()
    ) if alphabet else IntervalSet.default_text()
    if len(a) == 0 and min_size > 0:
        raise Error("InvalidArgument: text(): empty alphabet with min_size > 0")
    return Text(a^, min_size, hi)


def text(
    alphabet: Characters,
    *,
    min_size: Int = 0,
    max_size: Optional[Int] = None,
) raises -> Text:
    """Strings made of the characters `alphabet` can produce."""
    var hi = _check_sizes(min_size, max_size)
    return Text(alphabet.alphabet[].copy(), min_size, hi)


struct Binary(Copyable, Strategy):
    """Byte strings; see `binary()`."""

    comptime Value = List[UInt8]
    var min_size: Int
    var max_size: Int

    def __init__(out self, min_size: Int, max_size: Int):
        self.min_size = min_size
        self.max_size = max_size

    def do_draw(self, mut data: ConjectureData) raises -> List[UInt8]:
        return data.draw_bytes(self.min_size, self.max_size)


def binary(
    *, min_size: Int = 0, max_size: Optional[Int] = None
) raises -> Binary:
    """Byte strings (`List[UInt8]`) with length in `[min_size, max_size]`."""
    var hi = _check_sizes(min_size, max_size)
    return Binary(min_size, hi)


# ===----------------------------------------------------------------------=== #
# Recursion
# ===----------------------------------------------------------------------=== #


struct _LimitedLeaves[T: Drawable](Copyable, Strategy):
    """The base case of a recursive strategy, counting leaves."""

    comptime Value = Self.T
    var base: BoxedStrategy[Self.T]

    def __init__(out self, var base: BoxedStrategy[Self.T]):
        self.base = base^

    def label(self) -> UInt64:
        return self.base.label()

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        var n = len(data.leaf_budgets)
        if n == 0:
            return draw(data, self.base)
        data.leaf_budgets[n - 1] -= 1
        if data.leaf_budgets[n - 1] < 0:
            data.mark_invalid("max_leaves exceeded in recursive()")
        return draw(data, self.base)


struct Recursive[T: Drawable](Copyable, Strategy):
    """Recursive data; see `recursive()`."""

    comptime Value = Self.T
    var strategy: BoxedStrategy[Self.T]
    var max_leaves: Int

    def __init__(
        out self, var strategy: BoxedStrategy[Self.T], max_leaves: Int
    ):
        self.strategy = strategy^
        self.max_leaves = max_leaves

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("recursive"), self.strategy.label()
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        data.leaf_budgets.append(self.max_leaves)
        var v = draw(data, self.strategy)
        _ = data.leaf_budgets.pop()
        return v^


def recursive[
    S: Strategy & Copyable,
    //,
    F: def(BoxedStrategy[S.Value]) raises -> BoxedStrategy[S.Value],
](var base: S, extend: F, *, max_leaves: Int = 100) raises -> Recursive[
    S.Value
]:
    """Recursive data: `base` values, or `extend(s)` where `s` is the
    recursive strategy itself, up to about `max_leaves` base values per
    example (Hypothesis's `recursive`).

    For example, nested lists of integers, rendered as strings:

    ```mojo
    def show(x: Int) -> String:
        return String(x)

    def node(children: List[String]) -> String:
        ...  # "[" + ", ".join(children) + "]"

    def nest(s: BoxedStrategy[String]) raises -> BoxedStrategy[String]:
        return boxed(map(lists(s.copy(), max_size=3), node))

    var trees = recursive(map(integers(), show), nest)
    ```
    """
    var limited = BoxedStrategy[S.Value](
        _LimitedLeaves[S.Value](BoxedStrategy[S.Value](base^))
    )
    var strategies = List[BoxedStrategy[S.Value]]()
    strategies.append(limited.copy())
    strategies.append(extend(limited))
    while (1 << (len(strategies) - 1)) <= max_leaves:
        var current = BoxedStrategy[S.Value](OneOf[S.Value](strategies.copy()))
        strategies.append(extend(current))
    var top = BoxedStrategy[S.Value](OneOf[S.Value](strategies^))
    return Recursive[S.Value](top^, max_leaves)
