# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Constraint types: wrappers whose type says which values to generate.

Borrowed from QuickCheck's modifiers (`Positive`, `NonEmptyList`,
`SortedList`, `Blind`, ...); Hypothesis has no equivalent. Each wrapper
implements `Arbitrary`, so `check`, `from_type` and struct fields pick
the constraint up from the type alone:

```mojo
def prop(xs: NonEmpty[List[Int]], i: NonNegative[Int]) -> Bool:
    return xs.value[i.value % len(xs.value)] in xs.value
check(prop)
```

The wrapped value is `.value`. Reports print the value itself (or
`<hidden>` for `Blind`). The constraint survives shrinking without any
extra work: every shrunk value is drawn again through the same strategy.

| Type | Values |
|---|---|
| `Bounded[lo, hi, T = Int]` | `lo <= value <= hi` |
| `Positive[T]` | `value > 0` (floats: finite) |
| `NonNegative[T]` | `value >= 0` (floats: finite) |
| `NonZero[T]` | `value != 0` (floats: finite, not NaN) |
| `NonEmpty[T]` | `len(value) >= 1`, for `List`, `String`, `Set`, `Dict` |
| `Sorted[List[T]]` | a list in ascending order |
| `Blind[T]` | any `T`, printed as `<hidden>` |
| `Via[f]` | whatever `f(data)` draws |

The numeric constraints take integer scalars (`Int`, `UInt8`, ...),
`Float64` and `Float32`.
"""

from std.collections import Set, Dict
from std.hash.hasher import default_hasher
from std.iter import downcast

from proptest.internal.data import ConjectureData
from proptest.strategies.strategy import Drawable, format_value
from proptest.strategies.core import (
    integers_of,
    floats,
    floats32,
    lists,
    sets,
    dictionaries,
    text,
    filter,
)
from proptest.strategies.types import Arbitrary, FromType, draw_from_type


# ===----------------------------------------------------------------------=== #
# Numbers
# ===----------------------------------------------------------------------=== #

comptime _POSITIVE = 0
comptime _NON_NEGATIVE = 1
comptime _NON_ZERO = 2

comptime _NUMERIC_ONLY = (
    "this constraint needs a numeric scalar type (Int, UInt8, Float64, ...)"
)


def _draw_between[
    dtype: DType, lo: Int, hi: Int
](mut data: ConjectureData) raises -> Scalar[dtype]:
    comptime assert lo <= hi, "Bounded[lo, hi]: lo > hi"
    comptime if dtype == DType.float64:
        return rebind_var[Scalar[dtype]](
            data.draw(floats(Float64(lo), Float64(hi)))
        )
    elif dtype == DType.float32:
        return rebind_var[Scalar[dtype]](
            data.draw(floats32(Float64(lo), Float64(hi)))
        )
    else:
        comptime assert dtype.is_integral(), _NUMERIC_ONLY
        comptime assert Int128(lo) >= Int128(Scalar[dtype].MIN) and Int128(
            hi
        ) <= Int128(Scalar[dtype].MAX), "Bounded[lo, hi]: outside the type"
        return data.draw(
            integers_of[dtype](Scalar[dtype](lo), Scalar[dtype](hi))
        )


def _nonzero[dtype: DType](x: Scalar[dtype]) raises -> Bool:
    return x != 0


def _draw_signed[
    dtype: DType, kind: Int
](mut data: ConjectureData) raises -> Scalar[dtype]:
    comptime if dtype == DType.float64:
        comptime if kind == _POSITIVE:
            var s = floats(0.0, allow_infinity=False, exclude_min=True)
            return rebind_var[Scalar[dtype]](data.draw(s))
        elif kind == _NON_NEGATIVE:
            var s = floats(0.0, allow_infinity=False)
            return rebind_var[Scalar[dtype]](data.draw(s))
        else:
            var s = floats(allow_nan=False, allow_infinity=False)
            return rebind_var[Scalar[dtype]](
                data.draw(filter(s^, _nonzero[DType.float64]))
            )
    elif dtype == DType.float32:
        comptime F32_SMALLEST = 1.401298464324817e-45
        comptime if kind == _POSITIVE:
            var s = floats32(F32_SMALLEST, allow_infinity=False)
            return rebind_var[Scalar[dtype]](data.draw(s))
        elif kind == _NON_NEGATIVE:
            var s = floats32(0.0, allow_infinity=False)
            return rebind_var[Scalar[dtype]](data.draw(s))
        else:
            var s = floats32(allow_nan=False, allow_infinity=False)
            return rebind_var[Scalar[dtype]](
                data.draw(filter(s^, _nonzero[DType.float32]))
            )
    else:
        comptime assert dtype.is_integral(), _NUMERIC_ONLY
        comptime if kind == _POSITIVE:
            return data.draw(integers_of[dtype](Scalar[dtype](1)))
        elif kind == _NON_NEGATIVE:
            return data.draw(integers_of[dtype](Scalar[dtype](0)))
        else:
            return data.draw(filter(integers_of[dtype](), _nonzero[dtype]))


trait _Numeric:
    """Numeric scalars, for the numeric constraint types."""

    @staticmethod
    def draw_between[
        Out: Movable & Deinitable, lo: Int, hi: Int
    ](mut data: ConjectureData) raises -> Out:
        ...

    @staticmethod
    def draw_signed[
        Out: Movable & Deinitable, kind: Int
    ](mut data: ConjectureData) raises -> Out:
        ...


__extension SIMD(_Numeric):
    @staticmethod
    def draw_between[
        Out: Movable & Deinitable, lo: Int, hi: Int
    ](mut data: ConjectureData) raises -> Out:
        comptime assert Self.length == 1, "constraint types need a scalar"
        return rebind_var[Out](_draw_between[Self.dtype, lo, hi](data))

    @staticmethod
    def draw_signed[
        Out: Movable & Deinitable, kind: Int
    ](mut data: ConjectureData) raises -> Out:
        comptime assert Self.length == 1, "constraint types need a scalar"
        return rebind_var[Out](_draw_signed[Self.dtype, kind](data))


struct Bounded[lo: Int, hi: Int, T: Drawable = Int](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A `T` in `[lo, hi]` (bounds converted to `T`)."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        comptime assert conforms_to(Self.T, _Numeric), _NUMERIC_ONLY
        return Self(
            downcast[Self.T, _Numeric].draw_between[Self.T, Self.lo, Self.hi](
                data
            )
        )

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))


struct Positive[T: Drawable](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A `T` greater than zero. Floats are also finite."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        comptime assert conforms_to(Self.T, _Numeric), _NUMERIC_ONLY
        return Self(
            downcast[Self.T, _Numeric].draw_signed[Self.T, _POSITIVE](data)
        )

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))


struct NonNegative[T: Drawable](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A `T` that is at least zero. Floats are also finite."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        comptime assert conforms_to(Self.T, _Numeric), _NUMERIC_ONLY
        return Self(
            downcast[Self.T, _Numeric].draw_signed[Self.T, _NON_NEGATIVE](data)
        )

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))


struct NonZero[T: Drawable](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A `T` other than zero (safe to divide by). Floats are also finite."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        comptime assert conforms_to(Self.T, _Numeric), _NUMERIC_ONLY
        return Self(
            downcast[Self.T, _Numeric].draw_signed[Self.T, _NON_ZERO](data)
        )

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))


# ===----------------------------------------------------------------------=== #
# Collections
# ===----------------------------------------------------------------------=== #


trait _Collection:
    """Collections with a length, for `NonEmpty`."""

    @staticmethod
    def draw_non_empty[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        ...


trait _Sortable:
    """Lists, for `Sorted`."""

    @staticmethod
    def draw_sorted[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        ...


comptime _Of[T: AnyType] = FromType[downcast[T, Drawable]]


__extension List(_Collection, _Sortable):
    @staticmethod
    def draw_non_empty[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        return rebind_var[Out](data.draw(lists(_Of[Self.T](), min_size=1)))

    @staticmethod
    def draw_sorted[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime assert conforms_to(
            Self.T, Comparable
        ), "Sorted[List[T]]: T must be Comparable"
        comptime assert conforms_to(
            Self.T, Copyable
        ), "Sorted[List[T]]: T must be Copyable"
        comptime E = downcast[Self.T, Drawable & Comparable & Copyable]
        var xs: List[E] = data.draw(lists(FromType[E]()))
        sort(xs)
        return rebind_var[Out](xs^)


__extension String(_Collection):
    @staticmethod
    def draw_non_empty[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        return rebind_var[Out](data.draw(text(min_size=1)))


__extension Set(_Collection):
    @staticmethod
    def draw_non_empty[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime assert (
            Self.H == default_hasher
        ), "NonEmpty: only Sets with the default hasher are supported"
        comptime E = downcast[Self.T, Drawable & KeyElement & Copyable]
        return rebind_var[Out](data.draw(sets(FromType[E](), min_size=1)))


__extension Dict(_Collection):
    @staticmethod
    def draw_non_empty[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime assert (
            Self.H == default_hasher
        ), "NonEmpty: only Dicts with the default hasher are supported"
        comptime K = downcast[Self.K, Drawable & KeyElement & Copyable]
        return rebind_var[Out](
            data.draw(dictionaries(FromType[K](), _Of[Self.V](), min_size=1))
        )


struct NonEmpty[T: Drawable](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A `List`, `String`, `Set` or `Dict` with at least one element."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        comptime assert conforms_to(
            Self.T, _Collection
        ), "NonEmpty[T]: T must be a List, String, Set or Dict"
        return Self(downcast[Self.T, _Collection].draw_non_empty[Self.T](data))

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))


struct Sorted[T: Drawable](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A `List[E]` in ascending order, for `Comparable` `E`. NaN has no
    place in that order, so for floats use `Via` to leave it out."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        comptime assert conforms_to(
            Self.T, _Sortable
        ), "Sorted[T]: T must be a List"
        return Self(downcast[Self.T, _Sortable].draw_sorted[Self.T](data))

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))


# ===----------------------------------------------------------------------=== #
# Presentation and custom draws
# ===----------------------------------------------------------------------=== #


struct Blind[T: Drawable](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """Any `T`, printed as `<hidden>` in reports (for values whose printed
    form is huge or meaningless)."""

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        return Self(draw_from_type[Self.T](data))

    def write_to(self, mut writer: Some[Writer]):
        writer.write("<hidden>")


struct Via[T: Drawable, //, f: def(mut ConjectureData) raises thin -> T](
    Arbitrary, Copyable where conforms_to(T, Copyable), Writable
):
    """A value drawn by `f`, so any strategy can be named in a type.

    For example:

    ```mojo
    def digits(mut data: ConjectureData) raises -> List[Int]:
        return data.draw(lists(integers(0, 9), max_size=4))

    def prop(xs: Via[digits]) -> Bool:
        return len(xs.value) <= 4
    ```

    `f` must be a top-level (non-capturing) function.
    """

    var value: Self.T

    def __init__(out self, var value: Self.T):
        self.value = value^

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        return Self(Self.f(data))

    def write_to(self, mut writer: Some[Writer]):
        writer.write(format_value(self.value))
