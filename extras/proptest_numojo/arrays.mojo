# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""`arrays`, `array_shapes` and `from_dtype` for NuMojo's `NDArray`.

Port of the core of `hypothesis.extra.numpy`. Differences: every element
is drawn (Hypothesis draws only some and fills the rest with a fill value,
which is faster for large arrays), arrays are always C-contiguous, and the
dtype is a compile-time parameter rather than a strategy.
"""

import numojo as nm
from numojo.prelude import *

from proptest import (
    ConjectureData,
    Strategy,
    BoxedStrategy,
    Drawable,
    boxed,
    integers,
    integers_of,
    floats,
    floats32,
    booleans,
    map,
    lists,
)
from proptest.internal.data import calc_label_from_name, combine_labels


# ===----------------------------------------------------------------------=== #
# dtypes
# ===----------------------------------------------------------------------=== #


def _f32_to[dtype: DType](x: Float32) -> Scalar[dtype]:
    return Scalar[dtype](x)


def _bool_to[dtype: DType](b: Bool) -> Scalar[dtype]:
    return Scalar[dtype](b)


def from_dtype[dtype: DType]() raises -> BoxedStrategy[Scalar[dtype]]:
    """Scalars of `dtype`, over the dtype's whole range (Hypothesis's
    `from_dtype`): integers of every width, `float16`/`float32`/`float64`
    (including NaN and infinities) and `bool`."""
    comptime if dtype.is_integral():
        return boxed(integers_of[dtype]())
    elif dtype == DType.float64:
        return rebind_var[BoxedStrategy[Scalar[dtype]]](boxed(floats()))
    elif dtype == DType.float32 or dtype == DType.float16:
        # draw as float32 (float16 values round from it)
        return boxed(map(floats32(), _f32_to[dtype]))
    elif dtype == DType.bool:
        return boxed(map(booleans(), _bool_to[dtype]))
    else:
        comptime assert False, "from_dtype: unsupported dtype"


# ===----------------------------------------------------------------------=== #
# shapes
# ===----------------------------------------------------------------------=== #


struct ArrayShapes(Copyable, Strategy):
    """Array shapes; see `array_shapes()`."""

    comptime Value = List[Int]
    var min_dims: Int
    var max_dims: Int
    var min_side: Int
    var max_side: Int

    def __init__(
        out self, min_dims: Int, max_dims: Int, min_side: Int, max_side: Int
    ):
        self.min_dims = min_dims
        self.max_dims = max_dims
        self.min_side = min_side
        self.max_side = max_side

    def do_draw(self, mut data: ConjectureData) raises -> List[Int]:
        return data.draw(
            lists(
                integers(self.min_side, self.max_side),
                min_size=self.min_dims,
                max_size=self.max_dims,
            )
        )


def array_shapes(
    *,
    min_dims: Int = 1,
    max_dims: Optional[Int] = None,
    min_side: Int = 1,
    max_side: Optional[Int] = None,
) raises -> ArrayShapes:
    """Shapes with `min_dims` to `max_dims` dimensions (default
    `min_dims + 2`), each of length `min_side` to `max_side` (default
    `min_side + 5`), as in Hypothesis. Shrinks towards fewer, shorter
    dimensions."""
    var hi_dims = max_dims.value() if max_dims else min_dims + 2
    var hi_side = max_side.value() if max_side else min_side + 5
    if min_dims < 0 or hi_dims < min_dims or min_side < 0 or hi_side < min_side:
        raise Error("InvalidArgument: array_shapes: bad bounds")
    if hi_dims > 32:
        raise Error("InvalidArgument: array_shapes: at most 32 dimensions")
    return ArrayShapes(min_dims, hi_dims, min_side, hi_side)


# ===----------------------------------------------------------------------=== #
# arrays
# ===----------------------------------------------------------------------=== #


struct Arrays[dtype: DType, Sh: Strategy & Copyable, E: Strategy & Copyable](
    Copyable, Strategy
):
    """Arrays of a dtype; see `arrays()`."""

    comptime Value = NDArray[Self.dtype]
    var shape: Self.Sh
    var elements: Self.E
    var unique: Bool

    def __init__(
        out self, var shape: Self.Sh, var elements: Self.E, unique: Bool
    ):
        self.shape = shape^
        self.elements = elements^
        self.unique = unique

    def label(self) -> UInt64:
        return combine_labels(
            calc_label_from_name("numojo.arrays"), self.elements.label()
        )

    def do_draw(self, mut data: ConjectureData) raises -> NDArray[Self.dtype]:
        var shape = rebind_var[List[Int]](data.draw(self.shape))
        var a = nm.zeros[Self.dtype](shape)
        var seen_hashes = List[Scalar[Self.dtype]]()
        for i in range(a.size):
            var v = rebind_var[Scalar[Self.dtype]](data.draw(self.elements))
            if self.unique:
                # retry a few times, then give up on this example
                var tries = 0
                while _contains(seen_hashes, v):
                    tries += 1
                    if tries > 10:
                        data.mark_invalid(
                            "could not draw unique array elements"
                        )
                    v = rebind_var[Scalar[Self.dtype]](data.draw(self.elements))
                seen_hashes.append(v)
            a.unsafe_set(i, v)
        return a^


def _contains[dtype: DType](xs: List[Scalar[dtype]], v: Scalar[dtype]) -> Bool:
    for x in xs:
        if x == v:
            return True
    return False


struct _JustShape(Copyable, Strategy):
    comptime Value = List[Int]
    var shape: List[Int]

    def __init__(out self, var shape: List[Int]):
        self.shape = shape^

    def do_draw(self, mut data: ConjectureData) raises -> List[Int]:
        return self.shape.copy()


def arrays[
    dtype: DType
](var shape: List[Int], *, unique: Bool = False) raises -> Arrays[
    dtype, _JustShape, BoxedStrategy[Scalar[dtype]]
]:
    """Arrays of `dtype` with a fixed `shape`, elements from `from_dtype`."""
    return Arrays[dtype, _JustShape, BoxedStrategy[Scalar[dtype]]](
        _JustShape(shape^), from_dtype[dtype](), unique
    )


def arrays[
    dtype: DType, E: Strategy & Copyable
](
    var shape: List[Int], var elements: E, *, unique: Bool = False
) raises -> Arrays[dtype, _JustShape, E]:
    """Arrays of `dtype` with a fixed `shape`, elements drawn from
    `elements` (whose values must be `Scalar[dtype]`)."""
    comptime assert (
        E.Value == Scalar[dtype]
    ), "elements must produce Scalar[dtype]"
    return Arrays[dtype, _JustShape, E](_JustShape(shape^), elements^, unique)


def arrays[
    dtype: DType
](var shape: ArrayShapes, *, unique: Bool = False) raises -> Arrays[
    dtype, ArrayShapes, BoxedStrategy[Scalar[dtype]]
]:
    """Arrays of `dtype` with shapes drawn from `shape`."""
    return Arrays[dtype, ArrayShapes, BoxedStrategy[Scalar[dtype]]](
        shape^, from_dtype[dtype](), unique
    )


def arrays[
    dtype: DType, E: Strategy & Copyable
](
    var shape: ArrayShapes, var elements: E, *, unique: Bool = False
) raises -> Arrays[dtype, ArrayShapes, E]:
    """Arrays of `dtype` with shapes drawn from `shape` and elements from
    `elements` (whose values must be `Scalar[dtype]`)."""
    comptime assert (
        E.Value == Scalar[dtype]
    ), "elements must produce Scalar[dtype]"
    return Arrays[dtype, ArrayShapes, E](shape^, elements^, unique)
