# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Shape-broadcasting and indexing strategies for NuMojo.

Port of `broadcastable_shapes`, `mutually_broadcastable_shapes`,
`basic_indices` and `integer_array_indices` from `hypothesis.extra.numpy`
(`hypothesis/extra/_array_helpers.py`).

Differences from Hypothesis:

- `basic_indices` produces a `BasicIndex` (a list of index items) rather
  than a Python tuple; `index.apply(array)` indexes a NuMojo array with it.
  Slices use non-negative bounds and positive steps (integer indices may be
  negative), since that is what NuMojo's slicing documents.
- `mutually_broadcastable_shapes` takes `num_shapes` only (no gufunc
  `signature`).
- `integer_array_indices` returns a `List` of `NDArray[DType.int]`, one per
  dimension; NuMojo's integer-array indexing (`a[indices]`) indexes the
  first dimension only, so use `indices[0]` with it.
"""

from std.builtin.type_aliases import EllipsisType

import numojo as nm
from numojo.prelude import *
from numojo.core.ndarray import IndexTypes
from numojo.core.layout.array_methods import NewAxis

from proptest import (
    ConjectureData,
    Strategy,
    integers,
)
from proptest_numojo.arrays import ArrayShapes, array_shapes

comptime NDIM_MAX = 32


def _broadcast(shapes: List[List[Int]]) raises -> List[Int]:
    """The broadcast of several shapes (NumPy's rules)."""
    var n = 0
    for s in shapes:
        n = max(n, len(s))
    var out = List[Int](length=n, fill=1)
    for s in shapes:
        for i in range(len(s)):
            var d = s[len(s) - 1 - i]
            var j = n - 1 - i
            if out[j] == 1:
                out[j] = d
            elif d != 1 and d != out[j]:
                raise Error("shapes do not broadcast")
    return out^


# ===----------------------------------------------------------------------=== #
# broadcastable_shapes
# ===----------------------------------------------------------------------=== #


struct BroadcastableShapesOf(Copyable, Strategy):
    """Shapes that broadcast with a given shape; see `broadcastable_shapes()`.
    """

    comptime Value = List[Int]
    var shape: List[Int]
    var min_dims: Int
    var max_dims: Int
    var min_side: Int
    var max_side: Int

    def __init__(
        out self,
        var shape: List[Int],
        min_dims: Int,
        max_dims: Int,
        min_side: Int,
        max_side: Int,
    ):
        self.shape = shape^
        self.min_dims = min_dims
        self.max_dims = max_dims
        self.min_side = min_side
        self.max_side = max_side

    def do_draw(self, mut data: ConjectureData) raises -> List[Int]:
        var n = Int(
            data.draw_integer(Int128(self.min_dims), Int128(self.max_dims))
        )
        var rev = List[Int]()
        for i in range(n):
            if i < len(self.shape):
                # aligned: 1 or the same size, shrinking towards 1
                var side = self.shape[len(self.shape) - 1 - i]
                if side == 1:
                    rev.append(1)
                elif data.draw_integer(Int128(0), Int128(1)) == 0:
                    rev.append(1)
                else:
                    rev.append(side)
            else:
                rev.append(
                    Int(
                        data.draw_integer(
                            Int128(self.min_side), Int128(self.max_side)
                        )
                    )
                )
        rev.reverse()
        return rev^


def _max_side_default(shape: List[Int], min_side: Int) -> Int:
    var m = min_side
    for d in shape:
        m = max(m, d)
    return m + 2


def broadcastable_shapes(
    var shape: List[Int],
    *,
    min_dims: Int = 0,
    max_dims: Optional[Int] = None,
    min_side: Int = 1,
    max_side: Optional[Int] = None,
) raises -> BroadcastableShapesOf:
    """Shapes that can broadcast against `shape` (Hypothesis's
    `broadcastable_shapes`). Aligned dimensions are 1 or the same size and
    shrink towards 1; other dimensions have sizes in
    `[min_side, max_side]` and shrink towards `min_side`. `max_dims`
    defaults to `max(len(shape), min_dims) + 2` and `max_side` to the
    largest aligned size plus 2."""
    var hi_dims = max_dims.value() if max_dims else min(
        max(len(shape), min_dims) + 2, NDIM_MAX
    )
    var hi_side = max_side.value() if max_side else _max_side_default(
        shape, min_side
    )
    if min_dims < 0 or hi_dims < min_dims or hi_dims > NDIM_MAX:
        raise Error(
            "InvalidArgument: broadcastable_shapes: bad dimension bounds"
        )
    if min_side < 0 or hi_side < min_side:
        raise Error("InvalidArgument: broadcastable_shapes: bad side bounds")
    return BroadcastableShapesOf(shape^, min_dims, hi_dims, min_side, hi_side)


# ===----------------------------------------------------------------------=== #
# mutually_broadcastable_shapes
# ===----------------------------------------------------------------------=== #


struct BroadcastableShapes(Copyable, Writable):
    """Shapes that broadcast together, and the shape they broadcast to
    (Hypothesis's `BroadcastableShapes` named tuple)."""

    var input_shapes: List[List[Int]]
    var result_shape: List[Int]

    def __init__(
        out self, var input_shapes: List[List[Int]], var result_shape: List[Int]
    ):
        self.input_shapes = input_shapes^
        self.result_shape = result_shape^

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "BroadcastableShapes(input_shapes=",
            self.input_shapes,
            ", result_shape=",
            self.result_shape,
            ")",
        )


struct MutuallyBroadcastableShapes(Copyable, Strategy):
    """See `mutually_broadcastable_shapes()`."""

    comptime Value = BroadcastableShapes
    var num_shapes: Int
    var base_shape: List[Int]
    var min_dims: Int
    var max_dims: Int
    var min_side: Int
    var max_side: Int

    def __init__(
        out self,
        num_shapes: Int,
        var base_shape: List[Int],
        min_dims: Int,
        max_dims: Int,
        min_side: Int,
        max_side: Int,
    ):
        self.num_shapes = num_shapes
        self.base_shape = base_shape^
        self.min_dims = min_dims
        self.max_dims = max_dims
        self.min_side = min_side
        self.max_side = max_side

    def do_draw(self, mut data: ConjectureData) raises -> BroadcastableShapes:
        # The common dimensions, right-aligned: those overlapping
        # `base_shape` are fixed by it, the others are drawn when first used.
        var nb = len(self.base_shape)
        var common = List[Int](length=self.max_dims, fill=-1)
        for i in range(min(nb, self.max_dims)):
            common[i] = self.base_shape[nb - 1 - i]
        var shapes = List[List[Int]]()
        for _ in range(self.num_shapes):
            var n = Int(
                data.draw_integer(Int128(self.min_dims), Int128(self.max_dims))
            )
            var rev = List[Int]()
            for i in range(n):
                if common[i] < 0:
                    common[i] = Int(
                        data.draw_integer(
                            Int128(self.min_side), Int128(self.max_side)
                        )
                    )
                var side = common[i]
                var one_ok = side != 1 and (self.min_side <= 1 or i < nb)
                if one_ok and data.draw_integer(Int128(0), Int128(1)) == 0:
                    rev.append(1)
                else:
                    rev.append(side)
            rev.reverse()
            shapes.append(rev^)
        var all_shapes = shapes.copy()
        all_shapes.append(self.base_shape.copy())
        var result = _broadcast(all_shapes)
        return BroadcastableShapes(shapes^, result^)


def mutually_broadcastable_shapes(
    *,
    num_shapes: Int,
    var base_shape: List[Int] = [],
    min_dims: Int = 0,
    max_dims: Optional[Int] = None,
    min_side: Int = 1,
    max_side: Optional[Int] = None,
) raises -> MutuallyBroadcastableShapes:
    """`num_shapes` shapes that broadcast with each other and with
    `base_shape`, with the shape they broadcast to (Hypothesis's
    `mutually_broadcastable_shapes`, without gufunc signatures)."""
    if num_shapes < 1:
        raise Error("InvalidArgument: num_shapes must be at least 1")
    var hi_dims = max_dims.value() if max_dims else min(
        max(len(base_shape), min_dims) + 2, NDIM_MAX
    )
    var hi_side = max_side.value() if max_side else _max_side_default(
        base_shape, min_side
    )
    if min_dims < 0 or hi_dims < min_dims or hi_dims > NDIM_MAX:
        raise Error(
            "InvalidArgument: mutually_broadcastable_shapes: bad dimension"
            " bounds"
        )
    if min_side < 0 or hi_side < min_side:
        raise Error(
            "InvalidArgument: mutually_broadcastable_shapes: bad side bounds"
        )
    return MutuallyBroadcastableShapes(
        num_shapes, base_shape^, min_dims, hi_dims, min_side, hi_side
    )


# ===----------------------------------------------------------------------=== #
# basic_indices
# ===----------------------------------------------------------------------=== #

comptime _INT = 0
comptime _SLICE = 1
comptime _ELLIPSIS = 2
comptime _NEWAXIS = 3


struct IndexItem(Copyable, Equatable, Writable):
    """One element of a basic index: an integer, a slice, `...` or a new
    axis."""

    var kind: Int
    var value: Int
    var start: Optional[Int]
    var stop: Optional[Int]
    var step: Optional[Int]

    def __init__(out self, kind: Int, value: Int = 0):
        self.kind = kind
        self.value = value
        self.start = None
        self.stop = None
        self.step = None

    @staticmethod
    def slice(
        start: Optional[Int], stop: Optional[Int], step: Optional[Int]
    ) -> Self:
        var s = Self(_SLICE)
        s.start = start
        s.stop = stop
        s.step = step
        return s^

    def is_full_slice(self) -> Bool:
        return (
            self.kind == _SLICE
            and not self.start
            and not self.stop
            and not self.step
        )

    def __eq__(self, other: Self) -> Bool:
        if self.kind != other.kind:
            return False
        if self.kind == _INT:
            return self.value == other.value
        if self.kind == _SLICE:
            return (
                self.start == other.start
                and self.stop == other.stop
                and self.step == other.step
            )
        return True

    def write_to(self, mut writer: Some[Writer]):
        if self.kind == _INT:
            writer.write(self.value)
        elif self.kind == _ELLIPSIS:
            writer.write("...")
        elif self.kind == _NEWAXIS:
            writer.write("newaxis")
        else:
            if self.start:
                writer.write(self.start.value())
            writer.write(":")
            if self.stop:
                writer.write(self.stop.value())
            if self.step:
                writer.write(":", self.step.value())


struct BasicIndex(Copyable, Writable):
    """A NumPy-style basic index: integers, slices, at most one `...`, and
    new axes."""

    var items: List[IndexItem]

    def __init__(out self, var items: List[IndexItem]):
        self.items = items^

    def to_numojo(self) -> List[IndexTypes]:
        """The index as NuMojo's index entries."""
        var out = List[IndexTypes]()
        for it in self.items:
            if it.kind == _INT:
                out.append(IndexTypes(it.value))
            elif it.kind == _ELLIPSIS:
                var e: EllipsisType = ...
                out.append(IndexTypes(e))
            elif it.kind == _NEWAXIS:
                out.append(IndexTypes(NewAxis()))
            else:
                out.append(IndexTypes(Slice(it.start, it.stop, it.step)))
        return out^

    def apply[dtype: DType](self, a: NDArray[dtype]) raises -> NDArray[dtype]:
        """`a` indexed by this index."""
        return a._getitem_from_index_list(self.to_numojo())

    def result_ndim(self, ndim: Int) -> Int:
        """The number of dimensions of the result of indexing an array with
        `ndim` dimensions."""
        var consumed = 0
        var added = 0
        for it in self.items:
            if it.kind == _INT:
                consumed += 1
            elif it.kind == _SLICE:
                consumed += 1
                added += 1
            elif it.kind == _NEWAXIS:
                added += 1
        # dimensions not mentioned (or covered by ...) are kept whole
        return added + (ndim - consumed)

    def ellipsis_matches_nothing(self, ndim: Int) -> Bool:
        """Whether the index has a `...` that stands for zero dimensions of
        an `ndim`-dimensional array (valid in NumPy; NuMojo 0.12 rejects
        such indices)."""
        var consumed = 0
        var has_ellipsis = False
        for it in self.items:
            if it.kind == _INT or it.kind == _SLICE:
                consumed += 1
            elif it.kind == _ELLIPSIS:
                has_ellipsis = True
        return has_ellipsis and consumed == ndim

    def write_to(self, mut writer: Some[Writer]):
        writer.write("(")
        for i in range(len(self.items)):
            if i > 0:
                writer.write(", ")
            writer.write(self.items[i])
        if len(self.items) == 1:
            writer.write(",")
        writer.write(")")


struct BasicIndices(Copyable, Strategy):
    """See `basic_indices()`."""

    comptime Value = BasicIndex
    var shape: List[Int]
    var min_dims: Int
    var max_dims: Int
    var allow_ellipsis: Bool
    var allow_newaxis: Bool

    def __init__(
        out self,
        var shape: List[Int],
        min_dims: Int,
        max_dims: Int,
        allow_ellipsis: Bool,
        allow_newaxis: Bool,
    ):
        self.shape = shape^
        self.min_dims = min_dims
        self.max_dims = max_dims
        self.allow_ellipsis = allow_ellipsis
        self.allow_newaxis = allow_newaxis

    def _slice(self, mut data: ConjectureData, size: Int) raises -> IndexItem:
        # st.slices(size), restricted to non-negative bounds and positive
        # steps; None (the simplest) for each part when possible
        var start: Optional[Int] = None
        var stop: Optional[Int] = None
        var step: Optional[Int] = None
        if data.draw_integer(Int128(0), Int128(1)) == 1:
            start = Int(data.draw_integer(Int128(0), Int128(size)))
        if data.draw_integer(Int128(0), Int128(1)) == 1:
            stop = Int(data.draw_integer(Int128(0), Int128(size)))
        if data.draw_integer(Int128(0), Int128(1)) == 1:
            step = Int(data.draw_integer(Int128(1), Int128(max(size, 1))))
        return IndexItem.slice(start, stop, step)

    def do_draw(self, mut data: ConjectureData) raises -> BasicIndex:
        # Port of BasicIndexStrategy.do_draw: choose the selection for each
        # dimension, then insert new axes, then maybe an ellipsis.
        var result = List[IndexItem]()
        for dim_size in self.shape:
            if dim_size == 0:
                result.append(IndexItem.slice(None, None, None))
                continue
            # integers(-dim_size, dim_size - 1) | slices(dim_size)
            if data.draw_integer(Int128(0), Int128(1)) == 0:
                result.append(
                    IndexItem(
                        _INT,
                        Int(
                            data.draw_integer(
                                Int128(-dim_size), Int128(dim_size - 1)
                            )
                        ),
                    )
                )
            else:
                result.append(self._slice(data, dim_size))
        var result_dims = 0
        for it in result:
            if it.kind == _SLICE:
                result_dims += 1
        while (
            self.allow_newaxis
            and result_dims < self.max_dims
            and (result_dims < self.min_dims or data.draw_boolean(0.5))
        ):
            var i = Int(data.draw_integer(Int128(0), Int128(len(result))))
            result.insert(i, IndexItem(_NEWAXIS))
            result_dims += 1
        if result_dims < self.min_dims or result_dims > self.max_dims:
            data.mark_invalid("basic_indices: wrong number of dimensions")
        if self.allow_ellipsis and data.draw_boolean(0.5):
            # replace a run of whole-dimension slices around a point with ...
            var i = Int(data.draw_integer(Int128(0), Int128(len(result))))
            var j = i
            while i > 0 and result[i - 1].is_full_slice():
                i -= 1
            while j < len(result) and result[j].is_full_slice():
                j += 1
            var out = List[IndexItem]()
            for k in range(i):
                out.append(result[k].copy())
            out.append(IndexItem(_ELLIPSIS))
            for k in range(j, len(result)):
                out.append(result[k].copy())
            result = out^
        else:
            # trailing whole-dimension slices may be left out
            while (
                len(result) > 0
                and result[len(result) - 1].is_full_slice()
                and data.draw_integer(Int128(0), Int128(7)) != 0
            ):
                _ = result.pop()
        return BasicIndex(result^)


def basic_indices(
    var shape: List[Int],
    *,
    min_dims: Int = 0,
    max_dims: Optional[Int] = None,
    allow_newaxis: Bool = False,
    allow_ellipsis: Bool = True,
) raises -> BasicIndices:
    """Basic indices (integers, slices, `...`, new axes) for an array of
    `shape`, giving results with `min_dims` to `max_dims` dimensions
    (Hypothesis's `basic_indices`). `max_dims` defaults to `len(shape)`, or
    `max(len(shape), min_dims) + 2` with `allow_newaxis`."""
    var hi: Int
    if max_dims:
        hi = max_dims.value()
    elif allow_newaxis:
        hi = min(max(len(shape), min_dims) + 2, NDIM_MAX)
    else:
        hi = min(len(shape), NDIM_MAX)
    if min_dims < 0 or hi < min_dims:
        raise Error("InvalidArgument: basic_indices: bad dimension bounds")
    if not allow_newaxis and min_dims > len(shape):
        raise Error(
            "InvalidArgument: basic_indices: min_dims > len(shape) needs"
            " allow_newaxis=True"
        )
    return BasicIndices(shape^, min_dims, hi, allow_ellipsis, allow_newaxis)


# ===----------------------------------------------------------------------=== #
# integer_array_indices
# ===----------------------------------------------------------------------=== #


struct IntegerArrayIndices[Sh: Strategy & Copyable](Copyable, Strategy):
    """See `integer_array_indices()`."""

    comptime Value = List[NDArray[DType.int]]
    var shape: List[Int]
    var result_shape: Self.Sh

    def __init__(out self, var shape: List[Int], var result_shape: Self.Sh):
        self.shape = shape^
        self.result_shape = result_shape^

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var rshape = rebind_var[List[Int]](data.draw(self.result_shape))
        var out = List[NDArray[DType.int]]()
        for side in self.shape:
            var a = nm.zeros[DType.int](rshape)
            for i in range(a.size):
                a.unsafe_set(
                    i,
                    Scalar[DType.int](
                        Int(data.draw_integer(Int128(-side), Int128(side - 1)))
                    ),
                )
            out.append(a^)
        return out^


def integer_array_indices(
    var shape: List[Int], *, var result_shape: ArrayShapes
) raises -> IntegerArrayIndices[ArrayShapes]:
    """One integer array per dimension of `shape`, all of a shape drawn from
    `result_shape`, with values valid as indices (negative ones included)
    along their dimension (Hypothesis's `integer_array_indices`)."""
    for side in shape:
        if side <= 0:
            raise Error(
                "InvalidArgument: integer_array_indices needs positive sides"
            )
    return IntegerArrayIndices[ArrayShapes](shape^, result_shape^)


def integer_array_indices(
    var shape: List[Int],
) raises -> IntegerArrayIndices[ArrayShapes]:
    """`integer_array_indices(shape, result_shape=array_shapes())`."""
    return integer_array_indices(shape^, result_shape=array_shapes())
