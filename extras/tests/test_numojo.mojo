# Tests for the NuMojo strategies (extras/proptest_numojo). Run with
#   pixi run test-numojo
# Ported in spirit from hypothesis/tests/numpy/test_gen_data.py.

from std.testing import TestSuite, assert_equal, assert_true, assert_false
from std.math import isnan

import numojo as nm
from numojo.prelude import *

from proptest import *
from proptest_numojo import (
    arrays,
    array_shapes,
    from_dtype,
    broadcastable_shapes,
    mutually_broadcastable_shapes,
    basic_indices,
    integer_array_indices,
    BroadcastableShapes,
    BasicIndex,
)
from proptest_numojo.indices import _broadcast


def fast() -> Settings:
    return Settings(database=None, max_examples=100)


def test_fixed_shape() raises:
    def prop(a: NDArray[DType.int32]) raises:
        assert_equal(a.ndim, 2)
        assert_equal(a.size, 6)

    given(arrays[DType.int32]([2, 3]), prop, fast())


def test_shapes_respect_bounds() raises:
    def prop(s: List[Int]) raises:
        assert_true(len(s) >= 1 and len(s) <= 3)
        for d in s:
            assert_true(d >= 2 and d <= 4)

    given(array_shapes(max_dims=3, min_side=2, max_side=4), prop, fast())


def test_elements_respect_strategy() raises:
    def prop(a: NDArray[DType.float64]) raises:
        for i in range(a.size):
            var x = a.unsafe_get(i)
            assert_true(x >= -1.0 and x <= 1.0)

    given(
        arrays[DType.float64](array_shapes(), floats(-1.0, 1.0)), prop, fast()
    )


def test_from_dtype_covers_range() raises:
    def big(x: UInt8) -> Bool:
        return x > 250

    assert_equal(find(from_dtype[DType.uint8](), big), UInt8(251))

    def has_nan(x: Float64) -> Bool:
        return isnan(x)

    assert_true(isnan(find(from_dtype[DType.float64](), has_nan)))


def test_unique_elements() raises:
    def prop(a: NDArray[DType.int8]) raises:
        for i in range(a.size):
            for j in range(i + 1, a.size):
                assert_true(a.unsafe_get(i) != a.unsafe_get(j))

    given(arrays[DType.int8]([3, 3], unique=True), prop, fast())


def test_array_failures_shrink() raises:
    # a "bug": summing more than 5 elements loses precision
    def prop(a: NDArray[DType.int64]) raises:
        if a.size > 5 and a.unsafe_get(0) > 100:
            fail("big first element in a big array")

    var msg = String()
    try:
        given(arrays[DType.int64](array_shapes(max_dims=2)), prop, fast())
    except e:
        msg = String(e)
    assert_true("big first element" in msg, msg)
    # minimal: shape [6] (or [2, 3]/[3, 2]), first element 101, rest 0
    assert_true("101" in msg, msg)


def test_broadcastable_shapes() raises:
    var base: List[Int] = [3, 1, 4]

    def prop(s: List[Int]) raises {base}:
        assert_true(len(s) <= 5)
        var both: List[List[Int]] = [base.copy(), s.copy()]
        _ = _broadcast(both)  # raises if they don't broadcast

    given(broadcastable_shapes(base.copy()), prop, fast())

    def any_shape(s: List[Int]) -> Bool:
        return True

    assert_equal(len(find(broadcastable_shapes([2, 3]), any_shape)), 0)

    def long(s: List[Int]) -> Bool:
        return len(s) >= 3

    # aligned dimensions shrink to 1, unaligned ones to min_side
    assert_equal(find(broadcastable_shapes([2, 3]), long), [1, 1, 1])


def test_mutually_broadcastable_shapes() raises:
    def prop(b: BroadcastableShapes) raises:
        assert_equal(len(b.input_shapes), 3)
        var all = b.input_shapes.copy()
        all.append([2, 1])
        assert_equal(_broadcast(all), b.result_shape)

    given(
        mutually_broadcastable_shapes(num_shapes=3, base_shape=[2, 1]),
        prop,
        fast(),
    )


def _all_ints_with_newaxis(ix: BasicIndex, ndim: Int) -> Bool:
    var ints = 0
    var newaxes = 0
    for it in ix.items:
        if it.kind == 0:  # integer
            ints += 1
        elif it.kind == 3:  # new axis
            newaxes += 1
    return ints == ndim and newaxes > 0


def test_basic_indices_index_arrays() raises:
    var shape: List[Int] = [3, 4, 2]
    var a = nm.zeros[DType.int32](shape)

    def prop(ix: BasicIndex) raises {shape, a}:
        # NumPy accepts an ellipsis standing for no dimensions, e.g.
        # (..., 0, 0, 0) on a 3-D array; NuMojo 0.12 counts the ellipsis as
        # a dimension and raises "Too many indices". (Found by this test.)
        assume(not ix.ellipsis_matches_nothing(len(shape)))
        # NuMojo 0.12 also drops new axes when every dimension of the array
        # is indexed by an integer: a[newaxis, 0, 0, 0] has shape () rather
        # than NumPy's (1,). (Also found by this test.)
        assume(not _all_ints_with_newaxis(ix, len(shape)))
        var r = ix.apply(a)
        assert_equal(r.ndim, ix.result_ndim(len(shape)), String(ix))

    given(basic_indices(shape.copy()), prop, fast())
    given(
        basic_indices(shape.copy(), allow_newaxis=True, min_dims=1),
        prop,
        fast(),
    )

    def anything(ix: BasicIndex) -> Bool:
        return True

    assert_equal(
        String(find(basic_indices(shape.copy()), anything)), "(0, 0, 0)"
    )


def test_integer_array_indices() raises:
    var shape: List[Int] = [5, 3]

    def prop(ixs: List[NDArray[DType.int]]) raises {shape}:
        assert_equal(len(ixs), 2)
        assert_equal(ixs[0].size, ixs[1].size)
        for d in range(2):
            for i in range(ixs[d].size):
                var v = Int(ixs[d].unsafe_get(i))
                assert_true(v >= -shape[d] and v < shape[d])
        var a = nm.zeros[DType.int32](shape)
        _ = a[ixs[0]]

    given(integer_array_indices(shape.copy()), prop, fast())


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
