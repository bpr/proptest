# Generate NuMojo arrays

[NuMojo](https://github.com/Mojo-Numerics-and-Algorithms-group/NuMojo) is
Mojo's NumPy-like array library. proptest's strategies for it live in a
separate package, `proptest_numojo`, in the repository's `extras/`
directory, so that proptest itself doesn't depend on NuMojo. It's the
counterpart of `hypothesis.extra.numpy`.

## Setup

Put proptest, `extras/`, and the directory containing `numojo` on the
include path:

```sh
mojo run -I path/to/proptest -I path/to/proptest/extras -I path/to/numojo-parent my_test.mojo
```

`proptest_numojo` needs a NuMojo that builds with Mojo 1.3. The published
NuMojo 0.12 requires an older Mojo; `extras/run_tests.sh` describes a
patched copy that works.

## Arrays

```mojo
~from std.testing import assert_true
from numojo.prelude import *
from proptest import given, floats
from proptest_numojo import arrays, array_shapes

def prop(a: NDArray[DType.float64]) raises:
    assert_true(a.ndim >= 1 and a.ndim <= 2)

~def main() raises:
    given(arrays[DType.float64](array_shapes(max_dims=2), floats(-1.0, 1.0)), prop)
```

| Strategy | Values |
|---|---|
| `arrays[dtype](shape, elements, unique=)` | `NDArray[dtype]`; `shape` is a fixed `List[Int]` or a shape strategy; `elements` defaults to `from_dtype[dtype]()` |
| `array_shapes(min_dims=, max_dims=, min_side=, max_side=)` | shapes, shrinking towards fewer and shorter dimensions |
| `from_dtype[dtype]()` | scalars over a dtype's whole range, including NaN and infinities for floats |

## Broadcasting and indexing

| Strategy | Values |
|---|---|
| `broadcastable_shapes(shape, ...)` | shapes that broadcast against `shape` |
| `mutually_broadcastable_shapes(num_shapes=, base_shape=, ...)` | several shapes that broadcast together, with their result shape |
| `basic_indices(shape, min_dims=, max_dims=, allow_newaxis=, allow_ellipsis=)` | integers, slices, `...` and new axes for indexing an array of `shape` |
| `integer_array_indices(shape, result_shape=)` | one integer array per dimension, for fancy indexing |

These follow Hypothesis's functions of the same names (without gufunc
signatures). Indices are values of proptest's own `BasicIndex` and
`IndexItem` types, since NuMojo has no single index type; apply them to an
array as your code would.

## Shrinking

Arrays shrink like other proptest values: towards smaller shapes, and
towards simple element values (zeros). A failure prints the array as
NuMojo writes it.
