# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Strategies for NuMojo arrays: the counterpart of `hypothesis.extra.numpy`.

A separate package, so that proptest itself doesn't depend on NuMojo. Put
both on the include path:

    mojo run -I <proptest repo> -I <proptest repo>/extras -I <numojo parent> test.mojo

```mojo
from proptest import given, floats
from proptest_numojo import arrays, array_shapes

def prop(a: NDArray[DType.float64]) raises:
    ...
given(arrays[DType.float64](array_shapes(max_dims=2), floats(-1.0, 1.0)), prop)
```
"""

from proptest_numojo.arrays import (
    arrays,
    array_shapes,
    from_dtype,
    Arrays,
    ArrayShapes,
)
from proptest_numojo.indices import (
    broadcastable_shapes,
    mutually_broadcastable_shapes,
    basic_indices,
    integer_array_indices,
    BroadcastableShapes,
    BasicIndex,
    IndexItem,
)
