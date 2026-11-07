# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Property-based testing for Mojo, ported from Hypothesis.

Write a property, say which inputs it should hold for, and proptest checks
it against many generated inputs, shrinking any failure to a minimal
example:

```mojo
from proptest import given, lists, integers
from std.testing import assert_equal

def test_sort_idempotent() raises:
    def prop(xs: List[Int]) raises:
        var once = xs.copy()
        sort(once)
        var twice = once.copy()
        sort(twice)
        assert_equal(once, twice)
    given(lists(integers()), prop)
```
"""

from proptest.core import (
    given,
    given_data,
    find,
    example,
    assume,
    fail,
    check_examples,
    run_test,
)
from proptest.settings import Settings, Phases, Verbosity, HealthCheck
from proptest.database import ExampleDatabase
from proptest.internal.data import ConjectureData, Status
from proptest.strategies.strategy import Strategy, Drawable, Many, draw
from proptest.strategies.core import (
    integers,
    integers_of,
    booleans,
    floats,
    floats32,
    just,
    sampled_from,
    one_of,
    boxed,
    BoxedStrategy,
    map,
    filter,
    flatmap,
    composite,
    lists,
    unique_lists,
    unique_lists_by,
    sets,
    dictionaries,
    optionals,
    permutations,
    tuples,
    characters,
    text,
    binary,
    recursive,
    shared,
    # strategy types, for spelling out the types of strategies
    Integers,
    ScalarIntegers,
    Booleans,
    Floats,
    Floats32,
    Just,
    SampledFrom,
    OneOf,
    Mapped,
    Filtered,
    FlatMapped,
    Composite,
    Lists,
    UniqueLists,
    UniqueValues,
    Sets,
    Dictionaries,
    Optionals,
    Permutations,
    Tuples2,
    Tuples3,
    Tuples4,
    Tuples5,
    Tuples6,
    Shared,
    Characters,
    Text,
    Binary,
    Recursive,
)
from proptest.strategies.regex import from_regex, Regex
from proptest.strategies.types import (
    from_type,
    FromType,
    Arbitrary,
    draw_from_type,
)
from proptest.stateful import (
    StateMachine,
    Bundle,
    run_state_machine_as_test,
    run_state_machine,
)
