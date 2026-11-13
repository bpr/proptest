# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Property-based testing for Mojo, inspired by Hypothesis.

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
    before_minimal_test_case,
    run_property,
    PropertyResult,
    expect_failure,
    Outcome,
    Testable,
    given_data,
    check,
    find,
    example,
    assume,
    fail,
    check_examples,
    run_test,
)
from proptest.fuzz import FuzzReport, FuzzTarget, fuzz_target, fuzz_target_data
from proptest.settings import (
    Settings,
    Phases,
    Verbosity,
    HealthCheck,
    Confidence,
)
from proptest.internal.statistics import Statistics
from proptest.internal.engine import RunReport
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
    lazy_just,
    sampled_from,
    one_of,
    boxed,
    BoxedStrategy,
    map,
    apply,
    Applied2,
    Applied3,
    Applied4,
    Applied5,
    Applied6,
    filter,
    filter_map,
    cover,
    tabulate,
    flatmap,
    composite,
    lists,
    unique_lists,
    unique_lists_by,
    sets,
    dictionaries,
    optionals,
    permutations,
    subsequence,
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
    LazyJust,
    SampledFrom,
    OneOf,
    Alternatives,
    Mapped,
    Filtered,
    FilterMapped,
    Covered,
    Tabulated,
    FlatMapped,
    Composite,
    Lists,
    UniqueLists,
    UniqueValues,
    Sets,
    Dictionaries,
    Optionals,
    Permutations,
    Subsequences,
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
    build,
    Built,
    field,
    Field,
    FieldBinding,
)
from proptest.strategies.constraints import (
    Bounded,
    Positive,
    NonNegative,
    NonZero,
    NonEmpty,
    Sorted,
    Blind,
    Via,
)
from proptest.strategies.special import PolyA, PolyB, PolyC, Poly, Index
from proptest.strategies.functions import functions, Function, Functions
from proptest.stateful import (
    StateMachine,
    Bundle,
    run_state_machine_as_test,
    run_state_machine,
    TypedStateMachine,
    run_typed_state_machine_as_test,
    run_typed_state_machine,
)
from proptest.commands import (
    Command,
    Commands,
    CommandSequences,
    commands,
    run_commands,
    check_commands,
)
