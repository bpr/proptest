# Check the distribution of inputs

A property test can pass because the property holds, or because the
strategies never produce the inputs that would break it. A strategy for
"lists" that almost always makes short lists, or a filter that rejects
every interesting value, makes a test that passes and checks little.
Coverage requirements (from QuickCheck's `cover` and `checkCoverage`)
state what the inputs should include, and fail the test when they don't.

## Declare a requirement

In a `given_data` test, `data.cover(percent, condition, label)` requires
that at least `percent`% of test cases satisfy `condition`:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def prop(mut data: ConjectureData) raises:
~    var xs = data.draw(lists(integers()))
    data.cover(20, len(xs) >= 5, "long")
~
~def main() raises:
~    given_data(prop, Settings(database=None, verbosity=Verbosity.quiet))
```

For `given` and `check` tests, wrap the strategy instead:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    def prop(xs: List[Int]) raises:
~        pass
~
    var xs = cover(lists(integers()), 20, "long", lambda (xs: List[Int]) -> Bool: len(xs) >= 5)
    given(xs, prop)
```

By default, an unmet requirement prints a warning after the run:

```text
proptest: test.mojo:13:10: only 10.10% above 90 (in 99 examples), but expected 50.0%
```

## Make it a failure: `check_coverage`

With `Settings(check_coverage=Confidence())`, an unmet requirement fails the
test. A coverage check is statistical: with 100 examples, a condition that
holds 22% of the time will sometimes be seen in fewer than 20% of them. So
proptest decides with a significance test, as QuickCheck does:

- It generates past `max_examples` when the answer isn't clear yet,
  checking again at 2×, 4×, 8×, ... the number of examples.
- A requirement passes once proptest is confident that the true share is
  at least `tolerance` × `percent` (by default 0.9 × the requirement).
- It fails once proptest is confident the true share is below `percent`.
- Each conclusion is wrong with probability about `1 / certainty` (by
  default one in a billion).

```mojo
from proptest import given, cover, integers, Settings, Confidence

def main() raises:
    def prop(x: Int) raises:
        pass

    var s = cover(integers(0, 100), 50, "above 90", lambda (x: Int) -> Bool: x > 90)
    try:
        given(s, prop, Settings(database=None, check_coverage=Confidence()))
    except e:
        print(e)
```

```text
Insufficient coverage (coverage.mojo:9:14):
    only 10.00% above 90 (in 100 examples), but expected 50.0%
```

`Confidence(certainty=1e9, tolerance=0.9)` sets the two parameters. Raise
`certainty` for fewer wrong conclusions, at the cost of more examples
before one is reached.

## Look before you require

To see the distribution before deciding on requirements, record it with
`tabulate` or `data.event` and run with `Settings(show_statistics=True)`.
See [Adding notes and statistics](../tutorial/adding-notes.md#statistics).
