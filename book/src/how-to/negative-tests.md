# Write negative tests

A *negative test* checks that a property test fails when it should. It's
the property-testing version of making sure a test can go red: before
trusting that a property holds, check that it catches a bug you've planted.
This is especially worthwhile for custom strategies, which can quietly fail
to produce the inputs a property needs.

## `expect_failure`

`expect_failure(f)` runs a test function that should fail, and returns the
failure report. If the function passes, `expect_failure` raises
(QuickCheck's `expectFailure`):

```mojo
from std.testing import assert_true
from proptest import expect_failure, check, Settings

def buggy_max(xs: List[Int]) -> Int:
    var m = 0          # BUG: wrong for lists of negative numbers
    for x in xs:
        m = max(m, x)
    return m

def main() raises:
    def max_is_an_element(xs: List[Int]) -> Bool:
        return len(xs) == 0 or buggy_max(xs) in xs

    def run() raises:
        check(max_is_an_element, Settings(database=None))

    var report = expect_failure(run)
    assert_true("given([-1])" in report, report)
    print("the property catches the bug")
```

The report is the message the test would have raised, so you can also check
what was found, as above. `expect_failure` only accepts proptest's own
failures (falsifying examples and coverage failures); any other error, such
as a health check, is raised again, since it means the test didn't really
run.

## `run_property`: the result as data

`run_property(strategy, test, settings)` runs a property like `given`, but
returns a `PropertyResult` instead of raising (QuickCheck's
`quickCheckResult`):

```mojo
from proptest import run_property, lists, integers, fail, Settings

def main() raises:
    def short(xs: List[Int]) raises:
        if len(xs) >= 2:
            fail("too long")

    var r = run_property(lists(integers()), short, Settings(database=None))
    print(r.passed())                  # False
    print(r.counterexample.value())    # [0, 0]
    print(r.blob)                      # Settings(reproduce=...) replays it
```

A `PropertyResult[T]` has:

- `passed()`: whether the property held;
- `counterexample`: the shrunk failing value, typed, as an `Optional[T]`;
- `message`: the report `given` would have raised;
- `blob`: a string for `Settings(reproduce=...)`;
- `report`: the `RunReport`, with the counts of valid, invalid, and overrun
  examples, the number of shrinks, and the run's statistics.

It takes a single strategy; use `tuples(...)` for several arguments.
`run_property` is useful for building tools on top of proptest, and for
tests that check the counterexample itself rather than the message.
