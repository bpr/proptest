# How many times will proptest run my test?

The short answer is "`max_examples` times", 100 by default. The long
answer has exceptions:

- **fewer**, if proptest exhausts the search space early;
- **more**, if some test cases are rejected (by `assume` or `filter`) or
  too large, since those don't count;
- **more**, under `check_coverage`, until the coverage requirements are
  settled;
- **fewer or more**, if proptest finds a failure.

## Search space exhaustion

proptest never runs an identical test case twice, and it knows when there
are no more to try:

```mojo
from proptest import given, integers

def main() raises:
    var calls = 0

    def prop(n: Int) raises {mut calls}:
        calls += 1

    given(integers(0, 19), prop)
    print(calls)   # 20
```

There are only 20 integers to try, so the test runs 20 times. The same
thing shows up less obviously in the statistics: after the empty list has
been tried once, `lists(...)` never generates it again.

## Rejected test cases

A test case that fails an `assume`, a `filter` (after three tries), or
returns `Outcome.discard()` is *invalid*, and doesn't count towards
`max_examples`:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
def prop(n: Int) raises:
    assume(n % 2 == 0)
~
~def main() raises:
~    given(integers(), prop, Settings(database=None))
```

runs about 200 times to get 100 valid examples. If most test cases are
invalid, the `filter_too_much` health check fails the test.

## Test cases that are too large

There's a limit on the number of choices in a test case (8,192). A test
case that hits it is *overrun*: abandoned, and not counted. Early in a run,
proptest also keeps test cases deliberately small, so that simple bugs are
found with simple inputs, and abandons those that grow too large. Many
overruns fail the `data_too_large` health check.

## Coverage checks

With `Settings(check_coverage=Confidence())`, proptest keeps generating
past `max_examples` until every `cover` requirement is known to hold or
fail, up to 100,000 examples.

## Failing test cases

When proptest finds a failure, it stops generating. It then runs the test
many more times while shrinking, and while explaining the result. Finally
it runs the minimal example once more, to collect its report and check
that the failure is reproducible.
