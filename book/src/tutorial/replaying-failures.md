# Replaying failures

When a test fails, you want the failure to keep happening until you've
fixed it, and you want to be able to rerun exactly the failing input.
proptest has three tools for this: the example database, explicit
examples, and reproduce blobs.

## The example database

When a test fails, proptest saves the shrunk failing example in the
*example database*: a directory, by default `.proptest/examples` under the
working directory. The next time the test runs, proptest tries the saved
examples first (the *reuse* phase). So a failure doesn't disappear on the
next run just because the random search went somewhere else. Once a saved
example passes, it's deleted.

Each test's examples are kept under a key, which `given` and `check` take
from the test's source location (`file:line:column`). Moving a test to
another line changes its key, and its saved examples are no longer found.
To keep them, give the test a fixed key with
`Settings(database_key="parser round trip")`.

What's saved is the example's *choice sequence*: the choices the strategies
made, one per line, not the value itself. It replays through whatever
strategies the test uses now. So if you change the test's strategies, a
saved example may turn into a different value, or become invalid and be
dropped.

### Disabling the database

Pass `Settings(database=None)`, or set `PROPTEST_DATABASE=none` in the
environment to disable it for every test that uses the default. A test
suite's runner might do this in CI, where nothing is kept between runs
anyway. You can also add `.proptest/` to `.gitignore`.

## Explicit examples

`check_examples(examples, test)` runs a test on specific inputs (Hypothesis's
`@example`). Use it for inputs that must always be tested, such as a
regression from a bug report or a known edge case:

```mojo
from proptest import check_examples, given, integers

def main():
    def small(x: Int) raises:
        if x > 100:
            raise Error("too big")

    try:
        check_examples([1, 5, 500], small)
    except e:
        print(e)
```

```text
Falsifying explicit example (example.mojo:9:23):
    example(500)
too big
```

Explicit examples are not shrunk: the input is the one you gave.

### Prefer explicit examples to the database for important cases

The database is a cache, not a test suite: a saved example is lost when the
test's strategies or location change, and it isn't shared through version
control. When a failure matters enough that it must never come back, add
it as an explicit example.

## Replaying a test case with `reproduce`

With `Settings(print_blob=True)`, or verbose output, a failure report ends
with a line like this:

```text
Falsifying example (test.mojo:20:14):
    given(101)
    To reproduce this example, run the test with Settings(reproduce="proptest1:aToxMDEK")
too big
```

Running the test with `Settings(reproduce="proptest1:aToxMDEK")` replays
exactly that example, without any search or shrinking (Hypothesis's
`@reproduce_failure`). The blob is the encoded choice sequence, so it's
small enough to paste into a bug report. Like a database entry, it only
reproduces the failure while the test's strategies stay the same.

## Repeating a run with a seed

Verbose output also prints the run's random seed. `Settings(seed=...)` or
`PROPTEST_SEED=...` repeats the whole run, including the examples that
passed. `Settings(derandomize=True)` makes every run of a test use the same
seed, derived from its key.

## Sharing failures

The database is a directory of small text files, so you can copy it between
machines, or point several checkouts at one directory with
`PROPTEST_DATABASE=/shared/path`. Keys are source locations, so the
checkouts should be at the same version of the tests.

## Stopping on the minimal example in a debugger

proptest calls `before_minimal_test_case(name)` just before it replays a
shrunk failure for the last time. Set a breakpoint on it to stop only on the
minimal failing example; see [Debug a failing test](../how-to/debugging.md).
