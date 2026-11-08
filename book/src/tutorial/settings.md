# Configuring test settings

`Settings` controls how a test runs: how many examples to try, which
random seed to use, where to save failures, and more. Hypothesis's
settings are a decorator with named profiles; proptest's are a plain struct
of keyword arguments, passed as the last argument of `given`, `check`,
`given_data`, and the state machine runners.

## Configuring a single test

```mojo
from proptest import given, integers, Settings

def main() raises:
    def prop(x: Int) raises:
        pass

    given(integers(), prop, Settings(max_examples=500))
    print("passed")
```

Every field has a default, so you only name the ones you change.

## Changing the number of test cases

`max_examples` (default 100) is the number of *valid* examples to try
before the test passes. Raise it for important or subtle properties, lower
it for slow ones:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    def prop(xs: List[Int]) raises:
~        pass
~
    given(lists(integers()), prop, Settings(max_examples=5000))
```

The test may run more or fewer times than `max_examples`; see
[How many times will proptest run my test?](../explanation/test-case-count.md)

## Other settings

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    var settings = (
Settings(
    max_examples=500,                # valid examples to try
    seed=UInt64(1234),               # fixed seed (or derandomize=True)
    database=None,                   # don't save failures
    phases=Phases(shrink=False),     # skip shrinking
    verbosity=Verbosity.verbose,     # say what the run is doing
    report_multiple_bugs=False,      # stop at the first distinct failure
    suppress_health_check=[HealthCheck.filter_too_much],
    deadline=500.0,                  # ms per example (default 200; None disables)
    print_blob=True,                 # print a blob for reproduce=
    show_statistics=True,            # print events, tables and coverage
)
~    )
~    def prop(x: Int) raises:
~        pass
~    given(integers(), prop, settings)
```

The most useful:

- **`seed`** fixes the random seed, so a run is repeatable.
  **`derandomize=True`** derives the seed from the test's identity
  instead, so every run of the test tries the same examples.
- **`database`** is the directory where failing examples are saved
  (default `.proptest/examples`); `None` disables it. See
  [Replaying failures](replaying-failures.md).
- **`deadline`** fails any example whose test body takes longer than this
  many milliseconds (time spent generating the data isn't counted). It
  catches accidental slowness; set it to `None` for tests that are
  expected to be slow.
- **`verbosity`**: `Verbosity.quiet`, `normal`, `verbose`, or `debug`.
  Verbose output reports each run's counts and seed, and prints the
  statistics and a reproduce blob with every failure:

  ```text
  proptest: test.mojo:8:14: 3 valid, 0 invalid, 0 overrun examples in 10 calls (seed 17430662364796405847)
  proptest: first failure at call 2; shrinking
  ```

- **`phases`** turns phases of the run on or off: `explicit`, `reuse`,
  `generate`, `target`, `shrink`, and `explain`. For example,
  `Phases(explain=False)` skips the explain phase, which can be slow for
  tests with many arguments.
- **`report_multiple_bugs`** (default `True`): when a run finds failures
  with different causes, report them all. A failure's cause is where its
  error was raised; see [How proptest works](../explanation/how-it-works.md#distinct-failures).
- **`stateful_step_count`** (default 50): the maximum number of steps in a
  stateful test.

The [settings reference](../reference/settings.md) lists every setting.

## Changing settings across a test suite

proptest has no global settings profiles (Mojo has no global variables
for a library to keep them in). Two things replace them.

The first is the environment. These variables change any setting that a
test leaves at its default, much like loading a Hypothesis profile:

| Variable | Setting |
|---|---|
| `PROPTEST_MAX_EXAMPLES` | `max_examples` |
| `PROPTEST_SEED` | `seed` |
| `PROPTEST_VERBOSITY` | `verbosity`: `quiet`, `normal`, `verbose`, or `debug` |
| `PROPTEST_DATABASE` | `database`: a directory, or `none` to disable it |

A value set explicitly in the code wins over the environment. For example,
a CI job might run every test with more examples and without the database:

```sh
PROPTEST_MAX_EXAMPLES=1000 PROPTEST_DATABASE=none mojo run -I . tests/test_parser.mojo
```

The second is an ordinary function. A test suite can define its own
defaults and pass them to every test:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
def suite_settings() -> Settings:
    return Settings(max_examples=300, deadline=None)

~def main() raises:
~    def prop(x: Int) raises:
~        pass
~
    given(integers(), prop, suite_settings())
```
