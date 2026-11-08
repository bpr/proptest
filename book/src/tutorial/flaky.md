# Flaky failures

A test is *flaky* if it can pass or fail on the same input. Property-based
testing relies on replaying inputs: to shrink a failure, proptest runs the
test again on simpler variations of the input, and to report it, runs the
shrunk input once more. If the test's outcome depends on something other
than its input, none of that works.

## Why flakiness is bad

When a test fails only sometimes, the shrinker gets misleading answers: a
simpler input appears to pass because the flaky condition didn't happen,
not because the input avoids the bug. The reported example may not fail
when you try it, and the database replays an example that doesn't
reproduce.

## Common sources of flakiness

- **The clock**: timeouts, measurements, anything that depends on how fast
  the code runs.
- **Randomness** not drawn through proptest, such as a random generator
  seeded from the time.
- **External state**: files, the network, environment variables.
- **State left over between test cases**: a captured mutable variable, a
  cache, or a global resource that one test case changes and the next one
  sees.

Draw every random choice through proptest (`data.draw`, or a strategy), and
reset state at the start of each test case.

## Kinds of flakiness proptest detects

### A failure that doesn't reproduce

After shrinking, proptest runs the minimal example one last time to
collect its report. If it passes, proptest says so:

```text
Flaky: the falsifying example did not fail when replayed
```

A deadline failure that passes on replay is reported as a flaky deadline:
an example exceeded the deadline once, but not again. For timing-sensitive
tests, disable the deadline (`deadline=None`) or raise it.

### Inconsistent data generation

proptest records the choices each test case makes in a tree, so that it
doesn't run the same input twice. If replaying a choice sequence makes
different *kinds* of choice than before, the strategies themselves aren't
deterministic, and proptest raises:

```text
FlakyStrategyDefinition: Inconsistent data generation! Data generation behaved differently
between different runs (...). Is the strategy or test depending on external state, such as
a captured mutable variable or the clock?
```

The usual cause is a strategy or `given_data` test that decides what to draw
from something other than earlier draws: a counter captured by the closure,
or the time.
