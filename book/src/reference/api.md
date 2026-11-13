# Tests and results

Everything here is imported from `proptest`. Functions that run tests take
an optional `location` keyword argument, which defaults to the caller's
source location. It names the test in reports and keys it in the example
database; you only need it when wrapping these functions in your own
helpers.

## Running tests

### `given`

```mojo-sig
given(s1, test, settings=Settings())
given(s1, s2, test, settings=Settings())
...                                        # up to six strategies
```

Runs `test(a1, ..., aN)` on values drawn from the strategies, `max_examples`
times (see [How many times will proptest run my test?](../explanation/test-case-count.md)).
If the test raises, shrinks the failing input and raises an `Error` whose
message is the failure report. The test's parameter types must be the
strategies' value types. It formats the arguments after the test runs, so
generated `Function`s can print the calls made.

### `check`

```mojo-sig
check(prop, settings=Settings())
```

Like `given`, with each argument drawn by `from_type` from the property's
parameter types. `prop` takes one to six arguments and either raises on
failure, returns `Bool` (`False` fails with `check: the property returned
False`), or returns an `Outcome`.

### `given_data`

```mojo-sig
given_data(test, settings=Settings())   # test: def(mut ConjectureData) raises
```

Runs a test that draws its own values with `data.draw(strategy, label)`
(Hypothesis's `st.data()`). Reports list each draw as `Draw n (label):
value`.

### `check_examples`

```mojo-sig
check_examples(examples: List[V], test)
```

Runs `test` on each explicit example (Hypothesis's `@example`), raising
`Falsifying explicit example` for the first that fails. Explicit examples
are not shrunk.

### `run_test`

```mojo-sig
run_test(test_fn, settings, name) -> RunReport   # test_fn: def(mut ConjectureData) raises
```

The engine entry point used by the functions above: generate, shrink, and
replay, then return a `RunReport` without raising for failures. `name`
identifies the test in reports, and its `settings.database_key` should be
set if you use the database.

### `fuzz_target`

```mojo-sig
fuzz_target(s1, test, settings=Settings()) -> FuzzTarget[...]
fuzz_target(s1, s2, test, settings=Settings()) -> FuzzTarget[...]
...                                        # up to six strategies
fuzz_target_data(test, settings=Settings()) -> FuzzTarget[...]
```

Makes a fuzz target from the same arguments as `given` (or
`given_data`), without running it. `target.fuzz_one_input(bytes)` runs
the test once, reading its choices from `bytes` (Hypothesis's
`fuzz_one_input`). It returns the canonical bytes that replay the test
case if the test passed, `None` if the bytes don't make a valid test case,
and raises the test's error if it failed, after saving the example to the
database. The target owns the test and its strategies.

```mojo-sig
target.fuzz(seconds=60, *, max_inputs=None) -> FuzzReport
```

Fuzzes the test for `seconds` (or `max_inputs` test cases), keeping a
corpus of test cases that covered something new and mutating them. It
raises the shrunk failures, as `given` does, if it finds any, and returns
a `FuzzReport` (`inputs`, `valid`, `corpus`, `features`, `seconds`)
otherwise. With a database, the corpus is saved under
`<database_key>.fuzz`. See [Drive a test from a fuzzer](../how-to/fuzzing.md).

## Inside a test

### `assume`

```mojo-sig
assume(condition: Bool) raises
```

Discards the current test case if `condition` is false. Discarded test cases
don't count towards `max_examples`; too many fail the `filter_too_much`
health check.

### `fail`

```mojo-sig
fail(msg: String) raises
```

Fails the test with `msg`. Like the `std.testing` assertions, the error
records where it was raised, which is how proptest tells distinct bugs
apart.

### `ConjectureData` methods for tests

In `given_data` tests, `composite` functions, state machine rules, and
`Arbitrary.arbitrary`:

| Method | Description |
|---|---|
| `data.draw(strategy, label="")` | Draw a value. With a label, the value is named in reports. |
| `data.note(msg)` | Add a line to the report of the final, shrunk example. |
| `data.event(label)` | Record an event, counted in the run's statistics. |
| `data.tabulate(table, value)` | Record a value in a statistics table. |
| `data.cover(percent, condition, label)` | Declare a coverage requirement. |
| `data.target(score, label="")` | Report a score for targeted search to maximize. |

The low-level methods, for making primitive choices, are in
[Writing strategies: the low-level API](internals.md).

## Exploring strategies

### `example`

```mojo-sig
example(strategy, seed: Optional[UInt64] = None) -> S.Value
```

One random value from `strategy`, for exploring interactively; not for use
in tests.

### `find`

```mojo-sig
find(strategy, condition, settings=Settings(max_examples=2000, database=None)) -> S.Value
```

The simplest value satisfying `condition` (`def(S.Value) raises -> Bool`),
found by searching and then shrinking. Raises `NoSuchExample` if none is
found.

## Results

### `Outcome`

A result type for properties passed to `check` (quickcheck's
`TestResult`):

| Constructor | Meaning |
|---|---|
| `Outcome.passed()` | The property held. |
| `Outcome.discard()` | The input doesn't count, like `assume(False)`. |
| `Outcome.fail(message)` | The property failed; `message` goes in the report. |
| `Outcome.of(condition, message="")` | `passed()` if `condition`, else `fail(message)`. |

`is_failure()` says whether it's a failure. `Outcome` implements the
`Testable` trait (`check_result(self) raises`), which `check` accepts as a
property's return type.

### `run_property`

```mojo-sig
run_property(strategy, test, settings=Settings()) -> PropertyResult[S.Value]
```

Runs `given(strategy, test)` and returns what happened instead of raising
(QuickCheck's `quickCheckResult`). Use `tuples(...)` for several arguments.

### `PropertyResult[T]`

| Member | Description |
|---|---|
| `passed()` | Whether the property held. |
| `counterexample: Optional[T]` | The shrunk failing value (of the first failure). |
| `message: String` | The report `given` would have raised (empty if it passed). |
| `blob: String` | A string for `Settings(reproduce=...)` that replays the counterexample. |
| `report: RunReport` | Counts, statistics, and the raw failures. |

### `RunReport`

| Field | Description |
|---|---|
| `valid`, `invalid`, `overrun` | Counts of test cases by status. |
| `calls` | Total calls of the test function. |
| `shrinks` | Successful shrinks. |
| `seed` | The run's random seed. |
| `exit_reason` | Why generation stopped. |
| `failures`, `errors` | The shrunk failures, one per distinct origin, and their messages. |
| `statistics: Statistics` | Events, tables, and coverage from the generate phase. |
| `coverage_error` | Why the coverage requirements failed, if they did. |

### `expect_failure`

```mojo-sig
expect_failure(test: def() raises) raises -> String
```

Runs `test`, which should fail with a proptest failure (a falsifying
example, several distinct failures, or insufficient coverage), and returns
its report. Raises if `test` passes; re-raises any other error
(QuickCheck's `expectFailure`).

## Debugging

### `before_minimal_test_case`

```mojo-sig
before_minimal_test_case(name: String)
```

Called just before the final replay of each shrunk failure, and before a
`reproduce=` replay. It does nothing; it's a place for a debugger
breakpoint. `name` is the test's location.

## Failure messages

| Message starts with | Meaning |
|---|---|
| `Falsifying example (location):` | The test failed; the shrunk input follows. |
| `proptest found N distinct failures.` | Several bugs, each reported in turn. |
| `Falsifying explicit example` | An explicit example failed. |
| `Insufficient coverage` | A coverage requirement failed under `check_coverage`. |
| `FailedHealthCheck:` | A health check failed; see [Suppress a health check](../how-to/suppress-healthchecks.md). |
| `DeadlineExceeded` | An example ran longer than the `deadline`. |
| `Flaky:` | A failure didn't reproduce, or timings were unreliable. |
| `FlakyStrategyDefinition:` | Data generation wasn't deterministic. |
| `DidNotReproduce:` | The `reproduce=` example no longer fails. |
| `NoSuchExample` | `find` found no value satisfying its condition. |
| `InvalidArgument:` | A strategy was given invalid arguments. |
