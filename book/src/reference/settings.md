# Settings

## `Settings`

```mojo-sig
Settings(
    *,
    max_examples: Int = 100,
    seed: Optional[UInt64] = None,
    derandomize: Bool = False,
    database: Optional[String] = ".proptest/examples",
    database_key: String = "",
    phases: Phases = Phases(),
    verbosity: Verbosity = Verbosity.normal,
    report_multiple_bugs: Bool = True,
    suppress_health_check: List[HealthCheck] = [],
    stateful_step_count: Int = 50,
    max_shrinks: Int = 500,
    print_blob: Bool = False,
    deadline: Optional[Float64] = 200.0,
    reproduce: Optional[String] = None,
    show_statistics: Bool = False,
    check_coverage: Optional[Confidence] = None,
)
```

| Setting | Description |
|---|---|
| `max_examples` | How many valid test cases to run before passing. |
| `seed` | The random seed. Random for each run when unset. |
| `derandomize` | Derive the seed from the test's database key, so every run of the test is the same. |
| `database` | The directory for saved failures; `None` disables the database. |
| `database_key` | The test's key in the database. Filled in from the test's source location when empty. |
| `phases` | Which phases of the run are enabled; see `Phases`. |
| `verbosity` | How much to print; see `Verbosity`. |
| `report_multiple_bugs` | Report every distinct failure found, rather than just one. |
| `suppress_health_check` | Health checks not to run. |
| `stateful_step_count` | The maximum number of steps in a state machine program. |
| `max_shrinks` | Stop shrinking after this many successful shrinks. |
| `print_blob` | Include a `reproduce=` blob in failure reports. |
| `deadline` | Fail a test case whose body (not counting data generation) takes longer than this many milliseconds. `None` disables it. In stateful tests it applies to each step. |
| `reproduce` | A blob from a failure report: replay exactly that test case, without searching or shrinking (Hypothesis's `@reproduce_failure`). |
| `show_statistics` | Print the run's statistics: events, tables, and coverage. |
| `check_coverage` | Check `cover` requirements statistically, generating past `max_examples` until they're settled, and fail if one isn't met (QuickCheck's `checkCoverage`). |

## Environment variables

Settings that a test leaves at their defaults can be changed from the
environment, like a Hypothesis settings profile. A value set in the code
always wins.

| Variable | Setting | Values |
|---|---|---|
| `PROPTEST_MAX_EXAMPLES` | `max_examples` | an integer |
| `PROPTEST_SEED` | `seed` | an integer |
| `PROPTEST_VERBOSITY` | `verbosity` | `quiet`, `normal`, `verbose`, `debug` |
| `PROPTEST_DATABASE` | `database` | a directory, or `none` |

`settings.with_env_overrides()` returns the settings with these applied;
the test runners call it for you.

## `Phases`

```mojo-sig
Phases(*, explicit=True, reuse=True, generate=True, target=True, shrink=True, explain=True)
```

| Phase | Description |
|---|---|
| `explicit` | Run explicit examples. |
| `reuse` | Replay failures saved in the database. |
| `generate` | Generate new test cases. |
| `target` | Hill-climb on `data.target` scores. |
| `shrink` | Shrink failing test cases. |
| `explain` | After shrinking, find arguments that can vary without changing the failure, and mark them in the report. |

## `Verbosity`

| Value | Prints |
|---|---|
| `Verbosity.quiet` | Nothing beyond failures. Coverage warnings are suppressed. |
| `Verbosity.normal` | Failure reports, and warnings about unmet coverage. |
| `Verbosity.verbose` | Also each run's counts and seed, the statistics, and reproduce blobs. |
| `Verbosity.debug` | Also every test case, every shrink, and shrink pass statistics. |

## `HealthCheck`

| Value | Fails when |
|---|---|
| `HealthCheck.filter_too_much` | Most test cases are rejected. |
| `HealthCheck.data_too_large` | Many test cases exceed the choice limit (8,192 choices). |
| `HealthCheck.too_slow` | Generating data is too slow. |
| `HealthCheck.large_base_example` | The simplest input is very large. |

See [Suppress a health check](../how-to/suppress-healthchecks.md).

## `Confidence`

```mojo-sig
Confidence(*, certainty: Float64 = 1e9, tolerance: Float64 = 0.9)
```

How sure a coverage check must be (QuickCheck's `Confidence`). A
requirement of `p`% passes once proptest is confident the true share is at
least `tolerance × p`%, and fails once it is confident the share is below
`p`%. Each conclusion is wrong with probability about `1 / certainty`.
