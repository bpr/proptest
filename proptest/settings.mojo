# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Settings that control a property-based test run.

Port of `hypothesis._settings`. Hypothesis's settings are a decorator with
profiles; proptest's are a plain struct passed to `given(...)`:

```mojo
given(integers(), test, settings=Settings(max_examples=1000))
```

Supported: `max_examples`, `seed`/`derandomize`, `database`, `phases`,
`verbosity`, `report_multiple_bugs`, `suppress_health_check`,
`stateful_step_count`, `max_shrinks`, `deadline`, `reproduce`,
`show_statistics` and `check_coverage` (from QuickCheck). Not
supported: `backend`. Settings left at their defaults can be changed through
environment variables (like a Hypothesis settings profile):
`PROPTEST_MAX_EXAMPLES`, `PROPTEST_SEED`, `PROPTEST_VERBOSITY`
(`quiet`, `normal`, `verbose`, `debug`), and `PROPTEST_DATABASE`
(a directory, or `none` to disable it).
"""

from std.os import getenv


struct Verbosity(
    Comparable, Copyable, Equatable, TrivialRegisterPassable, Writable
):
    """How much a test run prints."""

    var value: Int
    comptime quiet = Verbosity(0)
    comptime normal = Verbosity(1)
    comptime verbose = Verbosity(2)
    comptime debug = Verbosity(3)

    def __init__(out self, value: Int):
        self.value = value

    def __eq__(self, other: Self) -> Bool:
        return self.value == other.value

    def __lt__(self, other: Self) -> Bool:
        return self.value < other.value

    def write_to(self, mut writer: Some[Writer]):
        if self.value == 0:
            writer.write("quiet")
        elif self.value == 1:
            writer.write("normal")
        elif self.value == 2:
            writer.write("verbose")
        else:
            writer.write("debug")


struct Phases(Copyable, Writable):
    """Which phases of a test run are enabled (Hypothesis's `Phase`)."""

    var explicit: Bool
    """Run the examples given with `examples=`."""
    var reuse: Bool
    """Replay failing examples saved in the database."""
    var generate: Bool
    """Generate new examples."""
    var target: Bool
    """Hill-climb on `data.target(...)` scores."""
    var shrink: Bool
    """Shrink failing examples."""
    var explain: Bool
    """After shrinking, find arguments that can vary without changing the
    failure, and say so in the report."""

    def __init__(
        out self,
        *,
        explicit: Bool = True,
        reuse: Bool = True,
        generate: Bool = True,
        target: Bool = True,
        shrink: Bool = True,
        explain: Bool = True,
    ):
        self.explicit = explicit
        self.reuse = reuse
        self.generate = generate
        self.target = target
        self.shrink = shrink
        self.explain = explain

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "Phases(explicit=",
            self.explicit,
            ", reuse=",
            self.reuse,
            ", generate=",
            self.generate,
            ", target=",
            self.target,
            ", shrink=",
            self.shrink,
            ", explain=",
            self.explain,
            ")",
        )


struct HealthCheck(Copyable, Equatable, TrivialRegisterPassable, Writable):
    """Health checks that can be suppressed."""

    var value: Int
    comptime filter_too_much = HealthCheck(0)
    comptime data_too_large = HealthCheck(1)
    comptime large_base_example = HealthCheck(2)
    comptime too_slow = HealthCheck(3)

    def __init__(out self, value: Int):
        self.value = value

    def __eq__(self, other: Self) -> Bool:
        return self.value == other.value

    def write_to(self, mut writer: Some[Writer]):
        if self.value == 0:
            writer.write("filter_too_much")
        elif self.value == 1:
            writer.write("data_too_large")
        elif self.value == 2:
            writer.write("large_base_example")
        else:
            writer.write("too_slow")


struct Confidence(Copyable, TrivialRegisterPassable, Writable):
    """How sure a coverage check must be (QuickCheck's `Confidence`).

    A requirement passes once proptest is confident it holds at least
    `tolerance` times over, and fails once it is confident it doesn't hold;
    each conclusion is wrong with probability about `1 / certainty`."""

    var certainty: Float64
    var tolerance: Float64

    def __init__(
        out self, *, certainty: Float64 = 1e9, tolerance: Float64 = 0.9
    ):
        self.certainty = certainty
        self.tolerance = tolerance

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "Confidence(certainty=",
            self.certainty,
            ", tolerance=",
            self.tolerance,
            ")",
        )


comptime DEFAULT_DATABASE = ".proptest/examples"


struct Settings(Copyable, Writable):
    """Configuration for one property-based test."""

    var max_examples: Int
    """How many valid examples to try before passing."""
    var seed: Optional[UInt64]
    """Seed for the random generator (random per run when unset)."""
    var derandomize: Bool
    """Use a seed derived from the test's database key, so runs repeat."""
    var database: Optional[String]
    """Directory for saved failing examples (`None` disables it)."""
    var database_key: String
    """Identifies the test in the database; `given` fills this in from the
    calling location when it is empty."""
    var phases: Phases
    var verbosity: Verbosity
    var report_multiple_bugs: Bool
    """Report every distinct failure found, not just one."""
    var suppress_health_check: List[HealthCheck]
    var stateful_step_count: Int
    """Maximum number of steps in a stateful test run."""
    var max_shrinks: Int
    """Stop shrinking after this many successful shrinks."""
    var print_blob: Bool
    """Print a blob that `reproduce=` accepts, to replay the failure."""
    var deadline: Optional[Float64]
    """Fail examples whose test body takes longer than this many
    milliseconds (Hypothesis's default is 200 ms; `None` disables it).
    Time spent drawing data is not counted."""
    var reproduce: Optional[String]
    """A blob printed with a failure: replay exactly that example instead of
    searching (Hypothesis's `@reproduce_failure`)."""
    var show_statistics: Bool
    """Print the run's statistics: events, tables and coverage
    (Hypothesis's `--hypothesis-show-statistics`). Also printed at
    verbose verbosity."""
    var check_coverage: Optional[Confidence]
    """Check `cover` requirements statistically: keep generating past
    `max_examples` until each is known to hold or not, and fail if one
    doesn't (QuickCheck's `checkCoverage`)."""

    def __init__(
        out self,
        *,
        max_examples: Int = 100,
        seed: Optional[UInt64] = None,
        derandomize: Bool = False,
        database: Optional[String] = String(DEFAULT_DATABASE),
        database_key: String = "",
        var phases: Phases = Phases(),
        verbosity: Verbosity = Verbosity.normal,
        report_multiple_bugs: Bool = True,
        var suppress_health_check: List[HealthCheck] = List[HealthCheck](),
        stateful_step_count: Int = 50,
        max_shrinks: Int = 500,
        print_blob: Bool = False,
        deadline: Optional[Float64] = 200.0,
        reproduce: Optional[String] = None,
        show_statistics: Bool = False,
        var check_coverage: Optional[Confidence] = None,
    ):
        self.max_examples = max_examples
        self.seed = seed
        self.derandomize = derandomize
        self.database = database
        self.database_key = database_key
        self.phases = phases^
        self.verbosity = verbosity
        self.report_multiple_bugs = report_multiple_bugs
        self.suppress_health_check = suppress_health_check^
        self.stateful_step_count = stateful_step_count
        self.max_shrinks = max_shrinks
        self.print_blob = print_blob
        self.deadline = deadline
        self.reproduce = reproduce
        self.show_statistics = show_statistics
        self.check_coverage = check_coverage^

    def with_env_overrides(self) -> Self:
        """These settings, updated from `PROPTEST_*` environment variables.

        Like a Hypothesis settings profile, the environment only changes
        settings that are still at their defaults: a value set explicitly in
        the code wins."""
        var s = self.copy()
        var me = getenv("PROPTEST_MAX_EXAMPLES")
        if me.byte_length() > 0 and s.max_examples == 100:
            try:
                s.max_examples = Int(me)
            except:
                pass
        var seed = getenv("PROPTEST_SEED")
        if seed.byte_length() > 0 and not s.seed:
            try:
                s.seed = UInt64(Int(seed))
            except:
                pass
        var v = getenv("PROPTEST_VERBOSITY")
        if s.verbosity == Verbosity.normal:
            if v == "quiet":
                s.verbosity = Verbosity.quiet
            elif v == "verbose":
                s.verbosity = Verbosity.verbose
            elif v == "debug":
                s.verbosity = Verbosity.debug
        var db = getenv("PROPTEST_DATABASE")
        if s.database and s.database.value() == DEFAULT_DATABASE:
            if db == "none" or db == "None":
                s.database = None
            elif db.byte_length() > 0:
                s.database = db
        return s^

    def deadline_ns(self) -> Int:
        """The deadline in nanoseconds, or -1 if there is none."""
        if self.deadline:
            return Int(self.deadline.value() * 1_000_000)
        return -1

    def suppressed(self, hc: HealthCheck) -> Bool:
        for h in self.suppress_health_check:
            if h == hc:
                return True
        return False

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "Settings(max_examples=",
            self.max_examples,
            ", derandomize=",
            self.derandomize,
            ", verbosity=",
            self.verbosity,
            ", ",
            self.phases,
            ")",
        )
