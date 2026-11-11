# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The test runner: generation, the database, targeting and shrinking.

Port of `hypothesis.internal.conjecture.engine.ConjectureRunner` (with parts
of `optimiser.py`). A run proceeds in phases:

1. **reuse**: replay failing examples saved in the database;
2. **generate**: run the simplest example, then random ones, each followed
   by a few *mutations* that duplicate a span's choices elsewhere;
3. **target**: hill-climb on scores reported with `data.target(...)`;
4. **shrink**: minimize each distinct failure (see `shrinker.mojo`).

Differences from Hypothesis: there is no `DataTree`, so novelty is
approximated by the result cache (a run that repeats an already-seen
choice sequence is counted as a duplicate, and many consecutive
duplicates end generation as "exhausted"); there are no deadlines, and
no alternative backends.
"""

from std.memory import ArcPointer
from std.collections import Dict
from std.time import perf_counter_ns
from std.hash import hash

from proptest.internal.choice import (
    ChoiceValue,
    ChoiceNode,
    Constraints,
    INTEGER,
    FLOAT,
    sort_key_less,
    choice_permitted,
)
from proptest.internal.data import (
    ConjectureData,
    ConjectureResult,
    Result,
    Status,
    is_stop_test,
    is_unsatisfied_assumption,
    BUFFER_SIZE,
)
from proptest.internal.provider import Provider, Constants
from proptest.internal.random import Random
from proptest.settings import Settings, Verbosity, HealthCheck
from proptest.database import ExampleDatabase
from proptest.internal.datatree import DataTree
from proptest.internal.fork import (
    ForkLog,
    LogReader,
    LOG_SIZE,
    SIGALRM,
    map_shared,
    unmap_shared,
    fork_process,
    wait_process,
    prepare_child,
    exit_child,
    exited,
    exit_code,
    term_signal,
    signal_name,
)
from proptest.internal.pareto import ParetoFront
from proptest.internal.statistics import (
    Statistics,
    COVERAGE_UNDECIDED,
    COVERAGE_SUFFICIENT,
    COVERAGE_INSUFFICIENT,
)

comptime CACHE_SIZE = 10000
comptime MIN_TEST_CALLS = 10
comptime MAX_SHRINKING_SECONDS = 300


def interesting_origin(msg: String) -> String:
    """A key identifying "the same bug" across test cases.

    Hypothesis uses the exception type and the location it was raised from.
    Mojo errors carry only a message, but the standard `assert_*` functions
    (and `proptest.fail`) prefix it with `At <file>:<line>:<col>: `, so the
    origin is that location plus the error kind, ignoring the rest of the
    message (which usually contains the failing values). Errors without a
    location all share one origin.
    """
    if msg.startswith("At "):
        # "At path:line:col: Kind: details" -> "At path:line:col: Kind"
        var parts = msg.split(": ")
        if len(parts) >= 2:
            var kind = String(parts[1]).split(":")[0]
            return String(parts[0], ": ", kind)
        return msg
    if msg.startswith("Unsatisfiable") or msg.startswith("FailedHealthCheck"):
        return msg
    if msg.startswith("DeadlineExceeded"):
        return "DeadlineExceeded"
    return "Error"


comptime _INVALID_PREFIX = "invalid because: "

comptime COVERAGE_MAX_EXAMPLES = 100_000
"""Give up deciding coverage after this many valid examples; the observed
share then decides."""


struct RunReport(Copyable):
    """What a run found."""

    var failures: List[Result]
    """The shrunk failing examples, one per distinct origin."""
    var errors: List[String]
    """The error message each failure raised (parallel to `failures`)."""
    var valid: Int
    var invalid: Int
    var overrun: Int
    var calls: Int
    var shrinks: Int
    var exit_reason: String
    var seed: UInt64
    var statistics: Statistics
    """Events, tables and coverage seen in the generate phase."""
    var coverage_error: String
    """Why the coverage requirements failed (empty if they didn't)."""

    def __init__(out self):
        self.failures = List[Result]()
        self.errors = List[String]()
        self.valid = 0
        self.invalid = 0
        self.overrun = 0
        self.calls = 0
        self.shrinks = 0
        self.exit_reason = String()
        self.seed = 0
        self.statistics = Statistics()
        self.coverage_error = String()


struct ConjectureRunner[F: def(mut ConjectureData) raises](Movable):
    """Runs a test function repeatedly, looking for and minimizing failures."""

    var test_fn: Self.F
    var settings: Settings
    var random: Random
    var seed: UInt64
    var constants: ArcPointer[Constants]
    var cache: Dict[List[ChoiceValue], Result]
    var call_count: Int
    var valid_count: Int
    var invalid_count: Int
    var overrun_count: Int
    var duplicate_count: Int
    var consecutive_duplicates: Int
    var misaligned_count: Int
    var next_id: Int
    var interesting: Dict[String, Result]
    """The simplest failing example found so far, per origin."""
    var interesting_errors: Dict[String, String]
    var origins: List[String]
    var first_bug_found_at: Int
    var last_bug_found_at: Int
    var best_targets: Dict[String, Result]
    var db: Optional[ExampleDatabase]
    var db_key: String
    var exit_reason: String
    var shrinks: Int
    var health_check_done: Bool
    var health_overruns: Int
    """Overruns from data too large (not from choice limits)."""
    var health_draw_ns: Int
    """Time spent generating data while the health checks are running."""
    var flaky_strategy: String
    """Set when data generation was found to be non-deterministic."""
    var start_ns: Int
    var tree: DataTree
    var tree_provider: Provider
    var saved: List[List[ChoiceValue]]
    """Choice sequences saved to the database during this run."""
    var arg_comments: Dict[String, Dict[Int, String]]
    """Explain-phase comments for each origin's final example."""
    var explain_notes: Dict[String, String]
    var front: Optional[ParetoFront]
    """The Pareto front of targeted test cases (kept only with a
    database, as in Hypothesis)."""
    var invalid_reasons: Dict[String, Int]
    """How often each `mark_invalid` reason (filters, `filter(reason=)`)
    rejected a test case."""
    var stats: Statistics
    var collecting_stats: Bool
    """Count test cases into `stats` (only in the generate phase)."""
    var coverage_next_check: Int
    var coverage_verdict: Int
    var fork_warned: Bool

    def __init__(out self, var test_fn: Self.F, settings: Settings):
        self.test_fn = test_fn^
        self.settings = settings.copy()
        var seed: UInt64
        if settings.seed:
            seed = settings.seed.value()
        elif settings.derandomize:
            seed = UInt64(hash(settings.database_key))
        else:
            var r = Random.from_time()
            seed = r.next_u64()
        self.seed = seed
        self.random = Random(seed)
        self.constants = ArcPointer(Constants())
        self.tree = DataTree()
        self.saved = List[List[ChoiceValue]]()
        self.arg_comments = Dict[String, Dict[Int, String]]()
        self.explain_notes = Dict[String, String]()
        if (
            settings.database
            and not settings.derandomize
            and settings.database_key.byte_length() > 0
        ):
            self.front = ParetoFront(Random(seed ^ 0x9E3779B97F4A7C15))
        else:
            self.front = None
        self.tree_provider = Provider(
            Random(seed ^ 0x5DEECE66D), self.constants
        )
        self.cache = Dict[List[ChoiceValue], Result]()
        self.call_count = 0
        self.valid_count = 0
        self.invalid_count = 0
        self.overrun_count = 0
        self.duplicate_count = 0
        self.consecutive_duplicates = 0
        self.misaligned_count = 0
        self.next_id = 1
        self.interesting = Dict[String, Result]()
        self.interesting_errors = Dict[String, String]()
        self.origins = List[String]()
        self.first_bug_found_at = -1
        self.last_bug_found_at = -1
        self.best_targets = Dict[String, Result]()
        if settings.database and not settings.derandomize:
            self.db = ExampleDatabase(settings.database.value())
        else:
            self.db = None
        self.db_key = settings.database_key
        self.exit_reason = String()
        self.shrinks = 0
        self.health_check_done = False
        self.health_overruns = 0
        self.health_draw_ns = 0
        self.flaky_strategy = String()
        self.start_ns = perf_counter_ns()
        self.invalid_reasons = Dict[String, Int]()
        self.stats = Statistics()
        self.collecting_stats = False
        self.coverage_next_check = max(settings.max_examples, 100)
        self.coverage_verdict = COVERAGE_UNDECIDED
        self.fork_warned = False

    # ===------------------------------------------------------------------=== #
    # Running test cases
    # ===------------------------------------------------------------------=== #

    def debug(self, msg: String):
        if self.settings.verbosity >= Verbosity.debug:
            print(msg)

    def new_data(
        mut self,
        var prefix: List[ChoiceValue],
        *,
        max_choices: Int = -1,
        extend_simplest: Bool = False,
    ) -> ConjectureData:
        var provider = Provider(Random(self.random.next_u64()), self.constants)
        var d = ConjectureData(
            prefix^,
            provider^,
            id=self.next_id,
            max_choices=max_choices,
            extend_simplest=extend_simplest,
        )
        self.next_id += 1
        return d^

    def execute(mut self, mut data: ConjectureData) -> String:
        """Run the test function on `data` and freeze it. Returns the error
        message if the test failed (status INTERESTING)."""
        self.call_count += 1
        if self.settings.forks():
            var base = map_shared(LOG_SIZE)
            if base != 0:
                var msg = self._execute_forked(data, base)
                unmap_shared(base, LOG_SIZE)
                if msg:
                    return msg.value()
            # no shared memory or no child process: run it here
            if not self.fork_warned:
                self.fork_warned = True
                print("proptest: warning: can't fork; running in-process")
        return self._execute_here(data)

    def _execute_forked(
        mut self, mut data: ConjectureData, base: Int
    ) -> Optional[String]:
        """Run the test case in a child process, logging to the shared
        memory at `base`, and rebuild it in `data` from the log. None if
        the child couldn't be started."""
        data.fork_log = ForkLog(base, LOG_SIZE)
        var pid = fork_process()
        if pid == 0:
            prepare_child(self.settings.timeout, quiet=not data.is_final)
            var msg = self._execute_here(data)
            data.log_end(msg)
            exit_child(0)
        data.fork_log = None
        if pid < 0:
            return None
        var status = wait_process(pid)
        var reader = LogReader(base)
        try:
            var finished = data.load_fork_log(reader)
            if finished:
                return finished.value()
        except e:
            # what the child sent back is inconsistent: it overwrote its
            # own memory (e.g. a use after free or a double free)
            data.status = Status.INTERESTING
            data.interesting_origin = "Crash: corrupted memory"
            return String(
                "Crash: the test case corrupted its memory (the record of",
                " it sent back by the child process has ",
                e,
                "), in a child process (Settings(fork=True))",
            )
        if reader.overflowed:
            # more than LOG_SIZE bytes of choices and notes
            data.status = Status.OVERRUN
            return String()
        data.status = Status.INTERESTING
        var sig = term_signal(status)
        if sig == SIGALRM and self.settings.timeout:
            data.interesting_origin = "Timeout"
            return String(
                "Timeout: the test case ran longer than ",
                self.settings.timeout.value(),
                " ms (Settings(timeout=...))",
            )
        if sig != 0:
            var name = signal_name(sig)
            data.interesting_origin = String("Crash: ", name)
            return String(
                "Crash: the test case was killed by ",
                name,
                " (signal ",
                sig,
                "), in a child process (Settings(fork=True))",
            )
        var code = exit_code(status) if exited(status) else -1
        data.interesting_origin = String("Crash: exit ", code)
        return String(
            "Crash: the test case exited with status ",
            code,
            " before finishing, in a child process (Settings(fork=True));",
            " a sanitizer's report, if there was one, is printed above",
        )

    def _execute_here(mut self, mut data: ConjectureData) -> String:
        """`execute`, in this process."""
        var error_msg = String()
        try:
            self.test_fn(data)
        except e:
            if data.frozen and is_stop_test(e):
                pass
            elif is_unsatisfied_assumption(e):
                data.status = Status.INVALID
            elif is_stop_test(e):
                # a StopTest from a draw after the test caught it: keep status
                pass
            else:
                error_msg = String(e)
                data.status = Status.INTERESTING
                data.interesting_origin = interesting_origin(error_msg)
        data.freeze()
        return error_msg^

    def test_function(mut self, mut data: ConjectureData) -> Result:
        """Run `data` through the test and record the outcome."""
        var msg = self.execute(data)
        var result = Result(data.as_result())
        if self.settings.verbosity >= Verbosity.debug:
            var line = String("  ", result[].status, " [")
            for k in range(len(result[].nodes)):
                if k > 0:
                    line += ", "
                line += String(result[].nodes[k].value)
            line += "]"
            print(line)
        self._record(result, msg)
        return result^

    def _record(mut self, result: Result, msg: String):
        ref r = result[]
        if r.misaligned:
            self.misaligned_count += 1
        var flaky = self.tree.record(r.nodes, r.status != Status.OVERRUN)
        if flaky.byte_length() > 0 and self.flaky_strategy.byte_length() == 0:
            self.flaky_strategy = flaky
        if not self.health_check_done:
            self.health_draw_ns += r.draw_time_ns
            if r.status == Status.OVERRUN and not r.hit_max_choices:
                self.health_overruns += 1
        var key = r.choices()
        if key in self.cache:
            self.duplicate_count += 1
            self.consecutive_duplicates += 1
        else:
            self.consecutive_duplicates = 0
        if len(self.cache) >= CACHE_SIZE:
            self.cache = Dict[List[ChoiceValue], Result]()
        self.cache[key^] = result
        if self.collecting_stats:
            try:
                self.stats.record(r)
            except:
                pass
        if r.status == Status.VALID:
            self.valid_count += 1
        elif r.status == Status.INVALID:
            self.invalid_count += 1
            for e in r.events:
                if e.startswith(_INVALID_PREFIX):
                    var why = String(e.removeprefix(_INVALID_PREFIX))
                    self.invalid_reasons[why] = (
                        self.invalid_reasons.get(why, 0) + 1
                    )
        elif r.status == Status.OVERRUN:
            self.overrun_count += 1
        if r.status >= Status.VALID:
            for item in r.target_observations.items():
                var label = item.key
                var score = item.value
                try:
                    if label not in self.best_targets:
                        self.best_targets[label] = result
                    else:
                        ref best = self.best_targets[label][]
                        var best_score = best.target_observations[label]
                        if score > best_score or (
                            score == best_score
                            and sort_key_less(r.nodes, best.nodes)
                        ):
                            self.best_targets[label] = result
                except:
                    pass
        if len(r.target_observations) > 0 and self.front:
            if self.front.value().add(result):
                self.db.value().save(self.pareto_key(), r.choices())
            self.sync_front()
        if r.status == Status.INTERESTING:
            var origin = r.interesting_origin
            if origin not in self.interesting:
                self.origins.append(origin)
                self.last_bug_found_at = self.call_count
                if self.first_bug_found_at < 0:
                    self.first_bug_found_at = self.call_count
                self.interesting[origin] = result
                self.interesting_errors[origin] = msg
                self.save_choices(r.choices())
            else:
                try:
                    ref existing = self.interesting[origin][]
                    if sort_key_less(r.nodes, existing.nodes):
                        self.interesting[origin] = result
                        self.interesting_errors[origin] = msg
                        self.save_choices(r.choices())
                except:
                    pass

    def cached_test_function(
        mut self,
        choices: List[ChoiceValue],
        *,
        extend: Int = 0,
        extend_simplest: Bool = False,
    ) -> Result:
        """Run the test on exactly `choices` (cached). With `extend > 0`, up
        to that many extra random choices may be drawn past the end; with
        `extend < 0`, any number. `extend_simplest` extends with the simplest
        choices instead of random ones."""
        if extend == 0 and not extend_simplest:
            try:
                if choices in self.cache:
                    return self.cache[choices]
                var used = self.tree.simulate(choices)
                if used and used.value() in self.cache:
                    return self.cache[used.value()]
            except:
                pass
        var max_choices = -1
        if not extend_simplest:
            if extend >= 0:
                max_choices = len(choices) + extend
        var data = self.new_data(
            choices.copy(),
            max_choices=max_choices,
            extend_simplest=extend_simplest,
        )
        var result = self.test_function(data)
        if extend == 0 and not extend_simplest:
            if len(self.cache) < CACHE_SIZE:
                self.cache[choices.copy()] = result
        return result^

    def pareto_key(self) -> String:
        return self.db_key + ".pareto"

    def sync_front(mut self):
        """Delete members evicted from the Pareto front from the database."""
        if not self.front:
            return
        var evicted = self.front.value().evicted.copy()
        self.front.value().evicted = List[List[ChoiceValue]]()
        if self.db:
            for c in evicted:
                self.db.value().delete(self.pareto_key(), c)

    def save_choices(mut self, choices: List[ChoiceValue]):
        if self.db and self.db_key.byte_length() > 0:
            self.db.value().save(self.db_key, choices)
            self.saved.append(choices.copy())

    def prune_saved(mut self, keep: List[List[ChoiceValue]]):
        """Delete the examples saved during this run except those in `keep`
        (the final shrunk failures), so the database holds one example per
        bug."""
        var saved = self.saved.copy()
        for c in saved:
            var kept = False
            for k in keep:
                if k == c:
                    kept = True
                    break
            if not kept:
                self.delete_choices(c)
        self.saved = List[List[ChoiceValue]]()

    def delete_choices(mut self, choices: List[ChoiceValue]):
        if self.db and self.db_key.byte_length() > 0:
            self.db.value().delete(self.db_key, choices)

    # ===------------------------------------------------------------------=== #
    # Phases
    # ===------------------------------------------------------------------=== #

    def reuse_existing_examples(mut self):
        """Replay saved failures; drop those that no longer fail."""
        if not self.settings.phases.reuse or not self.db:
            return
        if self.db_key.byte_length() == 0:
            return
        var saved = self.db.value().fetch(self.db_key)
        # simplest first (shortlex on the serialized form is a fine proxy)
        for i in range(1, len(saved)):
            var j = i
            while j > 0 and len(saved[j]) < len(saved[j - 1]):
                saved.swap_elements(j, j - 1)
                j -= 1
        for choices in saved:
            var result = self.cached_test_function(choices)
            if result[].status != Status.INTERESTING:
                self.delete_choices(choices)
            else:
                # prunable once a simpler example for its bug is known
                self.saved.append(choices.copy())
        if len(self.interesting) > 0:
            self.debug(
                String("Reused ", len(self.interesting), " failing example(s)")
            )
            return
        # Seed targeting with the Pareto front saved by earlier runs.
        var desired = max(2, (self.settings.max_examples + 9) // 10)
        if self.front and len(saved) < desired:
            var pareto = self.db.value().fetch(self.pareto_key())
            for i in range(1, len(pareto)):
                var j = i
                while j > 0 and len(pareto[j]) < len(pareto[j - 1]):
                    pareto.swap_elements(j, j - 1)
                    j -= 1
            var n = 0
            for choices in pareto:
                if n >= desired - len(saved):
                    break
                n += 1
                var result = self.cached_test_function(choices)
                if not self.front.value().contains(result):
                    self.db.value().delete(self.pareto_key(), choices)
                if result[].status == Status.INTERESTING:
                    break

    def should_generate_more(mut self) -> Bool:
        if (
            self.valid_count >= self.settings.max_examples
            and not self._coverage_wants_more()
        ):
            return False
        if self.tree.is_exhausted():
            return False
        var invalid_threshold = 1000 + 10 * self.settings.max_examples
        if self.invalid_count + self.overrun_count > invalid_threshold:
            return False
        if self.consecutive_duplicates > max(
            100, 2 * self.settings.max_examples
        ):
            return False
        if len(self.interesting) == 0:
            return True
        if (
            not self.settings.phases.shrink
            or not self.settings.report_multiple_bugs
        ):
            return False
        # keep looking for other bugs for a while after the first one
        return self.call_count < MIN_TEST_CALLS or self.call_count < min(
            self.first_bug_found_at + 1000, self.last_bug_found_at * 2
        )

    def _top_invalid_reasons(self) -> String:
        """The most common reasons test cases were rejected, for the
        `filter_too_much` message."""
        var keys = List[String]()
        for item in self.invalid_reasons.items():
            var j = len(keys)
            try:
                while j > 0 and self.invalid_reasons[keys[j - 1]] < item.value:
                    j -= 1
            except:
                pass
            keys.insert(j, item.key)
        if len(keys) == 0:
            return String()
        var out = String(" Most rejections were by:")
        for k in range(min(3, len(keys))):
            out += String(
                " ",
                keys[k],
                " (",
                self.invalid_reasons.get(keys[k], 0),
                ")",
                ";" if k + 1 < min(3, len(keys)) else ".",
            )
        return out^

    def _coverage_wants_more(mut self) -> Bool:
        """With `check_coverage`, whether the coverage requirements are
        still undecided, so generation should go on past `max_examples`.
        Checked at doubling numbers of examples, as QuickCheck does."""
        if (
            not self.settings.check_coverage
            or len(self.stats.cover_order) == 0
            or self.coverage_verdict != COVERAGE_UNDECIDED
            or len(self.interesting) > 0
        ):
            return False
        if self.stats.valid < self.coverage_next_check:
            return True
        try:
            var v = self.stats.coverage_verdict(
                self.settings.check_coverage.value()
            )
            if v != COVERAGE_UNDECIDED:
                self.coverage_verdict = v
                return False
        except:
            return False
        self.coverage_next_check *= 2
        return self.stats.valid < COVERAGE_MAX_EXAMPLES

    def _health_check(mut self) raises:
        """Fail early if the strategy mostly produces invalid data."""
        if self.health_check_done:
            return
        if self.valid_count >= 10 or len(self.interesting) > 0:
            self.health_check_done = True
            return
        if self.invalid_count >= 50 and not self.settings.suppressed(
            HealthCheck.filter_too_much
        ):
            raise Error(
                String(
                    "FailedHealthCheck: It looks like this test is filtering",
                    " out a lot of inputs. ",
                    self.valid_count,
                    " inputs were generated successfully, while ",
                    self.invalid_count,
                    " inputs were filtered out. Try to construct values that",
                    " satisfy the conditions directly instead of using",
                    " filter() or assume().",
                    self._top_invalid_reasons(),
                    " (suppress with HealthCheck.filter_too_much)",
                )
            )
        if self.health_overruns >= 20 and not self.settings.suppressed(
            HealthCheck.data_too_large
        ):
            raise Error(
                String(
                    "FailedHealthCheck: The test cases being generated are",
                    " too large: ",
                    self.health_overruns,
                    " of them exceeded the maximum size. Try decreasing the",
                    " size of the data being generated (e.g. with max_size).",
                    " (suppress with HealthCheck.data_too_large)",
                )
            )
        var deadline = self.settings.deadline_ns()
        var limit = max(
            1_000_000_000, 5 * (deadline if deadline > 0 else 6_000_000_000)
        )
        if self.health_draw_ns > limit and not self.settings.suppressed(
            HealthCheck.too_slow
        ):
            raise Error(
                String(
                    "FailedHealthCheck: Input generation is slow: only ",
                    self.valid_count,
                    " valid inputs after ",
                    Float64(self.health_draw_ns) / 1e9,
                    " seconds of drawing data. Try generating smaller or",
                    " simpler data. (suppress with HealthCheck.too_slow)",
                )
            )

    def generate_new_examples(mut self) raises:
        if not self.settings.phases.generate:
            return
        if len(self.interesting) > 0:
            return
        # The simplest possible example first.
        var zero = self.cached_test_function(
            List[ChoiceValue](), extend_simplest=True
        )
        if (
            zero[].status == Status.OVERRUN
            or (
                zero[].status == Status.VALID
                and zero[].length * 2 > BUFFER_SIZE
            )
        ) and not self.settings.suppressed(HealthCheck.large_base_example):
            raise Error(
                "FailedHealthCheck: The smallest natural input for this test"
                " is very large. This makes it difficult to generate good"
                " inputs and to shrink failing ones. (suppress with"
                " HealthCheck.large_base_example)"
            )
        var next_optimize_at = max(self.settings.max_examples // 2, 10)
        # Hypothesis's "small examples first": early test cases are limited
        # to a few times the size of the simplest completion of their prefix,
        # so simple bugs are found with simple inputs.
        var small_cap = min(self.settings.max_examples // 10, 50)
        var consecutive_zero_extend_invalid = 0
        self.collecting_stats = True
        while self.should_generate_more():
            self.check_flaky()
            self._health_check()
            var prefix = self.tree.generate_novel_prefix(self.tree_provider)
            var max_choices = -1
            if (
                self.valid_count <= small_cap
                and self.call_count <= 5 * small_cap
                and len(self.interesting) == 0
                and consecutive_zero_extend_invalid < 5
            ):
                var minimal = self.cached_test_function(
                    prefix, extend_simplest=True
                )
                if minimal[].status < Status.VALID:
                    consecutive_zero_extend_invalid += 1
                    continue
                consecutive_zero_extend_invalid = 0
                var extension = len(minimal[].nodes) - len(prefix)
                max_choices = len(prefix) + max(extension, 1) * 5
                # Choose the random continuation now, through the tree, and
                # skip it if it only leads to known test cases (Hypothesis's
                # `simulate_test_function` check).
                var trial = self.tree.extend_randomly(
                    prefix, self.tree_provider, max_choices
                )
                if not trial:
                    continue
                prefix = trial.value().copy()
            var data = self.new_data(prefix^, max_choices=max_choices)
            var result = self.test_function(data)
            self._health_check()
            self.generate_mutations_from(result)
            if (
                self.settings.phases.target
                and len(self.best_targets) > 0
                and len(self.interesting) == 0
                and self.valid_count >= next_optimize_at
            ):
                # hill climbing would skew the statistics
                self.collecting_stats = False
                self.optimize_targets(max_calls=self.settings.max_examples)
                self.collecting_stats = True
                next_optimize_at = self.valid_count + max(
                    self.settings.max_examples // 2, 10
                )
        self.collecting_stats = False
        if self.tree.is_exhausted() or self.consecutive_duplicates > max(
            100, 2 * self.settings.max_examples
        ):
            self.exit_reason = "exhausted the search space"
        elif self.valid_count >= self.settings.max_examples:
            self.exit_reason = "max_examples"

    def generate_mutations_from(mut self, var result: Result):
        """Try copying the choices of one span over another span with the
        same label (port of `generate_mutations_from`)."""
        if result[].status < Status.INVALID:
            return
        var initial_calls = self.call_count
        var failed = 0
        while (
            self.should_generate_more()
            and self.call_count <= initial_calls + 5
            and failed <= 5
        ):
            ref spans = result[].spans
            # group spans by label
            var groups = Dict[UInt64, List[Int]]()
            for i in range(len(spans)):
                var lbl = spans[i].label
                try:
                    if lbl in groups:
                        groups[lbl].append(i)
                    else:
                        var l = List[Int]()
                        l.append(i)
                        groups[lbl] = l^
                except:
                    pass
            var candidates = List[List[Int]]()
            for g in groups.values():
                if len(g) >= 2:
                    candidates.append(g.copy())
            if len(candidates) == 0:
                return
            ref group = candidates[
                Int(self.random.below(UInt64(len(candidates))))
            ]
            var a = Int(self.random.below(UInt64(len(group))))
            var b = Int(self.random.below(UInt64(len(group) - 1)))
            if b >= a:
                b += 1
            var s1 = spans[group[a]].copy()
            var s2 = spans[group[b]].copy()
            if s1.start > s2.start:
                var t = s1.copy()
                s1 = s2.copy()
                s2 = t^
            var choices = result[].choices()
            var attempt = List[ChoiceValue]()
            if s1.start <= s2.start and s2.end <= s1.end:
                # nested: replace the outer span with the inner one
                for k in range(s2.start):
                    attempt.append(choices[k].copy())
                for k in range(s1.start, len(choices)):
                    attempt.append(choices[k].copy())
            else:
                var use_first = self.random.getrandbits(1) == 0
                var rs = s1.start if use_first else s2.start
                var re = s1.end if use_first else s2.end
                for k in range(s1.start):
                    attempt.append(choices[k].copy())
                for k in range(rs, re):
                    attempt.append(choices[k].copy())
                for k in range(s1.end, s2.start):
                    attempt.append(choices[k].copy())
                for k in range(rs, re):
                    attempt.append(choices[k].copy())
                for k in range(s2.end, len(choices)):
                    attempt.append(choices[k].copy())
            var new = self.cached_test_function(attempt)
            if new[].status == Status.OVERRUN:
                failed += 1
                continue
            if new[].status >= result[].status and new[].choices() != choices:
                result = new
                failed = 0
            else:
                failed += 1

    def optimize_targets(mut self, max_calls: Int):
        """Hill-climb each target score (port of `Optimiser.hill_climb`):
        repeatedly nudge individual integer and float choices of the best
        example in the direction that increases its score."""
        var labels = List[String]()
        for k in self.best_targets.keys():
            labels.append(k)
        var budget_end = self.call_count + max_calls
        for label in labels:
            var improved = True
            while improved and self.call_count < budget_end:
                improved = False
                if len(self.interesting) > 0:
                    return
                var best: Result
                try:
                    best = self.best_targets[label]
                except:
                    break
                var n = len(best[].nodes)
                for i in range(n):
                    if (
                        self.call_count >= budget_end
                        or len(self.interesting) > 0
                    ):
                        return
                    ref node = best[].nodes[i]
                    if node.was_forced:
                        continue
                    var kind = node.value.kind
                    if kind != INTEGER and kind != FLOAT:
                        continue
                    for sign in [1, -1]:
                        if self._climb(label, i, sign):
                            improved = True

    def _score(self, r: Result, label: String) -> Optional[Float64]:
        try:
            if label in r[].target_observations:
                return r[].target_observations[label]
        except:
            pass
        return None

    def _climb(mut self, label: String, i: Int, sign: Int) -> Bool:
        """Try moving choice `i` of the best example by increasing steps
        (k = 1, 2, 4, ...) in direction `sign` while the score improves."""
        var any_improved = False
        var step = 1
        while step < (1 << 62):
            var best: Result
            try:
                best = self.best_targets[label]
            except:
                return any_improved
            if i >= len(best[].nodes):
                return any_improved
            var old_score = self._score(best, label)
            if not old_score:
                return any_improved
            ref node = best[].nodes[i]
            var v = node.value.copy()
            if v.kind == INTEGER:
                v.i += Int128(sign * step)
            elif v.kind == FLOAT:
                v.f += Float64(sign * step)
            else:
                return any_improved
            if not choice_permitted(v, node.constraints):
                return any_improved
            var choices = best[].choices()
            choices[i] = v^
            var r = self.cached_test_function(choices, extend=8)
            if r[].status == Status.INTERESTING:
                return True
            var s = self._score(r, label)
            if not s or s.value() <= old_score.value():
                return any_improved
            any_improved = True
            step *= 2
        return any_improved

    def check_flaky(self) raises:
        """Raise if data generation was found to be non-deterministic."""
        if self.flaky_strategy.byte_length() > 0:
            raise Error(
                String(
                    (
                        "FlakyStrategyDefinition: Inconsistent data generation!"
                        " Data generation behaved differently between different"
                        " runs ("
                    ),
                    self.flaky_strategy,
                    (
                        "). Is the strategy or test depending on external"
                        " state, such as a captured mutable variable or the"
                        " clock?"
                    ),
                )
            )

    def run(mut self) raises:
        """Run the reuse, generate and target phases. Shrinking is done by
        the caller (see `proptest.core`), which owns the shrinker."""
        self.reuse_existing_examples()
        self.generate_new_examples()
        if (
            self.settings.phases.target
            and len(self.best_targets) > 0
            and len(self.interesting) == 0
        ):
            self.optimize_targets(max_calls=self.settings.max_examples)
        self.check_flaky()
        if len(self.interesting) == 0 and self.valid_count == 0:
            if self.settings.max_examples > 0 and self.settings.phases.generate:
                raise Error(
                    String(
                        "Unsatisfiable: Unable to satisfy assumptions of the",
                        " test. ",
                        self.invalid_count,
                        " examples were invalid and ",
                        self.overrun_count,
                        " overran.",
                    )
                )
