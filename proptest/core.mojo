# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Running property-based tests: `given`, `find`, `assume` and friends.

Port of `hypothesis.core` and `hypothesis.control`. Hypothesis's `@given`
decorator becomes a function that takes the strategies and the test:

```mojo
from proptest import given, integers, lists
from std.testing import assert_equal

def test_reverse_twice() raises:
    def prop(xs: List[Int]) raises:
        var ys = xs.copy()
        ys.reverse()
        ys.reverse()
        assert_equal(xs, ys)
    given(lists(integers()), prop)
```

If the property fails, `given` shrinks the failure and raises an `Error`
describing the minimal falsifying example and the original error.
"""

from std.reflection import call_location, SourceLocation

from proptest.internal.data import (
    ConjectureData,
    Result,
    Status,
    UNSATISFIED_ASSUMPTION,
)
from proptest.internal.engine import ConjectureRunner, RunReport
from proptest.internal.shrinker import Shrinker
from proptest.internal.choice import ChoiceValue, sort_key_less
from std.memory import ArcPointer
from proptest.internal.provider import Provider, Constants
from proptest.internal.random import Random
from proptest.database import choices_to_string, encode_blob, decode_blob
from std.time import perf_counter_ns
from std.collections import Set
from proptest.settings import Settings, Verbosity, HealthCheck
from proptest.strategies.strategy import Strategy, Drawable, format_value


# ===----------------------------------------------------------------------=== #
# Inside a test
# ===----------------------------------------------------------------------=== #


def assume(condition: Bool) raises:
    """Reject the current example if `condition` is false. Rejected examples
    don't count towards `max_examples`; if too many are rejected the test
    fails a health check."""
    if not condition:
        raise Error(UNSATISFIED_ASSUMPTION)


@always_inline
def fail(msg: String, *, location: Optional[SourceLocation] = None) raises:
    """Fail the test with `msg`. Like the `std.testing` assertions, the error
    records where it was raised, which proptest uses to tell distinct bugs
    apart."""
    var loc = location.value() if location else call_location()
    raise Error(loc.prefix(String("AssertionError: ", msg)))


# ===----------------------------------------------------------------------=== #
# The driver
# ===----------------------------------------------------------------------=== #


def _resolve_settings(settings: Settings, location: SourceLocation) -> Settings:
    var s = settings.with_env_overrides()
    if s.database_key.byte_length() == 0:
        s.database_key = String(location)
    return s^


def run_test[
    F: def(mut ConjectureData) raises
](var test_fn: F, settings: Settings, name: String) raises -> RunReport:
    """Run a test function under the engine: generate, shrink, and replay
    the shrunk failures. Returns the report without raising for failures
    (`given` turns failures into errors)."""
    var runner = ConjectureRunner[F](test_fn^, settings)
    var report = RunReport()
    report.seed = runner.seed
    if settings.reproduce:
        # Replay exactly one example; no search, no shrinking.
        var choices = decode_blob(settings.reproduce.value())
        var n_choices = len(choices)
        var data = runner.new_data(choices^, max_choices=n_choices)
        data.is_final = True
        var msg = runner.execute(data)
        if data.status != Status.INTERESTING:
            raise Error(
                String(
                    "DidNotReproduce: the example given with reproduce= did",
                    " not fail (",
                    data.status,
                    "). The test or its strategies may have changed since",
                    " the blob was printed.",
                )
            )
        report.failures.append(Result(data.as_result()))
        report.errors.append(msg)
        report.calls = 1
        return report^
    runner.run()
    if settings.verbosity >= Verbosity.verbose:
        print(
            String(
                "proptest: ",
                name,
                ": ",
                runner.valid_count,
                " valid, ",
                runner.invalid_count,
                " invalid, ",
                runner.overrun_count,
                " overrun examples in ",
                runner.call_count,
                " calls (seed ",
                runner.seed,
                ")",
            )
        )
    # Pareto optimisation (Hypothesis runs it at the end of the target
    # phase): shrink each member of the front, from the most complex down,
    # keeping only shrinks that dominate it.
    if (
        settings.phases.target
        and runner.front
        and len(runner.best_targets) > 0
        and len(runner.interesting) == 0
    ):
        var seen = Set[List[ChoiceValue]]()
        var i = len(runner.front.value()) - 1
        # Unlike Hypothesis, bound the work: the front can hold hundreds of
        # members when targets compete, and each shrink costs many calls.
        var call_limit = runner.call_count + 10 * settings.max_examples
        while (
            i >= 0
            and len(runner.interesting) == 0
            and runner.call_count < call_limit
        ):
            var n = len(runner.front.value())
            if n == 0:
                break
            i = min(i, n - 1)
            var target = runner.front.value().front[i]
            if target[].choices() in seen:
                i -= 1
                continue
            if settings.verbosity >= Verbosity.debug:
                print("  pareto: shrinking member", i, "of", n)
            var sh = Shrinker[F](runner^, target, pareto=True)
            sh.call_limit = call_limit
            sh.shrink()
            seen.add(sh.target[].choices())
            runner = sh^.release()
            # resume at the largest member simpler than the old target
            i = runner.front.value().bisect_left(target)
    if (
        settings.verbosity >= Verbosity.verbose
        and runner.first_bug_found_at >= 0
    ):
        print(
            String(
                "proptest: first failure at call ",
                runner.first_bug_found_at,
                "; shrinking",
            )
        )
    if settings.phases.shrink:
        var k = 0
        while k < len(runner.origins):
            var origin = runner.origins[k]
            var target = runner.interesting[origin]
            var sh = Shrinker[F](runner^, target)
            sh.shrink()
            if settings.verbosity >= Verbosity.debug:
                sh.report_pass_statistics()
            if settings.phases.explain:
                sh.max_stall = 1 << 60
                sh.explain()
            var best = sh.target
            var comments = sh.arg_comments.copy()
            var explain_note = sh.explain_note
            report.shrinks += sh.shrinks
            runner = sh^.release()
            if len(comments) > 0:
                runner.arg_comments[origin] = comments^
                if explain_note.byte_length() > 0:
                    runner.explain_notes[origin] = explain_note
            # shrinking may have found a simpler example with this origin
            # (but comments from explain only apply to the shrink target)
            if origin in runner.arg_comments:
                runner.interesting[origin] = best
            elif origin in runner.interesting:
                var cur = runner.interesting[origin]
                if sort_key_less(best[].nodes, cur[].nodes):
                    runner.interesting[origin] = best
            if not settings.report_multiple_bugs:
                break
            k += 1
    runner.check_flaky()
    # Keep only the final failures in the database.
    var finals = List[List[ChoiceValue]]()
    for k in range(len(runner.origins)):
        finals.append(runner.interesting[runner.origins[k]][].choices())
    runner.prune_saved(finals)
    # Replay each shrunk failure, collecting what it prints.
    for k in range(len(runner.origins)):
        if not settings.report_multiple_bugs and k > 0:
            break
        var origin = runner.origins[k]
        var final_result = runner.interesting[origin]
        var choices = final_result[].choices()
        if runner.db and runner.db_key.byte_length() > 0:
            runner.db.value().save(runner.db_key, choices)
        var data = runner.new_data(choices.copy())
        data.is_final = True
        if origin in runner.arg_comments:
            data.arg_comments = runner.arg_comments[origin].copy()
        var msg = runner.execute(data)
        if origin in runner.explain_notes:
            data.notes.append(String("# ", runner.explain_notes[origin]))
        var r = Result(data.as_result())
        if r[].status != Status.INTERESTING and runner.interesting_errors[
            origin
        ].startswith("DeadlineExceeded"):
            msg = String(
                "Flaky: unreliable test timings! On an earlier run, ",
                runner.interesting_errors[origin],
                " But on the final replay it did not exceed the deadline. If",
                " you expect this variability in timing, set deadline=None.",
            )
        elif r[].status != Status.INTERESTING:
            msg = String(
                "Flaky: the falsifying example did not fail when replayed",
                " (the test may depend on state outside its inputs).",
                " Original error: ",
                runner.interesting_errors[origin],
            )
        report.failures.append(r)
        report.errors.append(msg)
    report.valid = runner.valid_count
    report.invalid = runner.invalid_count
    report.overrun = runner.overrun_count
    report.calls = runner.call_count
    report.exit_reason = runner.exit_reason
    return report^


def _failure_message(
    report: RunReport, name: String, settings: Settings
) -> String:
    var out = String()
    var n = len(report.failures)
    if n > 1:
        out += String("proptest found ", n, " distinct failures.\n")
    for k in range(n):
        ref r = report.failures[k][]
        if n > 1:
            out += String("\n--- Failure ", k + 1, " of ", n, " ---\n")
        out += String("Falsifying example (", name, "):\n")
        for note in r.notes:
            out += String("    ", note, "\n")
        if settings.print_blob or settings.verbosity >= Verbosity.verbose:
            out += String(
                "    To reproduce this example, run the test with",
                ' Settings(reproduce="',
                encode_blob(r.choices()),
                '")\n',
            )
        out += report.errors[k]
        if k + 1 < n:
            out += "\n"
    return out^


def _note_given(mut data: ConjectureData, var args: List[String]):
    """Record the falsifying arguments of a `given` test, with any
    explain-phase comments (Hypothesis's "or any other generated value")."""
    if len(data.arg_comments) == 0:
        var line = String("given(")
        for i in range(len(args)):
            if i > 0:
                line += ", "
            line += args[i]
        data.notes.append(line + ")")
        return
    data.notes.append("given(")
    for i in range(len(args)):
        data.notes.append(String("    ", args[i], ",", data.arg_comment(i)))
    data.notes.append(")")


def _check_deadline(
    data: ConjectureData, start_ns: Int, deadline_ns: Int
) raises:
    """Raise `DeadlineExceeded` if the test body took too long. As in
    Hypothesis, the deadline gets 25% grace except on the final replay, so
    that a failure reported for a deadline reproduces reliably."""
    if deadline_ns < 0:
        return
    var runtime = perf_counter_ns() - start_ns
    var limit = deadline_ns if data.is_final else (deadline_ns // 4) * 5
    if runtime >= limit:
        raise Error(
            String(
                "DeadlineExceeded: Test took ",
                Float64(runtime) / 1e6,
                "ms, which exceeds the deadline of ",
                Float64(deadline_ns) / 1e6,
                "ms. If this is expected, set deadline=None or a larger",
                " deadline in the test's Settings.",
            )
        )


def _raise_failures(report: RunReport, name: String, settings: Settings) raises:
    if len(report.failures) > 0:
        raise Error(_failure_message(report, name, settings))


# ===----------------------------------------------------------------------=== #
# given
# ===----------------------------------------------------------------------=== #


@always_inline
def given[
    S1: Strategy, //, T: def(S1.Value) raises
](
    s1: S1,
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check that `test(x)` passes for values `x` drawn from `s1`.

    Raises an `Error` describing the minimal failing example if it does not.
    """
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(mut data: ConjectureData) raises {s1, test, deadline}:
        var a = data.draw(s1)
        if data.is_final:
            _note_given(data, [format_value(a)])
        var start = perf_counter_ns()
        test(a)
        _check_deadline(data, start, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def given[
    S1: Strategy, S2: Strategy, //, T: def(S1.Value, S2.Value) raises
](
    s1: S1,
    s2: S2,
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check that `test(a, b)` passes for `a` from `s1` and `b` from `s2`."""
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(mut data: ConjectureData) raises {s1, s2, test, deadline}:
        var a = data.draw(s1)
        var b = data.draw(s2)
        if data.is_final:
            _note_given(data, [format_value(a), format_value(b)])
        var start = perf_counter_ns()
        test(a, b)
        _check_deadline(data, start, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def given[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value) raises,
](
    s1: S1,
    s2: S2,
    s3: S3,
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check `test(a, b, c)` for values drawn from three strategies."""
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(mut data: ConjectureData) raises {s1, s2, s3, test, deadline}:
        var a = data.draw(s1)
        var b = data.draw(s2)
        var c = data.draw(s3)
        if data.is_final:
            _note_given(
                data, [format_value(a), format_value(b), format_value(c)]
            )
        var start = perf_counter_ns()
        test(a, b, c)
        _check_deadline(data, start, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def given[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value, S4.Value) raises,
](
    s1: S1,
    s2: S2,
    s3: S3,
    s4: S4,
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check `test(a, b, c, d)` for values drawn from four strategies."""
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(
        mut data: ConjectureData,
    ) raises {s1, s2, s3, s4, test, deadline}:
        var a = data.draw(s1)
        var b = data.draw(s2)
        var c = data.draw(s3)
        var d = data.draw(s4)
        if data.is_final:
            _note_given(
                data,
                [
                    format_value(a),
                    format_value(b),
                    format_value(c),
                    format_value(d),
                ],
            )
        var start = perf_counter_ns()
        test(a, b, c, d)
        _check_deadline(data, start, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def given[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value, S4.Value, S5.Value) raises,
](
    s1: S1,
    s2: S2,
    s3: S3,
    s4: S4,
    s5: S5,
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check `test` for values drawn from 5 strategies."""
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(
        mut data: ConjectureData,
    ) raises {s1, s2, s3, s4, s5, test, deadline}:
        var a1 = data.draw(s1)
        var a2 = data.draw(s2)
        var a3 = data.draw(s3)
        var a4 = data.draw(s4)
        var a5 = data.draw(s5)
        if data.is_final:
            _note_given(
                data,
                [
                    format_value(a1),
                    format_value(a2),
                    format_value(a3),
                    format_value(a4),
                    format_value(a5),
                ],
            )
        var start = perf_counter_ns()
        test(a1, a2, a3, a4, a5)
        _check_deadline(data, start, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def given[
    S1: Strategy,
    S2: Strategy,
    S3: Strategy,
    S4: Strategy,
    S5: Strategy,
    S6: Strategy,
    //,
    T: def(S1.Value, S2.Value, S3.Value, S4.Value, S5.Value, S6.Value) raises,
](
    s1: S1,
    s2: S2,
    s3: S3,
    s4: S4,
    s5: S5,
    s6: S6,
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check `test` for values drawn from 6 strategies."""
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(
        mut data: ConjectureData,
    ) raises {s1, s2, s3, s4, s5, s6, test, deadline}:
        var a1 = data.draw(s1)
        var a2 = data.draw(s2)
        var a3 = data.draw(s3)
        var a4 = data.draw(s4)
        var a5 = data.draw(s5)
        var a6 = data.draw(s6)
        if data.is_final:
            _note_given(
                data,
                [
                    format_value(a1),
                    format_value(a2),
                    format_value(a3),
                    format_value(a4),
                    format_value(a5),
                    format_value(a6),
                ],
            )
        var start = perf_counter_ns()
        test(a1, a2, a3, a4, a5, a6)
        _check_deadline(data, start, deadline)

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def given_data[
    T: def(mut ConjectureData) raises
](
    test: T,
    settings: Settings = Settings(),
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Check a test that draws its own data interactively.

    This is Hypothesis's `@given(st.data())`:

    ```mojo
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers()), "xs")
        var i = data.draw(integers(0, max(len(xs) - 1, 0)), "index")
        ...
    given_data(prop)
    ```

    `data` also offers `note(msg)`, `event(msg)` and `target(score, label)`.
    """
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    var deadline = s.deadline_ns()

    def run_one(mut data: ConjectureData) raises {test, deadline}:
        data.report_draws = True
        var start = perf_counter_ns()
        var drawn_before = data.draw_time_ns
        test(data)
        # time spent drawing data doesn't count against the deadline
        _check_deadline(
            data, start + (data.draw_time_ns - drawn_before), deadline
        )

    var report = run_test(run_one, s, String(loc))
    _raise_failures(report, String(loc), s)


@always_inline
def check_examples[
    V: Drawable, //, T: def(V) raises
](
    examples: List[V],
    test: T,
    *,
    location: Optional[SourceLocation] = None,
) raises:
    """Run `test` on explicit examples (Hypothesis's `@example`), reporting
    the first that fails."""
    var loc = location.value() if location else call_location()
    for i in range(len(examples)):
        try:
            test(examples[i])
        except e:
            raise Error(
                String(
                    "Falsifying explicit example (",
                    loc,
                    "):\n    example(",
                    format_value(examples[i]),
                    ")\n",
                    e,
                )
            )


# ===----------------------------------------------------------------------=== #
# find / example
# ===----------------------------------------------------------------------=== #

comptime _FOUND = "At proptest.find: Found"


@always_inline
def find[
    S: Strategy, //, P: def(S.Value) raises -> Bool
](
    strategy: S,
    condition: P,
    settings: Settings = Settings(max_examples=2000, database=None),
    *,
    location: Optional[SourceLocation] = None,
) raises -> S.Value:
    """The simplest value from `strategy` satisfying `condition`, found by
    searching and then shrinking. Raises `NoSuchExample` if none is found.
    """
    var loc = location.value() if location else call_location()
    var s = _resolve_settings(settings, loc)
    s.report_multiple_bugs = False
    s.suppress_health_check = [
        HealthCheck.filter_too_much,
        HealthCheck.data_too_large,
        HealthCheck.large_base_example,
        HealthCheck.too_slow,
    ]

    def run_one(mut data: ConjectureData) raises {strategy, condition}:
        var v = data.draw(strategy)
        if condition(v):
            raise Error(_FOUND)

    var report = run_test(run_one, s, String(loc))
    if len(report.failures) == 0:
        raise Error(
            String(
                "NoSuchExample: no example satisfying the condition (", loc, ")"
            )
        )
    var data = ConjectureData(
        report.failures[0][].choices(),
        Provider(Random(0), ArcPointer(Constants())),
    )
    return data.draw(strategy)


def example[
    S: Strategy
](strategy: S, seed: Optional[UInt64] = None) raises -> S.Value:
    """One random value from `strategy` (Hypothesis's `strategy.example()`),
    for exploring strategies interactively, not for use in tests."""
    var r = Random(seed.value()) if seed else Random.from_time()
    for _ in range(1000):
        var data = ConjectureData(
            List[ChoiceValue](),
            Provider(Random(r.next_u64()), ArcPointer(Constants())),
        )
        try:
            return data.draw(strategy)
        except e:
            if data.status == Status.VALID and not data.frozen:
                raise e^
    raise Error("Unsatisfiable: could not generate an example")
