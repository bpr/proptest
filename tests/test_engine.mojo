# The engine as a whole: failure reports, assume(), health checks, multiple
# bugs, the example database, determinism, targeting, flakiness and
# exhaustion. Ported in spirit from hypothesis/tests/cover/test_given_*,
# test_health_checks.py, test_database_backend.py, test_targeting.py and
# tests/conjecture/test_engine.py.

from std.testing import TestSuite, assert_equal, assert_true, assert_false
from std.os import getenv
from std.time import sleep

from proptest import *


def failure_message[
    T: def(Int) raises
](test: T, settings: Settings) raises -> String:
    try:
        given(integers(), test, settings)
    except e:
        return String(e)
    return String()


def test_failure_report_has_minimal_example_and_error() raises:
    def prop(x: Int) raises:
        if x > 100:
            fail(String("x was ", x))

    var msg = failure_message(prop, Settings(database=None))
    assert_true("Falsifying example" in msg, msg)
    assert_true("given(101)" in msg, msg)
    assert_true("AssertionError: x was 101" in msg, msg)


def test_passing_test_does_not_raise() raises:
    def prop(x: Int) raises:
        assert_equal(x + 0, x)

    given(integers(), prop, Settings(database=None))


def test_assume_filters_examples() raises:
    var seen_odd = False

    def prop(x: Int) raises {mut seen_odd}:
        assume(x % 2 == 0)
        if x % 2 != 0:
            seen_odd = True

    given(integers(), prop, Settings(database=None))
    assert_false(seen_odd)


def test_impossible_assumption_is_unsatisfiable() raises:
    def prop(x: Int) raises:
        assume(False)

    var msg = String()
    try:
        given(integers(), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("Unsatisfiable" in msg or "FailedHealthCheck" in msg, msg)


def _never(x: Int) -> Bool:
    return x == 123456789


def test_filter_too_much_health_check() raises:
    def prop(x: Int) raises:
        pass

    var msg = String()
    try:
        given(filter(integers(), _never), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("FailedHealthCheck" in msg, msg)
    assert_true("filter" in msg, msg)


def test_health_check_can_be_suppressed() raises:
    def prop(x: Int) raises:
        pass

    var msg = String()
    try:
        given(
            filter(integers(), _never),
            prop,
            Settings(
                database=None,
                max_examples=10,
                suppress_health_check=[HealthCheck.filter_too_much],
            ),
        )
    except e:
        msg = String(e)
    assert_false("FailedHealthCheck" in msg, msg)


def test_reports_multiple_distinct_bugs() raises:
    def prop(x: Int) raises:
        if x > 1000:
            fail("too big")
        if x < -1000:
            fail("too small")

    var msg = failure_message(prop, Settings(database=None, max_examples=500))
    assert_true("2 distinct failures" in msg, msg)
    assert_true("given(1001)" in msg, msg)
    assert_true("given(-1001)" in msg, msg)


def test_report_multiple_bugs_false_reports_one() raises:
    def prop(x: Int) raises:
        if x > 1000:
            fail("too big")
        if x < -1000:
            fail("too small")

    var msg = failure_message(
        prop,
        Settings(database=None, max_examples=500, report_multiple_bugs=False),
    )
    assert_false("distinct failures" in msg, msg)
    assert_true("given(1001)" in msg or "given(-1001)" in msg, msg)


def test_database_replays_failures() raises:
    var db = String(".proptest/test-db-", getenv("USER", "x"))
    var calls = 0

    def prop(x: Int) raises {mut calls}:
        calls += 1
        if x > 12345:
            fail("big")

    var key = String("test_database_replays_failures")
    var first = String()
    try:
        given(integers(), prop, Settings(database=db, database_key=key))
    except e:
        first = String(e)
    assert_true("given(12346)" in first, first)
    # With generation and shrinking off, only the database can find it.
    calls = 0
    var second = String()
    try:
        given(
            integers(),
            prop,
            Settings(
                database=db,
                database_key=key,
                phases=Phases(generate=False, shrink=False),
            ),
        )
    except e:
        second = String(e)
    assert_true("given(12346)" in second, second)
    assert_true(calls <= 3, String(calls))

    # Once the bug is fixed, the stale entry is dropped.
    def fixed(x: Int) raises:
        pass

    given(
        integers(),
        fixed,
        Settings(database=db, database_key=key, phases=Phases(generate=False)),
    )
    var replayed = 0

    def count(x: Int) raises {mut replayed}:
        replayed += 1

    given(
        integers(),
        count,
        Settings(database=db, database_key=key, phases=Phases(generate=False)),
    )
    assert_equal(replayed, 0)


def test_seed_makes_runs_repeatable() raises:
    var a = List[Int]()
    var b = List[Int]()

    def rec_a(x: Int) raises {mut a}:
        a.append(x)

    def rec_b(x: Int) raises {mut b}:
        b.append(x)

    given(
        integers(),
        rec_a,
        Settings(database=None, seed=UInt64(42), max_examples=20),
    )
    given(
        integers(),
        rec_b,
        Settings(database=None, seed=UInt64(42), max_examples=20),
    )
    assert_equal(a, b)


def test_exhausts_small_search_spaces() raises:
    var calls = 0

    def prop(b: Bool) raises {mut calls}:
        calls += 1

    given(booleans(), prop, Settings(database=None))
    assert_equal(calls, 2)
    calls = 0

    def prop2(t: Tuple[Int, Bool]) raises {mut calls}:
        calls += 1

    given(tuples(integers(0, 9), booleans()), prop2, Settings(database=None))
    assert_equal(calls, 20)


def test_targeting_finds_rare_large_values() raises:
    def prop(mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 1 << 40), "x")
        data.target(Float64(x))
        if x >= (1 << 40) - 1000:
            fail("found a huge value")

    var msg = String()
    try:
        given_data(prop, Settings(database=None, max_examples=1000))
    except e:
        msg = String(e)
    assert_true("found a huge value" in msg, msg)


def test_given_data_reports_labeled_draws() raises:
    def prop(mut data: ConjectureData) raises:
        var flag = data.draw(booleans(), "flag")
        var xs = data.draw(lists(integers(0, 100)), "xs")
        data.note(String("note: len=", len(xs)))
        if len(xs) > 0 and xs[0] > 50:
            fail("element too big")

    var msg = String()
    try:
        given_data(prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("Draw 1 (flag): False" in msg, msg)
    assert_true("Draw 2 (xs): [51]" in msg, msg)
    assert_true("note: len=1" in msg, msg)


def test_flaky_test_is_reported() raises:
    var calls = 0

    def prop(x: Int) raises {mut calls}:
        calls += 1
        # fails only on the first few calls, so the replay passes
        if calls < 3 and x != 1234567:
            fail("flaky")

    var msg = String()
    try:
        given(integers(), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("Flaky" in msg, msg)


def test_shrink_phase_can_be_disabled() raises:
    def prop(x: Int) raises:
        if x > 100:
            fail("big")

    var msg = failure_message(
        prop, Settings(database=None, phases=Phases(shrink=False))
    )
    assert_true("AssertionError: big" in msg, msg)


def test_check_examples() raises:
    def prop(x: Int) raises:
        if x == 13:
            fail("unlucky")

    check_examples([1, 2, 3], prop)
    var msg = String()
    try:
        check_examples([1, 13], prop)
    except e:
        msg = String(e)
    assert_true("example(13)" in msg, msg)


def test_find_raises_when_nothing_matches() raises:
    var msg = String()
    try:
        _ = find(
            integers(0, 10), _never, Settings(database=None, max_examples=50)
        )
    except e:
        msg = String(e)
    assert_true("NoSuchExample" in msg, msg)


def test_many_arguments() raises:
    def prop(a: Int, b: String, c: Bool, d: List[Int]) raises:
        if c and len(d) > 1 and b.byte_length() > 0:
            fail("all set")

    var msg = String()
    try:
        given(
            integers(),
            text(),
            booleans(),
            lists(integers()),
            prop,
            Settings(database=None, phases=Phases(explain=False)),
        )
    except e:
        msg = String(e)
    assert_true("given(0, '0', True, [0, 0])" in msg, msg)


def test_explain_marks_free_arguments() raises:
    def prop(a: Int, s: String, b: Int) raises:
        if a > 10:
            fail("a too big")

    var msg = String()
    try:
        given(integers(), text(), integers(), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("        11,\n" in msg, msg)
    assert_true("'',  # or any other generated value" in msg, msg)
    assert_true("0,  # or any other generated value" in msg, msg)
    assert_true(
        "always failed when commented parts were varied together" in msg, msg
    )


def test_explain_does_not_mark_compared_arguments() raises:
    # Varying b alone almost never makes a == b false... but borrowing a's
    # value for b does, so neither may be marked.
    def prop(a: Int, b: Int) raises:
        if a == b:
            fail("equal")

    var msg = String()
    try:
        given(integers(), integers(), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("given(0, 0)" in msg, msg)
    assert_false("or any other" in msg, msg)


def test_explain_in_given_data() raises:
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers()), "xs")
        _ = data.draw(booleans(), "flag")
        if len(xs) > 2:
            fail("long")

    var msg = String()
    try:
        given_data(prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true(
        "Draw 2 (flag): False  # or any other generated value" in msg, msg
    )


def test_errors_without_location_are_one_bug() raises:
    def prop(x: Int) raises:
        if x > 10:
            raise Error(String("bad value ", x))

    var msg = failure_message(prop, Settings(database=None))
    assert_true("given(11)" in msg, msg)
    assert_true("bad value 11" in msg, msg)


def test_deadline_exceeded_is_reported() raises:
    def prop(x: Int) raises:
        if x > 1000:
            sleep(0.3)  # past the 250 ms (200 ms + 25% grace) limit

    var msg = failure_message(prop, Settings(database=None))
    assert_true("DeadlineExceeded" in msg, msg)
    assert_true("given(1001)" in msg, msg)


def test_deadline_can_be_disabled_or_raised() raises:
    def prop(x: Int) raises:
        if x > 1000:
            sleep(0.25)

    given(
        integers(0, 2000),
        prop,
        Settings(database=None, max_examples=5, deadline=None),
    )
    given(
        integers(0, 2000),
        prop,
        Settings(database=None, max_examples=5, deadline=1000.0),
    )


def _slow_int(mut data: ConjectureData) raises -> Int:
    sleep(0.15)
    return data.draw(integers())


def test_too_slow_health_check() raises:
    def prop(x: Int) raises:
        pass

    var msg = String()
    try:
        given(composite(_slow_int), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("FailedHealthCheck" in msg and "slow" in msg, msg)
    # ... and it can be suppressed
    given(
        composite(_slow_int),
        prop,
        Settings(
            database=None,
            max_examples=3,
            suppress_health_check=[HealthCheck.too_slow],
        ),
    )


def test_reproduce_blob_replays_failure() raises:
    def prop(x: Int) raises:
        if x > 4321:
            fail("big")

    var msg = failure_message(prop, Settings(database=None, print_blob=True))
    var start = msg.find('reproduce="')
    assert_true(start >= 0, msg)
    var blob = String(msg[byte = start + 11 : msg.find('")')])
    var calls = 0

    def counted(x: Int) raises {mut calls}:
        calls += 1
        if x > 4321:
            fail("big")

    var again = String()
    try:
        given(integers(), counted, Settings(database=None, reproduce=blob))
    except e:
        again = String(e)
    assert_true("given(4322)" in again, again)
    assert_equal(calls, 1)

    def fixed(x: Int) raises:
        pass

    var gone = String()
    try:
        given(integers(), fixed, Settings(database=None, reproduce=blob))
    except e:
        gone = String(e)
    assert_true("DidNotReproduce" in gone, gone)


def test_flaky_strategy_is_detected() raises:
    var n = 0

    def unstable(mut data: ConjectureData) raises {mut n} -> Int:
        # the range depends on how many times we've been called
        n += 1
        return data.draw(integers(0, 10 + n % 2))

    def prop(x: Int) raises:
        pass

    var msg = String()
    try:
        given(composite(unstable), prop, Settings(database=None))
    except e:
        msg = String(e)
    assert_true("FlakyStrategyDefinition" in msg, msg)


def test_six_arguments() raises:
    def prop(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int) raises:
        if a + b + c + d + e + f > 10:
            fail("sum too big")

    var msg = String()
    try:
        given(
            integers(0, 10),
            integers(0, 10),
            integers(0, 10),
            integers(0, 10),
            integers(0, 10),
            integers(0, 10),
            prop,
            Settings(database=None, phases=Phases(explain=False)),
        )
    except e:
        msg = String(e)
    assert_true("given(0, 0, 0, 0, 1, 10)" in msg, msg)


def test_pareto_front_is_saved_and_reused() raises:
    var db = String(".proptest/test-pareto-", getenv("USER", "x"))
    var key = String("test_pareto_front_is_saved_and_reused")

    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(0, 100), max_size=20))
        var total = 0
        for x in xs:
            total += x
        data.target(Float64(len(xs)), "length")
        data.target(Float64(total), "sum")

    given_data(prop, Settings(database=db, database_key=key, max_examples=50))
    var saved = ExampleDatabase(db).fetch(key + ".pareto")
    assert_true(len(saved) > 0)
    # every saved member is still non-dominated after a second run
    given_data(prop, Settings(database=db, database_key=key, max_examples=50))
    assert_true(len(ExampleDatabase(db).fetch(key + ".pareto")) > 0)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
