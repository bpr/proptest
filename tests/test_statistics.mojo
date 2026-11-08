# Run statistics: events, tables and coverage requirements (Hypothesis's
# statistics; QuickCheck's tabulate, cover and checkCoverage).

from std.testing import TestSuite, assert_equal, assert_true, assert_false
from std.math import abs

from proptest import *
from proptest.internal.statistics import inverse_normal_cdf, wilson


def fast() -> Settings:
    return Settings(database=None, max_examples=200)


def test_wilson_interval() raises:
    assert_true(abs(inverse_normal_cdf(0.975) - 1.959964) < 1e-5)
    assert_true(abs(inverse_normal_cdf(0.5)) < 1e-9)
    # 50 of 100 at 95%: about [0.404, 0.596]
    var z = inverse_normal_cdf(0.975)
    assert_true(abs(wilson(50, 100, -z) - 0.4038) < 1e-3)
    assert_true(abs(wilson(50, 100, z) - 0.5962) < 1e-3)


def test_statistics_count_events_tables_and_coverage() raises:
    def test(mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 999)) % 10
        if x < 5:
            data.event("small")
            data.event("small")  # counted once per test case
        data.tabulate("parity", "even" if x % 2 == 0 else "odd")
        data.cover(10, x == 9, "nine")
        if x == 7:
            assume(False)

    var report = run_test(test, fast(), "stats")
    ref st = report.statistics
    # the generate phase only (not the simplest example run before it)
    assert_true(st.valid <= report.valid and st.valid >= report.valid - 2)
    assert_true(st.valid >= 190 and st.invalid > 0, String(st))
    var small = st.events["small"]
    assert_true(small > st.cases // 4 and small < st.cases, String(st))
    var t = st.tables["parity"].copy()
    assert_equal(t["even"] + t["odd"], st.valid)
    assert_equal(st.cover_required["nine"], 10.0)
    assert_true(st.cover_hits["nine"] > 0, String(st))
    var text = String(st)
    assert_true("Events:" in text and ", small" in text, text)
    assert_true("parity (" in text, text)
    assert_true("nine (required 10.0%)" in text, text)


def test_check_coverage_passes_when_covered() raises:
    def prop(xs: List[Int]) raises:
        pass

    var long_lists = cover(
        lists(integers()),
        10,
        "long",
        lambda (xs: List[Int]) -> Bool: len(xs) >= 3,
    )
    given(
        long_lists,
        prop,
        Settings(database=None, check_coverage=Confidence()),
    )


def test_check_coverage_fails_when_not_covered() raises:
    def prop(x: Int) raises:
        pass

    var s = cover(
        integers(0, 100), 50, "above 90", lambda (x: Int) -> Bool: x > 90
    )
    var msg = String()
    try:
        given(s, prop, Settings(database=None, check_coverage=Confidence()))
    except e:
        msg = String(e)
    assert_true("Insufficient coverage" in msg, msg)
    assert_true("above 90" in msg and "but expected 50.0%" in msg, msg)


def test_unchecked_coverage_only_warns() raises:
    def prop(x: Int) raises:
        pass

    var s = cover(
        integers(0, 100), 50, "above 90", lambda (x: Int) -> Bool: x > 90
    )
    given(s, prop, Settings(database=None, verbosity=Verbosity.quiet))


def test_check_coverage_generates_past_max_examples() raises:
    # with near-certainty demanded, 100 examples can't settle a 10%
    # requirement that holds about a fifth of the time
    def test(mut data: ConjectureData) raises:
        var a = data.draw(booleans())
        var b = data.draw(booleans())
        _ = data.draw(integers())  # so the search space can't run out
        data.cover(10, a and b, "both")

    var report = run_test(
        test,
        Settings(
            database=None,
            max_examples=100,
            check_coverage=Confidence(certainty=1e100),
        ),
        "coverage",
    )
    assert_equal(report.coverage_error, "")
    assert_true(report.statistics.valid > 100, String(report.statistics))


def test_tabulate_strategy() raises:
    def test(mut data: ConjectureData) raises:
        _ = data.draw(
            tabulate(
                lists(booleans()),
                "length",
                lambda (xs: List[Bool]) -> String: String(len(xs)),
            )
        )

    var report = run_test(test, fast(), "tabulate")
    var t = report.statistics.tables["length"].copy()
    assert_true(len(t) > 3, String(report.statistics))


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
