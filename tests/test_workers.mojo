# Settings(workers=k): the generate phase runs in k forked worker
# processes (after QuickerCheck's parallel QuickCheck; not in Hypothesis).

from std.ffi import external_call
from std.testing import TestSuite, assert_equal, assert_true, assert_false
from std.time import perf_counter_ns

from proptest import *


def crash(sig: Int):
    """Kill this process with signal `sig`."""
    _ = external_call["kill", Int32](
        external_call["getpid", Int32](), Int32(sig)
    )


def sleep_ms(ms: Int):
    _ = external_call["usleep", Int32](UInt32(ms * 1000))


def in_workers(k: Int = 4) -> Settings:
    return Settings(database=None, workers=k, deadline=None)


def failure[T: def(Int) raises](test: T, settings: Settings) raises -> String:
    try:
        given(integers(), test, settings)
    except e:
        return String(e)
    return String()


def test_a_failure_found_by_a_worker_is_shrunk() raises:
    def prop(x: Int) raises:
        if x >= 1000:
            raise Error("too big")

    var msg = failure(prop, in_workers())
    assert_true("given(1000)" in msg and "too big" in msg, msg)


def test_distinct_failures_from_workers_are_all_reported() raises:
    # distinct failures need distinct origins (`At file:line:col:`),
    # which a plain `raise Error(...)` doesn't have
    def prop(x: Int) raises:
        assert_true(x <= 100, "high")
        assert_true(x >= -100, "low")

    var msg = failure(prop, in_workers())
    assert_true("given(101)" in msg and "high" in msg, msg)
    assert_true("given(-101)" in msg and "low" in msg, msg)


def test_counts_and_statistics_add_up_across_workers() raises:
    def test(mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 999)) % 10
        if x < 5:
            data.event("small")
        data.tabulate("parity", "even" if x % 2 == 0 else "odd")

    var settings = in_workers()
    settings.max_examples = 200
    var report = run_test(test, settings, "workers")
    assert_true(report.valid >= 200, String(report.valid))
    ref st = report.statistics
    assert_true(st.valid >= 196, String(st))
    var small = st.events["small"]
    assert_true(small > st.cases // 4 and small < st.cases, String(st))
    var t = st.tables["parity"].copy()
    assert_equal(t["even"] + t["odd"], st.valid)


def test_a_crashing_worker_is_reported() raises:
    def prop(x: Int) raises:
        if x >= 1000:
            crash(11)

    var msg = failure(prop, in_workers())
    assert_true("Crash: a worker process" in msg, msg)
    assert_true("SIGSEGV" in msg and "fork=True" in msg, msg)


def test_workers_with_fork_shrink_a_crash() raises:
    def prop(x: Int) raises:
        if x >= 1000:
            crash(11)

    var settings = in_workers()
    settings.fork = True
    var msg = failure(prop, settings)
    assert_true("given(1000)" in msg and "SIGSEGV" in msg, msg)


def test_health_check_errors_come_back_from_workers() raises:
    def prop(x: Int) raises:
        assume(False)

    var msg = failure(prop, in_workers())
    assert_true("FailedHealthCheck" in msg, msg)


def test_slow_test_cases_run_in_parallel() raises:
    def prop(x: Int) raises:
        sleep_ms(25)

    var settings = in_workers(4)
    settings.max_examples = 48
    var t0 = perf_counter_ns()
    given(integers(), prop, settings)
    var parallel = perf_counter_ns() - t0
    settings.workers = 1
    t0 = perf_counter_ns()
    given(integers(), prop, settings)
    var sequential = perf_counter_ns() - t0
    # 48 x 25 ms is 1.2 s in one process, 0.3 s in four (with room for
    # starting the workers on a busy machine)
    assert_true(
        parallel * 3 < sequential * 2,
        String("parallel ", parallel, " ns, sequential ", sequential, " ns"),
    )


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
