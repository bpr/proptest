# Settings(fork=True) and Settings(timeout=...): each test case runs in a
# child process, so crashes and hangs fail like any other error and are
# shrunk (after Rust proptest's `fork`; not in Hypothesis).

from std.benchmark import keep
from std.ffi import external_call
from std.os import abort, setenv, unsetenv
from std.testing import TestSuite, assert_equal, assert_true, assert_false

from proptest import *


def crash(sig: Int):
    """Kill this process with signal `sig`."""
    _ = external_call["kill", Int32](
        external_call["getpid", Int32](), Int32(sig)
    )


def failure[T: def(Int) raises](test: T, settings: Settings) raises -> String:
    try:
        given(integers(), test, settings)
    except e:
        return String(e)
    return String()


def forked() -> Settings:
    return Settings(database=None, fork=True)


def test_a_segfault_is_shrunk() raises:
    def prop(x: Int) raises:
        if x >= 1000:
            crash(11)

    var msg = failure(prop, forked())
    assert_true("Falsifying example" in msg, msg)
    assert_true("given(1000)" in msg, msg)
    assert_true("killed by SIGSEGV (signal 11)" in msg, msg)


def test_an_abort_is_shrunk() raises:
    def prop(x: Int) raises:
        if x < -50:
            abort("too small")

    var msg = failure(prop, forked())
    assert_true("given(-51)" in msg, msg)
    # Mojo's abort() ends in a trap instruction
    assert_true("SIGILL" in msg or "SIGTRAP" in msg or "SIGABRT" in msg, msg)


def test_exiting_early_is_a_failure() raises:
    def prop(x: Int) raises:
        if x > 7:
            external_call["_exit", NoneType](Int32(3))

    var msg = failure(prop, forked())
    assert_true("given(8)" in msg, msg)
    assert_true("exited with status 3" in msg, msg)


def test_distinct_crashes_are_distinct_failures() raises:
    def prop(x: Int) raises:
        if x > 100:
            crash(11)
        if x < -100:
            crash(6)

    var msg = failure(prop, forked())
    assert_true("2 distinct failures" in msg, msg)
    assert_true("given(101)" in msg and "SIGSEGV" in msg, msg)
    assert_true("given(-101)" in msg and "SIGABRT" in msg, msg)


def test_a_hang_times_out() raises:
    def prop(x: Int) raises:
        var n = 0
        while x > 10:  # never ends
            n += 1
            keep(n)

    var msg = failure(prop, Settings(database=None, timeout=100.0))
    assert_true("given(11)" in msg, msg)
    assert_true("Timeout: the test case ran longer than 100" in msg, msg)


def test_ordinary_failures_are_reported_as_usual() raises:
    def prop(x: Int) raises:
        if x > 100:
            fail(String("x was ", x))

    var msg = failure(prop, forked())
    assert_true("given(101)" in msg, msg)
    assert_true("AssertionError: x was 101" in msg, msg)


def test_passing_tests_pass_and_side_effects_stay_in_the_child() raises:
    var calls = 0

    def prop(x: Int) raises {mut calls}:
        calls += 1

    given(integers(), prop, forked())
    assert_equal(calls, 0)


def test_interactive_draws_are_reported_up_to_the_crash() raises:
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(0, 100)))
        data.note(String("length ", len(xs)))
        if len(xs) >= 3:
            crash(11)
        _ = data.draw(integers())

    var msg = String()
    try:
        given_data(prop, forked())
    except e:
        msg = String(e)
    assert_true("Draw 1: [0, 0, 0]" in msg, msg)
    assert_true("length 3" in msg, msg)
    assert_true("SIGSEGV" in msg, msg)


def test_strings_floats_and_weights_cross_the_log() raises:
    # string choices carry their alphabet (an interval set) and sampled_from
    # weights; both must survive the trip from the child to the shrinker
    def prop(s: String, f: Float64, k: Int) raises:
        if "z" in s and f > 1.5 and k == 3:
            crash(11)

    var msg = String()
    try:
        given(
            text(alphabet="abxyz"),
            floats(0.0, 10.0),
            sampled_from([1, 2, 3], weights=[1, 5, 1]),
            prop,
            forked(),
        )
    except e:
        msg = String(e)
    assert_true("given('z', 2.0, 3)" in msg, msg)


def test_a_crash_reproduces_from_its_blob() raises:
    def prop(x: Int) raises:
        if x >= 1000:
            crash(11)

    var settings = forked()
    settings.print_blob = True
    var msg = failure(prop, settings)
    var start = msg.find('reproduce="') + 11
    var blob = String(msg[byte = start : msg.find('"', start)])
    settings.reproduce = blob
    var again = failure(prop, settings)
    assert_true("given(1000)" in again, again)
    assert_true("SIGSEGV" in again, again)


def test_a_failure_that_changes_on_replay_says_so() raises:
    # as a use after free can: the final replay fails differently
    def prop(mut data: ConjectureData) raises:
        var x = data.draw(integers())
        if x > 5:
            if data.is_final:
                crash(11)
            fail("first error")

    var msg = String()
    try:
        given_data(prop, forked())
    except e:
        msg = String(e)
    assert_true("SIGSEGV" in msg, msg)
    assert_true("failed differently when it was found" in msg, msg)
    assert_true("first error" in msg, msg)


def test_the_environment_turns_fork_on() raises:
    var s = Settings()
    assert_false(s.forks())
    assert_true(Settings(timeout=5.0).forks())
    _ = setenv("PROPTEST_TIMEOUT", "250")
    var t = Settings().with_env_overrides()
    assert_true(t.forks())
    assert_equal(t.timeout.value(), 250.0)
    assert_equal(
        Settings(timeout=9.0).with_env_overrides().timeout.value(), 9.0
    )
    _ = unsetenv("PROPTEST_TIMEOUT")


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
