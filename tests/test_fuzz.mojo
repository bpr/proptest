# fuzz_target / FuzzTarget.fuzz_one_input: running a property on inputs
# from a byte-level fuzzer. Ported in spirit from
# hypothesis/tests/cover/test_fuzz_one_input.py.

from std.memory import bitcast
from std.os import abort, getenv
from std.testing import TestSuite, assert_equal, assert_true, assert_false

from proptest import *


struct Bytes(Movable):
    """A deterministic stream of pseudo-random byte strings."""

    var state: UInt64

    def __init__(out self, seed: UInt64):
        self.state = seed

    def next_u64(mut self) -> UInt64:
        self.state = self.state * 6364136223846793005 + 1442695040888963407
        var z = self.state
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
        return z ^ (z >> 31)

    def next(mut self, max_len: Int) -> List[UInt8]:
        var n = Int(self.next_u64() % UInt64(max_len + 1))
        var out = List[UInt8](capacity=n)
        for _ in range(n):
            out.append(UInt8(self.next_u64() & 0xFF))
        return out^


def no_db() -> Settings:
    return Settings(database=None)


def test_a_passing_input_returns_canonical_bytes_that_replay_it() raises:
    var seen = List[String]()

    def prop(x: Int, xs: List[Int], s: String, b: Bool) raises {mut seen}:
        seen.append(String(x, " ", xs, " ", repr(s), " ", b))

    var target = fuzz_target(
        integers(),
        lists(integers(-3, 1000), max_size=8),
        text(max_size=5),
        booleans(),
        prop,
        no_db(),
    )
    var gen = Bytes(1)
    var valid = 0
    for _ in range(2000):
        var input = gen.next(80)
        seen.clear()
        var out = target.fuzz_one_input(input)
        if not out:
            continue
        valid += 1
        var canonical = out.take()
        assert_true(len(canonical) <= len(input))
        var first = seen[len(seen) - 1]
        var again = target.fuzz_one_input(canonical)
        assert_true(Bool(again))
        assert_equal(again.value(), canonical)
        assert_equal(seen[len(seen) - 1], first)
    assert_true(valid > 100, String(valid))


def test_floats_round_trip_bit_for_bit() raises:
    var seen = List[UInt64]()

    def prop(x: Float64, y: Float64) raises {mut seen}:
        seen.append(bitcast[DType.uint64](x))
        seen.append(bitcast[DType.uint64](y))

    var target = fuzz_target(floats(), floats(-1.0, 1e10), prop, no_db())
    var gen = Bytes(2)
    var special = 0
    for _ in range(3000):
        seen.clear()
        var out = target.fuzz_one_input(gen.next(20))
        if not out:
            continue
        var x = bitcast[DType.float64](seen[0])
        if x != x or x == 0 or abs(x) == Float64.MAX or abs(x) < 1e-300:
            special += 1
        var a = seen[0]
        var b = seen[1]
        seen.clear()
        _ = target.fuzz_one_input(out.value())
        assert_equal(seen[0], a)
        assert_equal(seen[1], b)
    # NaNs, zeros, infinities and subnormals all occur
    assert_true(special > 0, String(special))


def test_too_few_bytes_is_an_invalid_input() raises:
    var calls = 0

    def prop(x: Int) raises {mut calls}:
        calls += 1

    var target = fuzz_target(integers(0, 1000), prop, no_db())
    assert_false(Bool(target.fuzz_one_input(List[UInt8]())))
    assert_false(Bool(target.fuzz_one_input([UInt8(1)])))
    assert_equal(calls, 0)
    assert_true(Bool(target.fuzz_one_input([UInt8(1), UInt8(2)])))
    assert_equal(calls, 1)


def test_a_rejected_input_returns_none() raises:
    def prop(x: Int) raises:
        assume(x % 2 == 0)

    var target = fuzz_target(integers(0, 255), prop, no_db())
    assert_true(Bool(target.fuzz_one_input([UInt8(4)])))
    assert_false(Bool(target.fuzz_one_input([UInt8(5)])))


def test_integers_read_their_bytes_big_endian() raises:
    var got = List[Int]()

    def prop(x: Int) raises {mut got}:
        got.append(x)

    var target = fuzz_target(integers(10, 10 + 65535), prop, no_db())
    var out = target.fuzz_one_input([UInt8(1), UInt8(2), UInt8(99)])
    assert_equal(got[0], 10 + 258)
    # the unused trailing byte is dropped
    assert_equal(out.value(), [UInt8(1), UInt8(2)])


def test_a_failure_is_raised_and_saved_for_given_to_replay() raises:
    var db = String(".proptest/test-fuzz-db-", getenv("USER", "x"))
    var key = String("test_a_failure_is_raised_and_saved")

    def prop(xs: List[Int]) raises:
        if len(xs) >= 3:
            fail("three or more")

    var settings = Settings(database=db, database_key=key)
    var target = fuzz_target(lists(integers(0, 255)), prop, settings)
    var gen = Bytes(3)
    var failures = 0
    for _ in range(200):
        try:
            _ = target.fuzz_one_input(gen.next(40))
        except e:
            assert_true("three or more" in String(e), String(e))
            failures += 1
    assert_true(failures > 0)
    # only failures simpler than the last one saved are saved
    var saved = len(ExampleDatabase(db).fetch(key))
    assert_true(saved >= 1 and saved < failures, String(saved, failures))

    # `given` with the same key replays and shrinks them without generating
    var msg = String()
    try:
        given(
            lists(integers(0, 255)),
            prop,
            Settings(
                database=db, database_key=key, phases=Phases(generate=False)
            ),
        )
    except e:
        msg = String(e)
    assert_true("given([0, 0, 0])" in msg, msg)

    # clean up: a passing run drops the stale entries
    def fixed(xs: List[Int]) raises:
        pass

    given(
        lists(integers(0, 255)),
        fixed,
        Settings(database=db, database_key=key, phases=Phases(generate=False)),
    )


def test_fuzz_target_data_draws_interactively() raises:
    var sums = List[Int]()

    def prop(mut data: ConjectureData) raises {mut sums}:
        var n = data.draw(integers(0, 3))
        var total = 0
        for _ in range(n):
            total += data.draw(integers(0, 9))
        sums.append(total)
        if total > 20:
            fail("too big")

    var target = fuzz_target_data(prop, no_db())
    _ = target.fuzz_one_input([UInt8(2), UInt8(4), UInt8(5)])
    assert_equal(sums[0], 9)
    var raised = False
    try:
        _ = target.fuzz_one_input([UInt8(3), UInt8(9), UInt8(9), UInt8(9)])
    except e:
        raised = "too big" in String(e)
    assert_true(raised)


def test_a_crash_in_fork_mode_is_raised() raises:
    def prop(x: Int) raises:
        if x == 7:
            abort("seven")

    var target = fuzz_target(
        integers(0, 255), prop, Settings(database=None, fork=True)
    )
    # a passing input still returns its canonical bytes, rebuilt from the
    # child's log
    assert_equal(
        target.fuzz_one_input([UInt8(3), UInt8(1)]).value(), [UInt8(3)]
    )
    var msg = String()
    try:
        _ = target.fuzz_one_input([UInt8(7)])
    except e:
        msg = String(e)
    assert_true("Crash" in msg, msg)


# ===----------------------------------------------------------------------=== #
# FuzzTarget.fuzz: the built-in fuzz loop
# ===----------------------------------------------------------------------=== #


def test_fuzz_without_a_failure_returns_what_it_did() raises:
    def prop(xs: List[Int], s: String) raises:
        pass

    var target = fuzz_target(
        lists(integers(0, 100)),
        text(),
        prop,
        Settings(database=None, seed=UInt64(1)),
    )
    var report = target.fuzz(max_inputs=2000)
    assert_equal(report.inputs, 2000)
    assert_true(report.valid > 1000, String(report))
    assert_true(report.corpus > 5, String(report))
    assert_true(report.features >= report.corpus, String(report))
    assert_true("2000 inputs" in String(report), String(report))


def test_fuzz_stops_after_its_time() raises:
    def prop(x: Int) raises:
        pass

    var target = fuzz_target(integers(), prop, Settings(database=None))
    var report = target.fuzz(0.3)
    assert_true(report.seconds >= 0.3 and report.seconds < 2, String(report))
    assert_true(report.inputs > 0)


def test_fuzz_is_guided_by_events() raises:
    # Each matching element is an event, so the inputs that get further
    # are kept and mutated: [1, 2, 3, 4, 5] is found a step at a time,
    # where random generation would need about 16**5 tries.
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(0, 15), min_size=5, max_size=5))
        for i in range(5):
            if xs[i] != i + 1:
                return
            data.event(String("matched ", i + 1))
        fail("found it")

    var target = fuzz_target_data(prop, Settings(database=None, seed=UInt64(3)))
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=50_000)
    except e:
        msg = String(e)
    assert_true("found it" in msg, msg)


def test_fuzz_shrinks_and_reports_like_given() raises:
    def prop(xs: List[Int]) raises:
        var total = 0
        for x in xs:
            total += x
        if total > 1000:
            fail("too big")

    var target = fuzz_target(
        lists(integers(0, 1000)), prop, Settings(database=None, seed=UInt64(2))
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=5000)
    except e:
        msg = String(e)
    assert_true("Falsifying example" in msg, msg)
    assert_true("given([1, 1000])" in msg, msg)
    assert_true("too big" in msg, msg)


def test_fuzz_finds_boundary_values() raises:
    def prop(x: Int, y: Float64) raises:
        if x == Int(Int64.MAX) and y != y:
            fail("max and nan")

    var target = fuzz_target(
        integers(), floats(), prop, Settings(database=None, seed=UInt64(4))
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=50_000)
    except e:
        msg = String(e)
    assert_true("max and nan" in msg, msg)


def test_fuzz_saves_its_corpus_for_the_next_run() raises:
    var db = String(".proptest/test-fuzz-db-", getenv("USER", "x"))
    var key = String("test_fuzz_saves_its_corpus")

    def prop(xs: List[Int], b: Bool) raises:
        pass

    var settings = Settings(database=db, database_key=key, seed=UInt64(5))
    var target = fuzz_target(lists(integers(0, 9)), booleans(), prop, settings)
    var first = target.fuzz(max_inputs=1000)
    var saved = len(ExampleDatabase(db).fetch(key + ".fuzz"))
    assert_true(saved > 0 and saved <= first.corpus, String(saved))
    # a new target starts from the saved corpus
    var again = fuzz_target(lists(integers(0, 9)), booleans(), prop, settings)
    var second = again.fuzz(max_inputs=1)
    assert_true(second.corpus >= saved - 1, String(second))
    # clean up
    var store = ExampleDatabase(db)
    for choices in store.fetch(key + ".fuzz"):
        store.delete(key + ".fuzz", choices)


def test_fuzz_reports_a_crash_in_fork_mode() raises:
    def prop(xs: List[Int]) raises:
        if len(xs) >= 2 and xs[0] == xs[1] + 1:
            abort("off by one")

    var target = fuzz_target(
        lists(integers(0, 100)),
        prop,
        Settings(database=None, fork=True, seed=UInt64(6)),
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=3000)
    except e:
        msg = String(e)
    assert_true("Crash" in msg, msg)
    assert_true("given([1, 0])" in msg, msg)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
