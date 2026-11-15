# Traced values: comparisons recorded for the fuzz loop (input-to-state
# replacement and value-profile features).

from std.memory import ArcPointer
from std.testing import TestSuite, assert_equal, assert_true, assert_false

from proptest import *
from proptest.internal.comparisons import ComparisonLog, int_closeness


def test_traced_values_compare_hash_and_print_like_their_value() raises:
    var log = ArcPointer(ComparisonLog())
    var x = Traced[Int](5, log)
    var y = Traced[Int](7, log)
    assert_true(x == 5 and x != 6 and x < 6 and x <= 5 and x > 4 and x >= 5)
    assert_true(x < y and y > x and x != y and not (x == y))
    assert_equal(hash(x), hash(5))
    assert_equal(String(x), "5")
    assert_equal(Int(x), 5)
    var s = Traced[String](String("PUSH 3"), log)
    assert_true(s.startswith("PUSH") and s.endswith("3") and "H 3" in s)
    assert_equal(s.byte_length(), 6)
    assert_equal(String(s), "PUSH 3")


def test_each_comparison_is_recorded_with_its_site_and_closeness() raises:
    var log = ArcPointer(ComparisonLog())
    var x = Traced[Int](4240, log)
    for _ in range(2):  # the same comparison again isn't recorded twice
        _ = x == 4242
    _ = x < 4242  # a different site
    var s = Traced[String](String("PUP"), log)
    _ = s == "PUSH"
    ref e = log[].entries
    assert_equal(len(e), 3)
    assert_equal(e[0].lhs.i, 4240)
    assert_equal(e[0].rhs.i, 4242)
    assert_equal(e[0].closeness, int_closeness(4240, 4242))
    assert_true(e[0].site != e[1].site)
    assert_equal(e[2].closeness, 4)  # a common prefix of 2
    _ = x == 4240
    assert_equal(log[].entries[3].closeness, 128)


def test_comparisons_between_traced_values_record_both_sides() raises:
    var log = ArcPointer(ComparisonLog())
    var x = Traced[Int](1, log)
    var y = Traced[Int](2, log)
    _ = x == y
    assert_equal(len(log[].entries), 2)
    assert_equal(log[].entries[0].rhs.i, 2)
    assert_equal(log[].entries[1].rhs.i, 1)


def _largest[T: Comparable & Copyable & Deinitable](xs: List[T]) -> T:
    var best = xs[0].copy()
    for x in xs:
        if x > best:
            best = x.copy()
    return best^


def test_generic_code_records_comparisons_too() raises:
    var log = ArcPointer(ComparisonLog())
    var xs: List[Traced[Int]] = [
        Traced[Int](3, log),
        Traced[Int](9, log),
        Traced[Int](4, log),
    ]
    assert_equal(_largest(xs).value, 9)
    assert_true(len(log[].entries) > 0)


def test_traced_draws_record_in_the_test_case() raises:
    def prop(mut data: ConjectureData) raises:
        var x = data.draw(traced(integers(0, 10)))
        _ = x == 99
        assert_equal(len(data.comparisons[].entries), 1)
        assert_equal(data.comparisons[].entries[0].rhs.i, 99)

    given_data(prop, Settings(database=None, max_examples=20))


def test_fuzz_gets_past_magic_numbers() raises:
    # Two 1-in-a-million (or worse) equalities: random mutation doesn't
    # find them in 100_000 inputs; with the values traced, replacing a
    # choice by the value it was compared with finds them in about 100.
    def prop(x: Traced[Int], y: Traced[Int]) raises:
        if x == 123456789 and y == 424242:
            fail("magic")

    var target = fuzz_target(
        traced(integers()),
        traced(integers(0, 1_000_000)),
        prop,
        Settings(database=None, seed=UInt64(1)),
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=5000)
    except e:
        msg = String(e)
    assert_true("magic" in msg, msg)
    assert_true("given(123456789, 424242)" in msg, msg)


def test_fuzz_gets_past_string_comparisons() raises:
    def prop(mut data: ConjectureData) raises:
        var cmds = data.draw(lists(traced(text()), max_size=8))
        var depth = 0
        var steps = 0
        for c in cmds:
            if c == "PUSH":
                depth += 1
            elif c.startswith("POP") and depth > 0:
                depth -= 1
                steps += 1
        data.event(String("steps ", steps, " depth ", depth))
        if steps >= 2:
            fail("popped twice")

    var target = fuzz_target_data(prop, Settings(database=None, seed=UInt64(2)))
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=20_000)
    except e:
        msg = String(e)
    assert_true("popped twice" in msg, msg)
    assert_true("[PUSH, POP, PUSH, POP]" in msg, msg)


def test_closeness_guides_fuzzing_when_the_value_is_not_a_choice() raises:
    # x + y is never drawn as is, so no choice can be replaced by 50_000;
    # getting closer to it at the comparison counts as coverage instead.
    def prop(mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 100_000))
        var y = data.draw(integers(0, 100_000))
        var sum = Traced(x + y, data.comparisons)
        if sum == 150_001:
            fail("sum")

    var target = fuzz_target_data(prop, Settings(database=None, seed=UInt64(3)))
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=50_000)
    except e:
        msg = String(e)
    assert_true("sum" in msg, msg)


def test_comparisons_survive_fork_mode() raises:
    def prop(x: Traced[Int]) raises:
        if x == 987654321:
            fail("magic")

    var target = fuzz_target(
        traced(integers()),
        prop,
        Settings(database=None, fork=True, seed=UInt64(4)),
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=2000)
    except e:
        msg = String(e)
    assert_true("magic" in msg, msg)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
