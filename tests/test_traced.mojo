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
    # either is a local minimum for the shrinker
    assert_true(
        "[PUSH, POP, PUSH, POP]" in msg or "[PUSH, PUSH, POP, POP]" in msg,
        msg,
    )


def test_closeness_guides_fuzzing_when_the_value_is_not_a_choice() raises:
    # x + y is never drawn as is, so no choice can be replaced by 50_000;
    # getting closer to it at the comparison counts as coverage instead.
    def prop(mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 100_000))
        var y = data.draw(integers(0, 100_000))
        var sum = Traced(x + y, data.comparisons)
        if sum == 150_001:
            fail("sum")

    var target = fuzz_target_data(
        prop, Settings(database=None, seed=UInt64(12))
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=50_000)
    except e:
        msg = String(e)
    assert_true("sum" in msg, msg)


def test_arithmetic_results_are_traced_back_to_the_drawn_value() raises:
    # each comparison of a computed value also records the drawn value
    # against what it would need to be
    var log = ArcPointer(ComparisonLog())
    var x = Traced[Int](10, log)
    _ = x * 3 + 7 == 100
    _ = 5 - x == 2
    _ = (x ^ 0xFF) == 0x12
    _ = -x == 4
    _ = ~x == 4
    ref e = log[].entries
    assert_equal(len(e), 10)
    for i in range(0, 10, 2):
        assert_equal(e[i + 1].lhs.i, 10)
        assert_equal(e[i + 1].closeness, e[i].closeness)
    assert_equal(e[1].rhs.i, 31)
    assert_equal(e[3].rhs.i, 3)
    assert_equal(e[5].rhs.i, 0xED)
    assert_equal(e[7].rhs.i, -4)
    assert_equal(e[9].rhs.i, -5)
    _ = x * 3 == 100  # no integer solution: nothing more recorded
    _ = x // 2 == 3  # not invertible
    assert_equal(len(log[].entries), 12)


def test_narrow_arithmetic_wraps_and_strings_strip_their_affixes() raises:
    var log = ArcPointer(ComparisonLog())
    var u = Traced[UInt8](250, log)
    var v = u + 10
    assert_equal(Int(v), 4)
    _ = v == 3
    assert_equal(log[].entries[1].rhs.i, 249)
    var s = Traced[String](String("ab"), log)
    var t = "<" + s + ">"
    assert_equal(String(t), "<ab>")
    _ = t == "<PUSH>"
    _ = t.startswith("<PU")
    _ = t == "PUSH"  # can't come from "<" + s + ">"
    ref e = log[].entries
    assert_equal(len(e), 7)
    assert_equal(String(e[3].lhs), String("'ab'"))
    assert_equal(String(e[3].rhs), String("'PUSH'"))
    assert_equal(String(e[5].rhs), String("'PU'"))
    var n = Traced[Int](1, log)
    n += 2
    n *= 5
    n -= 1
    assert_equal(Int(n), 14)


def test_fuzz_gets_past_magic_numbers_after_arithmetic() raises:
    def prop(x: Traced[Int], s: Traced[String]) raises:
        var code = (x - 1000) * 7 ^ 0x5A5A
        if code == 864_213_601 and "cmd:" + s == "cmd:OPEN":
            fail("unlocked")

    var target = fuzz_target(
        traced(integers()),
        traced(text()),
        prop,
        Settings(database=None, seed=UInt64(5)),
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=20_000)
    except e:
        msg = String(e)
    assert_true("unlocked" in msg, msg)
    assert_true("'OPEN'" in msg, msg)


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
