# Ported from hypothesis/tests/quality/test_shrink_quality.py: each test
# finds the minimal example satisfying a condition and checks it is the
# one Hypothesis finds.

from std.testing import TestSuite, assert_equal, assert_true

from std.collections import Set, Dict

from proptest import *


def always(x: Int) -> Bool:
    return True


def test_integers_from_minimizes_leftwards() raises:
    assert_equal(find(integers(min_value=101), always), 101)


def test_minimize_bounded_integers_to_zero() raises:
    assert_equal(find(integers(-10, 10), always), 0)


def not_zero(x: Int) -> Bool:
    return x != 0


def test_minimize_bounded_integers_to_positive() raises:
    assert_equal(find(filter(integers(-10, 10), not_zero), always), 1)


def test_minimize_string_to_empty() raises:
    def any_s(s: String) -> Bool:
        return True

    assert_equal(find(text(), any_s), "")


def len_ge_10(s: String) -> Bool:
    return len(s.codepoints()) >= 10


def test_minimize_longer_string() raises:
    assert_equal(find(text(), len_ge_10), "0000000000")


def list_len_ge_10[T: Copyable](xs: List[T]) -> Bool:
    return len(xs) >= 10


def test_minimize_longer_list_of_strings() raises:
    var xs = find(lists(text()), list_len_ge_10[String])
    assert_equal(len(xs), 10)
    for x in xs:
        assert_equal(x, "")


def test_minimize_one_of() raises:
    def any_i(x: Int) -> Bool:
        return True

    for _ in range(10):
        assert_equal(find(one_of(integers(), integers(10, 20)), any_i), 0)


def test_minimize_mixed_list() raises:
    var xs = find(
        lists(one_of(integers(), map(integers(1000, 2000), _neg))),
        list_len_ge_10[Int],
    )
    assert_equal(len(xs), 10)
    for x in xs:
        assert_equal(x, 0)


def _neg(x: Int) -> Int:
    return -x


def set_len_ge_3(s: Set[Int]) -> Bool:
    return len(s) >= 3


def test_minimize_3_set() raises:
    var s = find(sets(integers()), set_len_ge_3)
    assert_equal(len(s), 3)
    assert_true(
        (0 in s and 1 in s and 2 in s) or (-1 in s and 0 in s and 1 in s)
    )


def test_minimize_sets_sampled_from() raises:
    def any_set(s: Set[Int]) -> Bool:
        return True

    var s = find(
        sets(sampled_from([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]), min_size=3), any_set
    )
    assert_equal(len(s), 3)
    assert_true(0 in s and 1 in s and 2 in s)


def just_list(b: Bool) raises -> Lists[Just[Bool]]:
    return lists(just(b))


def bools_len_ge_10(xs: List[Bool]) -> Bool:
    return len(xs) >= 10


def test_can_simplify_flatmap_with_bounded_left_hand_size() raises:
    var xs = find(flatmap(booleans(), just_list), bools_len_ge_10)
    assert_equal(len(xs), 10)
    for x in xs:
        assert_equal(x, False)


def just_int(x: Int) -> Just[Int]:
    return just(x)


def test_can_simplify_across_flatmap_of_just() raises:
    assert_equal(find(flatmap(integers(), just_int), always), 0)


def just_int_list(x: Int) raises -> Lists[Just[Int]]:
    return lists(just(x))


def any_list(xs: List[Int]) -> Bool:
    return True


def test_can_simplify_on_right_hand_strategy_of_flatmap() raises:
    assert_equal(len(find(flatmap(integers(), just_int_list), any_list)), 0)


def test_can_simplify_on_both_sides_of_flatmap() raises:
    var xs = find(flatmap(integers(), just_int_list), list_len_ge_10[Int])
    assert_equal(len(xs), 10)
    for x in xs:
        assert_equal(x, 0)


def test_minimize_long_list() raises:
    def long_list(xs: List[Bool]) -> Bool:
        return len(xs) >= 70

    var xs = find(lists(booleans(), min_size=50), long_list)
    assert_equal(len(xs), 70)
    for x in xs:
        assert_equal(x, False)


def test_minimize_list_of_fairly_non_unique_ints() raises:
    def has_dup(xs: List[Int]) -> Bool:
        var s = Set[Int]()
        for x in xs:
            s.add(x)
        return len(s) < len(xs)

    var xs = find(lists(integers()), has_dup)
    assert_equal(xs, [0, 0])


def test_list_with_complex_sorting_structure() raises:
    def cond(xs: List[List[Bool]]) raises -> Bool:
        var rev = List[List[Bool]]()
        for t in xs:
            var r = t.copy()
            r.reverse()
            rev.append(r^)
        return _lex_gt(rev, xs) and len(xs) > 3

    var xs = find(lists(lists(booleans())), cond)
    assert_equal(len(xs), 4)


def _lex_gt(a: List[List[Bool]], b: List[List[Bool]]) -> Bool:
    """Python's list comparison `a > b` for lists of lists of bools."""
    for i in range(min(len(a), len(b))):
        ref x = a[i]
        ref y = b[i]
        for j in range(min(len(x), len(y))):
            if x[j] != y[j]:
                return x[j] and not y[j]
        if len(x) != len(y):
            return len(x) > len(y)
    return len(a) > len(b)


def test_list_with_wide_gap() raises:
    def cond(xs: List[Int]) -> Bool:
        if len(xs) == 0:
            return False
        var lo = xs[0]
        var hi = xs[0]
        for x in xs:
            lo = min(lo, x)
            hi = max(hi, x)
        return hi > lo + 10 and lo + 10 > 0

    var xs = find(lists(integers()), cond)
    assert_equal(len(xs), 2)
    var lo = min(xs[0], xs[1])
    var hi = max(xs[0], xs[1])
    assert_equal(hi, lo + 11)


def test_minimize_dict() raises:
    def big(d: Dict[Int, Bool]) -> Bool:
        return len(d) >= 3

    var d = find(dictionaries(integers(), booleans()), big)
    assert_equal(len(d), 3)
    for v in d.values():
        assert_equal(v, False)


def test_minimize_list_of_lists() raises:
    def cond(xs: List[List[Int]]) -> Bool:
        var n = 0
        for x in xs:
            if len(x) > 0:
                n += 1
        return n >= 3

    var xs = find(lists(lists(integers())), cond)
    assert_equal(len(xs), 3)
    for x in xs:
        assert_equal(x, [0])


def test_sum_of_pair_int() raises:
    def big(t: Tuple[Int, Int]) -> Bool:
        return t[0] + t[1] > 1000

    var t = find(tuples(integers(0, 1000), integers(0, 1000)), big)
    assert_equal(t[0], 1)
    assert_equal(t[1], 1000)


def test_sum_of_pair_float() raises:
    def big(t: Tuple[Float64, Float64]) -> Bool:
        return t[0] + t[1] > 1000

    var t = find(tuples(floats(0.0, 1000.0), floats(0.0, 1000.0)), big)
    assert_equal(t[0], 1.0)
    assert_equal(t[1], 1000.0)


def test_sum_of_pair_mixed() raises:
    def big(t: Tuple[Int, Float64]) -> Bool:
        return Float64(t[0]) + t[1] > 1000

    var t = find(tuples(integers(0, 1000), floats(0.0, 1000.0)), big)
    assert_equal(t[0], 1)
    assert_equal(t[1], 1000.0)


def test_lowering_together_positive() raises:
    def check(gap: Int) raises:
        def cond(t: Tuple[Int, Int]) {var gap} -> Bool:
            return t[0] + gap == t[1]

        var t = find(tuples(integers(0, 20), integers(0, 20)), cond)
        assert_equal(t[0], 0)
        assert_equal(t[1], gap)

    given(
        integers(0, 20),
        check,
        Settings(database=None, max_examples=10, deadline=None),
    )


def test_lowering_together_negative() raises:
    def check(gap: Int) raises:
        def cond(t: Tuple[Int, Int]) {var gap} -> Bool:
            return t[0] + gap == t[1]

        var t = find(tuples(integers(-20, 0), integers(-20, 0)), cond)
        assert_equal(t[0], 0)
        assert_equal(t[1], gap)

    given(
        integers(-20, 0),
        check,
        Settings(database=None, max_examples=10, deadline=None),
    )


def test_lowering_together_with_gap() raises:
    def check(gap: Int) raises:
        def cond(t: Tuple[Int, String, Float64, Int]) {var gap} -> Bool:
            return t[0] + gap == t[3]

        var t = find(
            tuples(integers(-10, 10), text(), floats(), integers(-10, 10)),
            cond,
        )
        assert_equal(t[0], 0)
        assert_equal(t[1], "")
        assert_equal(t[2], 0.0)
        assert_equal(t[3], gap)

    given(
        integers(-10, 10),
        check,
        Settings(database=None, max_examples=10, deadline=None),
    )


def test_perfectly_shrinks_integers() raises:
    for n in [-5, 0, 7, 100, 12345, -98765]:
        var target = n

        def ge(x: Int) {var target} -> Bool:
            return x >= target if target >= 0 else x <= target

        assert_equal(find(integers(), ge), n)


def test_minimal_float_above_one_and_a_half() raises:
    def gt(x: Float64) -> Bool:
        return x > 1.5

    assert_equal(find(floats(), gt), 2.0)


def test_minimal_fractional_float() raises:
    def frac(x: Float64) -> Bool:
        return x > 0 and x < 1

    assert_equal(find(floats(), frac), 0.5)


def test_minimal_infinite_float() raises:
    def inf_(x: Float64) -> Bool:
        return x == x and abs(x) > Float64.MAX_FINITE

    assert_equal(find(floats(), inf_), Float64.MAX_FINITE * 10)


def differs_from_lower(s: String) -> Bool:
    return s != s.lower()


def test_shrink_text_differs_from_lower_to_ascii() raises:
    # Hypothesis issue 4725: shrinking could get stuck on an accented
    # capital such as 'À' instead of reaching 'A'.
    assert_equal(find(text(min_size=1), differs_from_lower), "A")


def has_e(s: String) -> Bool:
    return "e" in s.lower() or "E" in s


def test_shrink_strips_accent_to_ascii_letter() raises:
    assert_equal(find(text(min_size=1), has_e), "E")


def lower_is(s: String, c: String) -> Bool:
    for cp in s.codepoints():
        if String(cp).lower() == c:
            return True
    return False


def has_t(s: String) -> Bool:
    return lower_is(s, "t")


def test_shrink_decomposes_compatibility_form_to_ascii() raises:
    # e.g. a Mathematical Bold Capital T reduces to "T"
    assert_equal(find(text(min_size=1), has_t), "T")


def has_f(s: String) -> Bool:
    return lower_is(s, "f")


def test_shrink_ligature_to_base_character() raises:
    # the ligature "ﬁ" decomposes (NFKD) to "fi"
    assert_equal(find(text(min_size=1), has_f), "F")


def differs_from_upper(s: String) -> Bool:
    return s != s.upper()


def test_shrink_text_differs_from_upper_to_ascii() raises:
    assert_equal(find(text(min_size=1), differs_from_upper), "a")


def test_minimal_text_containing_two_equal_chars() raises:
    def dup(s: String) -> Bool:
        var seen = Set[UInt32]()
        for c in s.codepoints():
            if c.to_u32() in seen:
                return True
            seen.add(c.to_u32())
        return False

    assert_equal(find(text(), dup), "00")


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
