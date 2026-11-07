# The internal machinery, mostly tested with proptest itself. Ported in
# spirit from hypothesis/tests/conjecture/test_choice.py, test_float_encoding.py,
# test_intervalset.py, test_shrinker.py and the shrinking/ tests.

from std.testing import TestSuite, assert_equal, assert_true, assert_false
from std.memory import ArcPointer
from std.math import isnan, floor

from proptest import *
from proptest.internal.choice import (
    ChoiceValue,
    Constraints,
    integer_index,
    integer_from_index,
    choice_permitted,
    choice_simplest,
    choice_compare,
    choice_from_index,
    zigzag_index,
    zigzag_value,
)
from proptest.internal.floats import (
    float_to_lex,
    lex_to_float,
    next_up,
    next_down,
    float_to_int,
)
from proptest.internal.intervals import IntervalSet, codepoints_to_string
from proptest.internal.shrinking import (
    find_integer,
    shrink_integer,
    shrink_float,
    shrink_collection,
    shrink_ordering,
)
from proptest.database import (
    choices_to_string,
    choices_from_string,
    ExampleDatabase,
    encode_blob,
    decode_blob,
)
from proptest.internal.shrinker import _simpler_case_chars
from proptest.internal.decomposition import Decompositions
from proptest.internal.charmap import (
    category_intervals,
    as_general_categories,
    all_categories,
)
from proptest.internal.pareto import (
    ParetoFront,
    dominance,
    LEFT_DOMINATES,
    RIGHT_DOMINATES,
    NO_DOMINANCE,
    EQUAL,
)
from proptest.internal.data import ConjectureResult, Result
from proptest.internal.choice import ChoiceNode
from proptest.internal.random import Random


def settings() -> Settings:
    return Settings(database=None, max_examples=300)


# --- choice indices -------------------------------------------------------------


def test_bounded_integer_index_order_matches_hypothesis() raises:
    # range [-2, 5], shrink_towards 2: 2 3 1 4 0 5 -1 -2
    var c = Constraints.integer(Int128(-2), Int128(5), 2)
    var expected: List[Int] = [2, 3, 1, 4, 0, 5, -1, -2]
    for i in range(8):
        assert_equal(Int(integer_from_index(UInt128(i), c)), expected[i])


def test_integer_index_roundtrip() raises:
    def prop(lo: Int, width: Int, offset: Int, towards: Int) raises:
        var hi = lo + width
        var v = lo + offset % (width + 1)
        var c = Constraints.integer(Int128(lo), Int128(hi), Int128(towards))
        var i = integer_index(Int128(v), c)
        assert_true(i <= UInt128(width), "index out of range")
        assert_equal(Int(integer_from_index(i, c)), v)

    given(
        integers(-1000, 1000),
        integers(0, 1000),
        integers(0, 10**6),
        integers(-2000, 2000),
        prop,
        settings(),
    )


def test_semibounded_and_unbounded_roundtrip() raises:
    def prop(v: Int, bound: Int) raises:
        var below = Constraints.integer(Int128(min(v, bound)), None)
        var above = Constraints.integer(None, Int128(max(v, bound)))
        var free = Constraints.integer()
        for c in [below.copy(), above.copy(), free.copy()]:
            assert_equal(
                Int(integer_from_index(integer_index(Int128(v), c), c)), v
            )

    given(integers(-(1 << 60), 1 << 60), integers(-100, 100), prop, settings())


def test_zigzag() raises:
    def prop(v: Int, s: Int) raises:
        assert_equal(
            Int(zigzag_value(zigzag_index(Int128(v), Int128(s)), Int128(s))), v
        )

    given(
        integers(-(1 << 60), 1 << 60), integers(-1000, 1000), prop, settings()
    )


def test_simplest_choice_is_permitted() raises:
    def prop(lo: Int, width: Int) raises:
        var c = Constraints.integer(Int128(lo), Int128(lo + width))
        var s = choice_simplest(c)
        assert_true(choice_permitted(s, c))
        if lo <= 0 and lo + width >= 0:
            assert_equal(Int(s.i), 0)

    given(integers(-100, 100), integers(0, 100), prop, settings())


def test_string_choice_from_index() raises:
    var c = Constraints.string(ArcPointer(IntervalSet.from_string("ab")), 0, 3)
    # "" then single characters, then pairs, in shrink order
    assert_equal(codepoints_to_string(choice_from_index(0, c).seq), "")
    assert_equal(codepoints_to_string(choice_from_index(1, c).seq), "a")
    assert_equal(codepoints_to_string(choice_from_index(2, c).seq), "b")
    assert_equal(codepoints_to_string(choice_from_index(3, c).seq), "aa")


# --- floats -----------------------------------------------------------------------


def test_float_lex_roundtrip() raises:
    def prop(x: Float64) raises:
        var f = abs(x)
        if isnan(f):
            return
        assert_equal(
            float_to_int(lex_to_float(float_to_lex(f))), float_to_int(f)
        )

    given(floats(), prop, settings())


def test_integral_floats_are_simpler_than_fractional() raises:
    def prop(n: Int, frac: Float64) raises:
        var whole = Float64(n)
        var fractional = Float64(n) + frac
        # for large n the sum can round back to an integer
        assume(fractional != floor(fractional))
        assert_true(float_to_lex(whole) < float_to_lex(fractional))

    given(integers(0, 1 << 50), floats(0.01, 0.99), prop, settings())


def test_floats_order_integers_by_value() raises:
    def prop(a: Int, b: Int) raises:
        if a < b:
            assert_true(float_to_lex(Float64(a)) < float_to_lex(Float64(b)))

    given(integers(0, 1 << 52), integers(0, 1 << 52), prop, settings())


def test_next_up_down() raises:
    def prop(x: Float64) raises:
        assert_true(next_up(x) > x)
        assert_true(next_down(x) < x)
        assert_equal(next_down(next_up(x)), x)

    given(floats(-1e300, 1e300), prop, settings())


# --- intervals --------------------------------------------------------------------


def test_interval_shrink_order_roundtrip() raises:
    var s = IntervalSet.default_text()

    def prop(i: Int) raises {s}:
        var c = s.char_in_shrink_order(i)
        assert_equal(s.index_from_char_in_shrink_order(c), i)

    given(integers(0, len(s) - 1), prop, settings())


def test_interval_shrink_order_starts_with_digits() raises:
    var s = IntervalSet.default_text()
    assert_equal(Int(s.char_in_shrink_order(0)), ord("0"))
    assert_equal(Int(s.char_in_shrink_order(1)), ord("1"))
    assert_equal(Int(s.char_in_shrink_order(10)), ord(":"))


def test_interval_set_operations() raises:
    var a = IntervalSet.range(0, 100)
    var b = IntervalSet.range(50, 150)
    assert_equal(len(a.union(b)), 151)
    assert_equal(len(a.intersection(b)), 51)
    assert_equal(len(a.difference(b)), 50)
    assert_true(UInt32(75) in a.intersection(b))
    assert_false(UInt32(75) in a.difference(b))


# --- serialization ---------------------------------------------------------------


def test_choices_serialization_roundtrip() raises:
    def prop(n: Int, f: Float64, b: Bool, s: String) raises:
        var choices = List[ChoiceValue]()
        choices.append(ChoiceValue(integer=Int128(n) * 1000))
        choices.append(ChoiceValue(float=f))
        choices.append(ChoiceValue(boolean=b))
        var cps = List[UInt32]()
        for c in s.codepoints():
            cps.append(c.to_u32())
        choices.append(ChoiceValue(string=cps^))
        var back = choices_from_string(choices_to_string(choices))
        assert_true(back == choices)

    given(integers(), floats(), booleans(), text(), prop, settings())


def test_blob_roundtrip() raises:
    var choices = List[ChoiceValue]()
    choices.append(ChoiceValue(integer=-12345))
    choices.append(ChoiceValue(float=2.5))
    choices.append(ChoiceValue(boolean=True))
    var back = decode_blob(encode_blob(choices))
    assert_true(back == choices)
    var raised = False
    try:
        _ = decode_blob("not a blob")
    except:
        raised = True
    assert_true(raised)


def test_simpler_case_chars() raises:
    var s = IntervalSet.default_text()
    assert_equal(_simpler_case_chars(UInt32(ord("a")), s), [UInt32(ord("A"))])
    # uppercase is already simpler than lowercase
    assert_equal(len(_simpler_case_chars(UInt32(ord("A")), s)), 0)
    # a-grave -> A-grave
    assert_equal(_simpler_case_chars(0xE0, s), [UInt32(0xC0)])
    # only characters in the alphabet are offered
    assert_equal(
        len(
            _simpler_case_chars(UInt32(ord("a")), IntervalSet.from_string("ab"))
        ),
        0,
    )


def test_unicode_category_sizes() raises:
    # Unicode 15.0 counts
    assert_equal(len(category_intervals(["Nd"])), 680)
    assert_equal(len(category_intervals(["Lu"])), 1831)
    assert_equal(len(as_general_categories(["L"])), 5)
    assert_equal(len(all_categories()), 30)


def _result(
    n: Int, score: Float64, status: Status = Status.VALID
) -> ConjectureResult:
    var r = ConjectureResult(id=n + 1, status=status)
    for _ in range(n):
        r.nodes.append(
            ChoiceNode(ChoiceValue(integer=1), Constraints.integer(), False)
        )
    r.target_observations["s"] = score
    return r^


def test_pareto_dominance() raises:
    # simpler and at least as good dominates
    assert_equal(dominance(_result(1, 5.0), _result(2, 5.0)), LEFT_DOMINATES)
    assert_equal(dominance(_result(2, 5.0), _result(1, 5.0)), RIGHT_DOMINATES)
    # simpler but worse: a trade-off
    assert_equal(dominance(_result(1, 4.0), _result(2, 5.0)), NO_DOMINANCE)
    assert_equal(dominance(_result(2, 5.0), _result(2, 5.0)), EQUAL)


def test_pareto_front_keeps_tradeoffs() raises:
    var front = ParetoFront(Random(1))
    assert_true(front.add(Result(_result(3, 3.0))))
    assert_true(front.add(Result(_result(1, 1.0))))  # simpler, lower score
    assert_equal(len(front), 2)
    # dominates the 3-choice member: simpler and better
    assert_true(front.add(Result(_result(2, 4.0))))
    assert_equal(len(front), 2)
    assert_equal(len(front.evicted), 1)
    # dominated by the 2-choice member
    assert_false(front.add(Result(_result(4, 2.0))))


def test_decompositions() raises:
    var d = Decompositions()
    # é = e + combining acute
    assert_equal(d.components(0xE9), [UInt32(0x65), UInt32(0x301)])
    # ﬁ -> f, i (NFKD)
    assert_equal(d.components(0xFB01), [UInt32(ord("f")), UInt32(ord("i"))])
    # Hangul syllables are decomposed algorithmically
    assert_equal(
        d.components(0xAC01), [UInt32(0x1100), UInt32(0x1161), UInt32(0x11A8)]
    )
    assert_equal(len(d.components(UInt32(ord("a")))), 0)
    var s = IntervalSet.default_text()
    # À -> A via decomposition (its lowercase à is not simpler)
    var cands = _simpler_case_chars(0xC0, s, d^)
    assert_equal(cands[0], UInt32(ord("A")))


def test_in_memory_database() raises:
    var db = ExampleDatabase.in_memory()
    var a = List[ChoiceValue]()
    a.append(ChoiceValue(integer=5))
    db.save("k", a)
    db.save("k", a)
    assert_equal(len(db.fetch("k")), 1)
    db.delete("k", a)
    assert_equal(len(db.fetch("k")), 0)


# --- value shrinkers ---------------------------------------------------------------


def test_find_integer() raises:
    def prop(n: Int) raises:
        def below(k: Int) raises {var n} -> Bool:
            return k <= n

        assert_equal(find_integer(below), n)

    given(integers(0, 100000), prop, settings())


def test_integer_shrinker_finds_threshold() raises:
    def prop(start: Int, threshold: Int) raises:
        var t = min(threshold, start)

        def ok(v: UInt128) raises {var t} -> Bool:
            return v >= UInt128(t)

        assert_equal(Int(shrink_integer(UInt128(start), ok)), t)

    given(integers(0, 1 << 40), integers(0, 1 << 40), prop, settings())


def test_float_shrinker_prefers_integers() raises:
    def gt(x: Float64) raises -> Bool:
        return x > 10.3

    assert_equal(shrink_float(1234.5678, gt), 11.0)


def test_collection_shrinker_deletes_and_sorts() raises:
    def has_three_big(xs: List[Int]) raises -> Bool:
        var n = 0
        for x in xs:
            if x >= 5:
                n += 1
        return n >= 3

    assert_equal(
        shrink_collection([9, 1, 7, 2, 8, 6], 0, has_three_big), [5, 5, 5]
    )


def test_ordering_shrinker_sorts() raises:
    def anything(xs: List[Int]) raises -> Bool:
        return True

    # items sorted by keys[item]: keys[1]=10 < keys[2]=20 < keys[0]=30
    assert_equal(shrink_ordering([2, 0, 1], [30, 10, 20], anything), [1, 2, 0])


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
