# Strategies produce values within their bounds, and the combinators do what
# they say. Ported in spirit from hypothesis/tests/cover/test_simple_*.py,
# test_numerics.py, test_float_nastiness.py and test_recursive.py.

from std.testing import TestSuite, assert_equal, assert_true, assert_false
from std.collections import Set, Dict
from std.math import isnan, isinf

from proptest import *
from proptest.internal.charmap import category_intervals, as_general_categories


def fast() -> Settings:
    return Settings(database=None, max_examples=200)


def test_integers_respect_bounds() raises:
    def check(t: Tuple[Int, Int, Int]) raises:
        pass

    def prop(lo: Int, width: Int) raises:
        var hi = lo + width

        def inner(x: Int) raises {var lo, var hi}:
            assert_true(
                lo <= x and x <= hi, String(x, " not in [", lo, ", ", hi, "]")
            )

        given(integers(lo, hi), inner, Settings(database=None, max_examples=20))

    given(
        integers(-1000, 1000),
        integers(0, 100),
        prop,
        Settings(database=None, max_examples=20),
    )


def test_integers_full_range_reaches_extremes() raises:
    def big(x: Int) -> Bool:
        return x > (1 << 40)

    def small(x: Int) -> Bool:
        return x < -(1 << 40)

    assert_equal(find(integers(), big), (1 << 40) + 1)
    assert_equal(find(integers(), small), -(1 << 40) - 1)


def test_integers_of_dtypes() raises:
    def p8(x: UInt8) raises:
        pass

    given(integers_of[DType.uint8](), p8, fast())

    def p64(x: UInt64) raises:
        pass

    given(integers_of[DType.uint64](), p64, fast())

    def huge(x: UInt64) -> Bool:
        return x > UInt64(1) << 63

    assert_equal(find(integers_of[DType.uint64](), huge), (UInt64(1) << 63) + 1)

    def neg(x: Int8) -> Bool:
        return x < -100

    assert_equal(find(integers_of[DType.int8](), neg), Int8(-101))


def test_invalid_integer_bounds_raise() raises:
    var raised = False
    try:
        _ = integers(10, 0)
    except e:
        raised = "InvalidArgument" in String(e)
    assert_true(raised)


def test_floats_respect_bounds() raises:
    def prop(x: Float64) raises:
        assert_true(x >= -1.5 and x <= 2.5, String(x))

    given(floats(-1.5, 2.5), prop, fast())


def test_floats_without_nan_or_infinity() raises:
    def prop(x: Float64) raises:
        assert_false(isnan(x))
        assert_false(isinf(x))

    given(floats(allow_nan=False, allow_infinity=False), prop, fast())


def test_floats_exclude_bounds() raises:
    def prop(x: Float64) raises:
        assert_true(x > 0.0 and x < 1.0, String(x))

    given(floats(0.0, 1.0, exclude_min=True, exclude_max=True), prop, fast())


def test_floats_find_nan_and_infinity() raises:
    def is_nan(x: Float64) -> Bool:
        return isnan(x)

    assert_true(isnan(find(floats(), is_nan)))

    def is_neg_inf(x: Float64) -> Bool:
        return isinf(x) and x < 0

    assert_true(isinf(find(floats(), is_neg_inf)))


def test_floats_no_subnormals() raises:
    def prop(x: Float64) raises:
        assert_true(
            isnan(x) or x == 0.0 or abs(x) >= 2.2250738585072014e-308, String(x)
        )

    given(floats(allow_subnormal=False), prop, fast())


def test_floats32() raises:
    def prop(x: Float32) raises:
        assert_true(
            isnan(x) or isinf(x) or abs(Float64(x)) <= 3.4028234663852886e38
        )

    given(floats32(), prop, fast())

    def bounded(x: Float32) raises:
        assert_true(x >= 0 and x <= 1)

    given(floats32(0.0, 1.0), bounded, fast())


def test_booleans_both_values() raises:
    def t(b: Bool) -> Bool:
        return b

    assert_equal(find(booleans(), t), True)


def test_just_and_sampled_from() raises:
    def p(x: String) raises:
        assert_equal(x, "hello")

    given(just(String("hello")), p, fast())

    def q(x: Int) raises:
        assert_true(x == 3 or x == 5 or x == 7)

    given(sampled_from([3, 5, 7]), q, fast())

    def big(x: Int) -> Bool:
        return x > 3

    assert_equal(find(sampled_from([3, 5, 7]), big), 5)


def test_lists_sizes() raises:
    def prop(xs: List[Int]) raises:
        assert_true(len(xs) >= 2 and len(xs) <= 5, String(len(xs)))

    given(lists(integers(), min_size=2, max_size=5), prop, fast())


def test_unique_lists_are_unique() raises:
    def prop(xs: List[Int]) raises:
        var s = Set[Int]()
        for x in xs:
            assert_false(x in s, String("duplicate ", x))
            s.add(x)

    given(unique_lists(integers(0, 20)), prop, fast())


def _mod10(x: Int) -> Int:
    return x % 10


def test_unique_lists_by_key() raises:
    def prop(xs: List[Int]) raises:
        var s = Set[Int]()
        for x in xs:
            assert_false(x % 10 in s)
            s.add(x % 10)

    given(unique_lists_by(integers(0, 1000), _mod10), prop, fast())


def test_unique_lists_min_size_satisfiable() raises:
    def prop(xs: List[Int]) raises:
        assert_equal(len(xs), 5)

    given(unique_lists(integers(0, 4), min_size=5, max_size=5), prop, fast())


def test_sets_and_dictionaries() raises:
    def ps(s: Set[Int]) raises:
        assert_true(len(s) <= 4)

    given(sets(integers(0, 100), max_size=4), ps, fast())

    def pd(d: Dict[String, Int]) raises:
        assert_true(len(d) >= 1 and len(d) <= 3)

    given(
        dictionaries(
            text("ab", max_size=3), integers(), min_size=1, max_size=3
        ),
        pd,
        fast(),
    )


def test_text_alphabet_and_size() raises:
    def prop(s: String) raises:
        var n = 0
        for c in s.codepoints():
            assert_true(
                c.to_u32() == UInt32(ord("x")) or c.to_u32() == UInt32(ord("y"))
            )
            n += 1
        assert_true(n >= 1 and n <= 4)

    given(text("xy", min_size=1, max_size=4), prop, fast())


def test_text_is_valid_utf8_unicode() raises:
    def prop(s: String) raises:
        # round-trips through codepoints
        var t = String()
        for c in s.codepoints():
            t += String(c)
        assert_equal(s, t)

    given(text(), prop, fast())


def test_characters_ranges() raises:
    def prop(c: String) raises:
        var n = 0
        for cp in c.codepoints():
            assert_true(cp.to_u32() >= 0x41 and cp.to_u32() <= 0x5A)
            assert_true(cp.to_u32() != UInt32(ord("Q")))
            n += 1
        assert_equal(n, 1)

    given(
        characters(
            min_codepoint=0x41, max_codepoint=0x5A, exclude_characters="Q"
        ),
        prop,
        fast(),
    )

    def ascii_text(s: String) raises:
        for b in s.as_bytes():
            assert_true(b < 128)

    given(text(characters(max_codepoint=127)), ascii_text, fast())


def test_binary_sizes() raises:
    def prop(b: List[UInt8]) raises:
        assert_true(len(b) >= 1 and len(b) <= 8)

    given(binary(min_size=1, max_size=8), prop, fast())

    def nonzero(b: List[UInt8]) -> Bool:
        return len(b) > 0 and b[0] != 0

    assert_equal(find(binary(), nonzero), [UInt8(1)])


def _double(x: Int) -> Int:
    return x * 2


def _is_odd(x: Int) -> Bool:
    return x % 2 == 1


def test_map_and_filter() raises:
    def even(x: Int) raises:
        assert_equal(x % 2, 0)

    given(map(integers(-100, 100), _double), even, fast())

    def odd(x: Int) raises:
        assert_equal(x % 2, 1)

    given(filter(integers(0, 100), _is_odd), odd, fast())


def test_map_with_closure_and_lambda() raises:
    var offset = 1000

    def shift(x: Int) {var offset} -> Int:
        return x + offset

    def above(x: Int) raises:
        assert_true(x >= 1000)

    given(map(integers(0, 10), shift), above, fast())
    given(
        map(integers(0, 10), lambda (x: Int) {} -> Int: x + 1000), above, fast()
    )


def _upto(n: Int) raises -> Lists[Integers]:
    return lists(integers(0, n), max_size=5)


def test_flatmap() raises:
    def prop(xs: List[Int]) raises:
        pass

    given(flatmap(integers(0, 10), _upto), prop, fast())


def _sorted_pair(mut data: ConjectureData) raises -> Tuple[Int, Int]:
    var a = data.draw(integers(0, 100))
    var b = data.draw(integers(a, 100))
    return (a, b)


def test_composite() raises:
    def prop(t: Tuple[Int, Int]) raises:
        assert_true(t[0] <= t[1])

    given(composite(_sorted_pair), prop, fast())

    def far(t: Tuple[Int, Int]) -> Bool:
        return t[1] - t[0] >= 10

    var t = find(composite(_sorted_pair), far)
    assert_equal(t[0], 0)
    assert_equal(t[1], 10)


def test_tuples() raises:
    def p2(t: Tuple[Int, Bool]) raises:
        assert_true(t[0] >= 0 and t[0] <= 3)

    given(tuples(integers(0, 3), booleans()), p2, fast())

    def p4(t: Tuple[Int, Int, Int, Int]) raises:
        assert_true(t[3] == 7)

    given(tuples(integers(), integers(), integers(), just(7)), p4, fast())


def test_one_of_and_boxed() raises:
    def prop(x: Int) raises:
        assert_true((x >= 0 and x <= 20) or (x >= 100 and x <= 110) or x == -1)

    given(one_of(integers(0, 10), integers(100, 110), just(-1)), prop, fast())
    var strategies: List[BoxedStrategy[Int]] = [
        boxed(integers(0, 10)),
        boxed(map(integers(0, 10), _double)),
    ]
    given(one_of(strategies^), prop, fast())


def test_one_of_is_unboxed_and_takes_up_to_six() raises:
    # a capturing lambda makes `map` non-copyable; unboxed one_of doesn't care
    var offset = 1000
    var shifted = map(
        integers(0, 5), lambda (x: Int) {offset} -> Int: x + offset
    )
    var s = one_of(just(0), just(1), just(2), just(3), just(4), shifted^)

    def at_least_five(x: Int) -> Bool:
        return x >= 5

    assert_equal(find(s, at_least_five), 1000)

    def anything(x: Int) -> Bool:
        return True

    # shrinks towards the first alternative
    assert_equal(find(one_of(integers(10, 20), integers(0, 5)), anything), 10)


def test_one_of_weights() raises:
    var s = one_of(just(0), just(1), just(2), weights=[1, 8, 1])
    var counts: List[Int] = [0, 0, 0]
    for _ in range(1000):
        counts[example(s)] += 1
    assert_true(counts[1] > 650 and counts[1] < 950, String(counts))
    assert_true(counts[0] > 0 and counts[2] > 0, String(counts))

    def anything(x: Int) -> Bool:
        return True

    # weights don't change the shrink order
    assert_equal(find(s, anything), 0)

    var boxes: List[BoxedStrategy[Int]] = [boxed(just(0)), boxed(just(1))]
    var w = one_of(boxes^, weights=[1, 19])
    var ones = 0
    for _ in range(500):
        ones += example(w)
    assert_true(ones > 400, String(ones))

    var msg = String()
    try:
        _ = one_of(just(0), just(1), weights=[1])
    except e:
        msg = String(e)
    assert_true("2 strategies" in msg, msg)
    msg = String()
    try:
        _ = one_of(just(0), just(1), weights=[1, 0])
    except e:
        msg = String(e)
    assert_true("positive" in msg, msg)


def test_optionals() raises:
    def some(x: Optional[Int]) -> Bool:
        return Bool(x)

    var x = find(optionals(integers(5, 10)), some)
    assert_equal(x.value(), 5)

    def none(x: Optional[Int]) -> Bool:
        return True

    assert_false(Bool(find(optionals(integers()), none)))


def test_permutations() raises:
    def prop(xs: List[Int]) raises:
        var s = Set[Int]()
        for x in xs:
            s.add(x)
        assert_equal(len(xs), 5)
        assert_equal(len(s), 5)

    given(permutations([1, 2, 3, 4, 5]), prop, fast())

    def anything(xs: List[Int]) -> Bool:
        return True

    assert_equal(find(permutations([1, 2, 3]), anything), [1, 2, 3])


def _leaf(x: Int) -> String:
    return String(x)


def _node(children: List[String]) -> String:
    var s = String("[")
    for i in range(len(children)):
        if i > 0:
            s += ", "
        s += children[i]
    return s + "]"


def _depth(s: String) -> Int:
    var d = 0
    var best = 0
    for b in s.as_bytes():
        if b == UInt8(ord("[")):
            d += 1
            best = max(best, d)
        elif b == UInt8(ord("]")):
            d -= 1
    return best


def _extend(s: BoxedStrategy[String]) raises -> BoxedStrategy[String]:
    return boxed(map(lists(s.copy(), max_size=3), _node))


def test_recursive() raises:
    """Nested lists of small integers (Hypothesis's canonical recursive()
    example), rendered as strings since Mojo structs can't hold a List of
    themselves."""
    var trees = recursive(map(integers(0, 9), _leaf), _extend, max_leaves=10)

    def prop(t: String) raises:
        assert_true(t.byte_length() >= 1)

    given(trees.copy(), prop, fast())

    def deep(t: String) -> Bool:
        return _depth(t) >= 3

    assert_equal(find(trees, deep), "[[[]]]")


@fieldwise_init
struct Point(Copyable, Writable):
    var x: Int
    var y: Int


struct Points(Copyable, Strategy):
    """The custom strategy from the README."""

    comptime Value = Point

    def __init__(out self):
        pass

    def do_draw(self, mut data: ConjectureData) raises -> Point:
        return Point(data.draw(integers(0, 100)), data.draw(integers(0, 100)))


def test_custom_strategy() raises:
    def far(p: Point) -> Bool:
        return p.x + p.y > 150

    var p = find(Points(), far)
    assert_equal(p.x + p.y, 151)
    var ps = find(
        lists(Points(), min_size=2), lambda (ps: List[Point]) {} -> Bool: True
    )
    assert_equal(len(ps), 2)


def test_shared_values_are_shared() raises:
    var x = shared(integers(0, 1000))

    def prop(t: Tuple[Int, Int, Int]) raises:
        assert_equal(t[0], t[1])

    given(tuples(x.copy(), x.copy(), integers()), prop, fast())

    # different keys draw independently
    def differ(t: Tuple[Int, Int]) -> Bool:
        return t[0] != t[1]

    var t = find(
        tuples(shared(integers(0, 9), "a"), shared(integers(0, 9), "b")), differ
    )
    assert_equal(t[0] + t[1], 1)

    # the same explicit key shares across different strategies
    def same_key(t: Tuple[Int, Int]) raises:
        assert_equal(t[0], t[1])

    given(
        tuples(shared(integers(0, 9), "k"), shared(integers(0, 9), "k")),
        same_key,
        fast(),
    )


def test_tuples_of_five_and_six() raises:
    def p5(t: Tuple[Int, Int, Int, Int, Bool]) raises:
        assert_true(t[0] >= 0 and t[3] <= 3)

    given(
        tuples(
            integers(0, 3),
            integers(0, 3),
            integers(0, 3),
            integers(0, 3),
            booleans(),
        ),
        p5,
        fast(),
    )

    def big(t: Tuple[Int, Int, Int, Int, Int, Int]) -> Bool:
        return t[5] > 2

    var t = find(
        tuples(
            integers(),
            integers(),
            integers(),
            integers(),
            integers(),
            integers(),
        ),
        big,
    )
    assert_equal(t[0], 0)
    assert_equal(t[5], 3)


# --- Unicode categories (hypothesis/tests/cover/test_simple_characters.py) ---


def _first_cp(c: String) -> UInt32:
    for cp in c.codepoints():
        return cp.to_u32()
    return 0


def _category_of(c: String) raises -> String:
    var cp = _first_cp(c)
    for cat in ["Lu", "Ll", "Nd", "Zs", "Po"]:
        if cp in category_intervals([String(cat)]):
            return String(cat)
    return "other"


def test_characters_categories() raises:
    def upper_or_digit(c: String) raises:
        var cat = _category_of(c)
        assert_true(cat == "Lu" or cat == "Nd", String(repr(c), " is ", cat))

    given(characters(categories=["Lu", "Nd"]), upper_or_digit, fast())

    def letter(c: String) raises:
        var cp = _first_cp(c)
        assert_true(cp in category_intervals(as_general_categories(["L"])))

    given(characters(categories=["L"]), letter, fast())

    def no_letters(c: String) raises:
        var cp = _first_cp(c)
        assert_false(cp in category_intervals(as_general_categories(["L"])))

    given(characters(exclude_categories=["L"]), no_letters, fast())


def test_characters_codec_and_errors() raises:
    def latin1(c: String) raises:
        assert_true(_first_cp(c) <= 255)

    given(characters(codec="latin-1"), latin1, fast())
    var raised = False
    try:
        _ = characters(categories=["Xx"])
    except e:
        raised = "not a Unicode category" in String(e)
    assert_true(raised)
    raised = False
    try:
        _ = characters(categories=["L"], exclude_categories=["N"])
    except e:
        raised = "at most one" in String(e)
    assert_true(raised)


def test_minimal_digit_is_zero() raises:
    def any_c(c: String) -> Bool:
        return True

    assert_equal(find(characters(categories=["Nd"]), any_c), "0")


# --- from_regex (hypothesis/tests/cover/test_regex.py) ---


def _all_in(s: String, alphabet: String) -> Bool:
    for c in s.codepoints():
        var found = False
        for a in alphabet.codepoints():
            if a == c:
                found = True
        if not found:
            return False
    return True


def test_regex_fullmatch_classes_and_repeats() raises:
    def prop(s: String) raises:
        var n = len(s.codepoints())
        assert_true(n >= 2 and n <= 4, repr(s))
        assert_true(_all_in(s, "abcxyz"), repr(s))

    given(from_regex("[a-c]{1,2}[x-z]{1,2}", fullmatch=True), prop, fast())


def test_regex_alternation_and_groups() raises:
    def prop(s: String) raises:
        assert_true(
            s == "foofoo" or s == "foobar" or s == "barfoo" or s == "barbar",
            repr(s),
        )

    given(from_regex("(foo|bar){2}", fullmatch=True), prop, fast())


def test_regex_digits_are_unicode_digits() raises:
    def prop(s: String) raises:
        assert_equal(len(s.codepoints()), 3)
        for c in s.codepoints():
            assert_true(c.to_u32() in category_intervals(["Nd"]))

    given(from_regex("\\d{3}", fullmatch=True), prop, fast())


def test_regex_search_pads_unless_anchored() raises:
    def contains(s: String) -> Bool:
        return s != "abc"

    # unanchored: the match can be surrounded by other text
    var padded = find(from_regex("abc"), contains)
    assert_true("abc" in padded, repr(padded))

    def anchored(s: String) raises:
        assert_true(s == "abc" or s == "abc\n", repr(s))

    given(from_regex("^abc$"), anchored, fast())

    def strict(s: String) raises:
        assert_equal(s, "abc")

    given(from_regex("\\Aabc\\Z"), strict, fast())


def test_regex_ignore_case_and_negated_class() raises:
    def ci(s: String) raises:
        assert_equal(s.lower(), "hi")

    given(from_regex("(?i)hi", fullmatch=True), ci, fast())

    def not_lower(s: String) raises:
        for c in s.codepoints():
            assert_false(
                c.to_u32() >= UInt32(ord("a"))
                and c.to_u32() <= UInt32(ord("z"))
            )

    given(from_regex("[^a-z]+", fullmatch=True), not_lower, fast())


def test_regex_shrinks() raises:
    def any_s(s: String) -> Bool:
        return True

    assert_equal(
        find(from_regex("[a-z]+@[a-z]+\\.(com|org)", fullmatch=True), any_s),
        "a@a.com",
    )


def test_regex_unsupported_syntax_raises() raises:
    for pat in ["(a)\\1", "(?=a)b", "a\\bb", "a^b", "(abc"]:
        var raised = False
        try:
            _ = from_regex(pat)
        except e:
            raised = "InvalidArgument" in String(e)
        assert_true(raised, pat)


# --- from_type (hypothesis/tests/cover/test_lookup.py, in spirit) ---


@fieldwise_init
struct Pixel(Copyable, Writable):
    var x: UInt16
    var y: UInt16
    var lit: Bool
    var name: String

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "Pixel(",
            self.x,
            ", ",
            self.y,
            ", ",
            self.lit,
            ", ",
            repr(self.name),
            ")",
        )


@fieldwise_init
struct Range(Arbitrary, Copyable, Writable):
    var lo: Int
    var hi: Int

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        var lo = data.draw(integers(-100, 100))
        return Self(lo, data.draw(integers(lo, 100)))

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Range(", self.lo, ", ", self.hi, ")")


@fieldwise_init
struct Sprite(Copyable, Writable):
    var at: Pixel
    var extent: Range
    var tags: List[String]
    var layer: Optional[Int8]
    var colors: Set[UInt8]

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "Sprite(",
            self.at,
            ", ",
            self.extent,
            ", ",
            len(self.tags),
            " tags)",
        )


def test_from_type_scalars() raises:
    def p(x: Int, y: UInt8, z: Float64, b: Bool, s: String) raises:
        pass

    given(
        from_type[Int](),
        from_type[UInt8](),
        from_type[Float64](),
        from_type[Bool](),
        from_type[String](),
        p,
        fast(),
    )

    def big(x: UInt16) -> Bool:
        return x > 60000

    assert_equal(find(from_type[UInt16](), big), UInt16(60001))


def test_from_type_containers() raises:
    def p(
        xs: List[Int], o: Optional[String], s: Set[Int64], d: Dict[String, Bool]
    ) raises:
        pass

    given(
        from_type[List[Int]](),
        from_type[Optional[String]](),
        from_type[Set[Int64]](),
        from_type[Dict[String, Bool]](),
        p,
        fast(),
    )


def test_from_type_nested_containers_and_tuples() raises:
    def p(
        a: List[List[Int]],
        b: Optional[List[String]],
        c: Dict[String, List[Bool]],
        d: Tuple[Int, String],
        e: List[Tuple[UInt8, Bool]],
        f: Tuple[Int, Float64, Bool],
    ) raises:
        pass

    given(
        from_type[List[List[Int]]](),
        from_type[Optional[List[String]]](),
        from_type[Dict[String, List[Bool]]](),
        from_type[Tuple[Int, String]](),
        from_type[List[Tuple[UInt8, Bool]]](),
        from_type[Tuple[Int, Float64, Bool]](),
        p,
        fast(),
    )

    def nested(xs: List[List[Int]]) -> Bool:
        return len(xs) >= 2 and len(xs[1]) >= 1

    assert_equal(find(from_type[List[List[Int]]](), nested), [[], [0]])


def test_from_type_any_depth_and_arity() raises:
    def p(
        a: Dict[Int8, List[Optional[Tuple[Bool, String]]]],
        b: List[List[List[UInt16]]],
        c: Tuple[Int],
        d: Tuple[Int, Bool, String, Float32, UInt8, List[Int]],
        e: Set[Tuple[Int, Bool]],
        f: Optional[Optional[Int64]],
    ) raises:
        pass

    check(p, fast())

    def deep(xs: List[List[List[UInt16]]]) -> Bool:
        return len(xs) >= 1 and len(xs[0]) >= 1 and len(xs[0][0]) >= 2

    assert_equal(find(from_type[List[List[List[UInt16]]]](), deep), [[[0, 0]]])

    def keyed(d: Dict[Int8, Bool]) -> Bool:
        return len(d) >= 2

    var d = find(from_type[Dict[Int8, Bool]](), keyed)
    assert_equal(len(d), 2)


def test_from_type_structs_and_arbitrary() raises:
    def p(s: Sprite) raises:
        assert_true(s.extent.lo <= s.extent.hi)

    given(from_type[Sprite](), p, fast())

    def interesting(s: Sprite) -> Bool:
        return (
            s.at.x > 100 and len(s.tags) > 1 and s.extent.hi - s.extent.lo > 5
        )

    var s = find(from_type[Sprite](), interesting)
    assert_equal(s.at.x, 101)
    assert_equal(s.at.y, 0)
    assert_equal(len(s.tags), 2)
    assert_equal(s.extent.lo, 0)
    assert_equal(s.extent.hi, 6)
    assert_false(Bool(s.layer))
    assert_equal(len(s.colors), 0)


def test_check_infers_strategies_from_parameter_types() raises:
    var calls = 0

    def one(xs: List[Int]) raises {mut calls}:
        calls += 1
        var ys = xs.copy()
        ys.reverse()
        ys.reverse()
        assert_equal(xs, ys)

    check(one, fast())
    assert_true(calls > 0)

    def two(s: Sprite, n: UInt8) raises:
        assert_true(s.extent.lo <= s.extent.hi)
        assert_true(Int(n) <= 255)

    check(two, fast())

    def six(
        a: Int, b: Bool, c: String, d: Float64, e: Int8, f: List[Int]
    ) raises:
        pass

    check(six, fast())

    def bool_prop(a: Int, b: Int) raises -> Bool:
        return a + b == b + a

    check(bool_prop, fast())


def test_check_reports_shrunk_failures() raises:
    def raising(a: Int, b: Int) raises:
        if a >= 1000:
            fail("too big")

    var msg = String()
    try:
        check(raising, fast())
    except e:
        msg = String(e)
    assert_true("given(\n        1000," in msg, msg)
    assert_true("too big" in msg, msg)
    assert_true("test_strategies.mojo" in msg, msg)

    def returns_false(xs: List[UInt8]) raises -> Bool:
        return len(xs) < 3

    msg = String()
    try:
        check(returns_false, fast())
    except e:
        msg = String(e)
    assert_true("given([0, 0, 0])" in msg, msg)
    assert_true("returned False" in msg, msg)


def test_example_returns_values() raises:
    for _ in range(10):
        var x = example(integers(0, 5))
        assert_true(x >= 0 and x <= 5)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
