# Smaller API pieces, mostly from Rust proptest and QuickCheck: filter
# reasons, filter_map, Outcome results, expect_failure, Poly types,
# subsequence and Index, run_property, and generated functions; and from
# RapidCheck: build/field, apply, weighted sampled_from, and
# before_minimal_test_case.

from std.testing import TestSuite, assert_equal, assert_true, assert_false

from proptest import *


def fast() -> Settings:
    return Settings(database=None, max_examples=200)


def test_filter_reason_in_health_check() raises:
    def prop(x: Int) raises:
        pass

    var msg = String()
    try:
        given(
            filter(
                integers(),
                lambda (x: Int) -> Bool: x == 12345,
                reason="equal to 12345",
            ),
            prop,
            fast(),
        )
    except e:
        msg = String(e)
    assert_true("filter_too_much" in msg, msg)
    assert_true("equal to 12345 (" in msg, msg)


def _even_half(x: Int) raises -> Optional[Int]:
    if x % 2 == 0:
        return x // 2
    return None


def test_filter_map() raises:
    def prop(h: Int) raises:
        assert_true(h >= 0 and h <= 50)

    given(filter_map(integers(0, 100), _even_half), prop, fast())

    def big(h: Int) -> Bool:
        return h > 20

    assert_equal(find(filter_map(integers(0, 100), _even_half), big), 21)


def test_outcome_results() raises:
    def division(a: Int8, b: Int8) -> Outcome:
        if b == 0:
            return Outcome.discard()
        var q = Int(a) // Int(b)
        return Outcome.of(q * Int(b) + Int(a) % Int(b) == Int(a), "identity")

    check(division, fast())

    def small(a: UInt8) -> Outcome:
        return Outcome.of(a < 100, "a is too big")

    var msg = String()
    try:
        check(small, fast())
    except e:
        msg = String(e)
    assert_true("given(100)" in msg, msg)
    assert_true("check: a is too big" in msg, msg)


def test_expect_failure() raises:
    def short(xs: List[Int]) -> Bool:
        return len(xs) < 3

    def run_short() raises:
        check(short, fast())

    var report = expect_failure(run_short)
    assert_true("given([0, 0, 0])" in report, report)

    def always(x: Int) -> Bool:
        return True

    var msg = String()
    try:

        def run_always() raises:
            check(always, fast())

        _ = expect_failure(run_always)
    except e:
        msg = String(e)
    assert_true("should have failed" in msg, msg)


def _reverse[T: Copyable](xs: List[T]) -> List[T]:
    var out = List[T]()
    for i in range(len(xs) - 1, -1, -1):
        out.append(xs[i].copy())
    return out^


def test_poly_types() raises:
    def reverse_twice(xs: List[PolyA]) -> Bool:
        return _reverse(_reverse(xs)) == xs

    check(reverse_twice, fast())

    def first_is_last(xs: List[PolyA]) -> Bool:
        return len(xs) == 0 or _reverse(xs)[0] == xs[0]

    var msg = String()
    try:
        check(first_is_last, fast())
    except e:
        msg = String(e)
    assert_true(
        "given([A(0), A(1)])" in msg or "given([A(1), A(0)])" in msg, msg
    )

    def pairs(d: Dict[PolyB, PolyC]) -> Bool:
        return len(d) >= 0

    check(pairs, fast())


def test_subsequence() raises:
    var base: List[Int] = [1, 2, 3, 4, 5, 6, 7, 8]

    def ordered(xs: List[Int]) raises:
        assert_true(len(xs) >= 2 and len(xs) <= 5, String(xs))
        for i in range(1, len(xs)):
            assert_true(xs[i - 1] < xs[i])

    given(subsequence(base.copy(), min_size=2, max_size=5), ordered, fast())

    def anything(xs: List[Int]) -> Bool:
        return True

    assert_equal(find(subsequence(base.copy(), min_size=2), anything), [7, 8])

    def has_three(xs: List[Int]) raises -> Bool:
        return 3 in xs

    assert_equal(find(subsequence(base.copy()), has_three), [3])


def test_index() raises:
    def prop(i: Index, xs: List[Int]) raises:
        if len(xs) > 0:
            var k = i.get(len(xs))
            assert_true(k >= 0 and k < len(xs))

    check(prop, fast())

    def at_least_half(i: Index) raises -> Bool:
        return i.get(10) >= 5

    assert_equal(find(from_type[Index](), at_least_half).get(10), 5)


def test_run_property() raises:
    def short(xs: List[Int]) raises:
        if len(xs) >= 2:
            fail("too long")

    var r = run_property(lists(integers()), short, fast())
    assert_false(r.passed())
    assert_equal(r.counterexample.value(), [0, 0])
    assert_true("too long" in r.message, r.message)
    assert_true(r.blob.startswith("proptest"), r.blob)
    # the blob replays the counterexample
    var replay = run_property(
        lists(integers()), short, Settings(database=None, reproduce=r.blob)
    )
    assert_equal(replay.counterexample.value(), [0, 0])

    def fine(xs: List[Int]) raises:
        pass

    var ok = run_property(lists(integers()), fine, fast())
    assert_true(ok.passed())
    assert_false(Bool(ok.counterexample))
    assert_true(ok.report.valid >= 200)


def test_functions() raises:
    def memoized(f: Function[Int, Int], x: Int) raises:
        assert_equal(f(x), f(x))
        var g = f.copy()
        assert_equal(g(x), f(x))

    given(functions[Int](integers()), integers(), memoized, fast())

    def monotone(f: Function[Int, Int]) raises:
        if f(1) > f(2):
            fail("not monotone")

    var msg = String()
    try:
        given(functions[Int](integers(0, 9)), monotone, fast())
    except e:
        msg = String(e)
    assert_true("given({1->1, 2->0})" in msg, msg)

    var f = example(functions[Int](integers()))
    var after = String()
    try:
        _ = f(5)
    except e:
        after = String(e)
    assert_true("after its test case ended" in after, after)


# ---- from RapidCheck


@fieldwise_init
struct Person(Copyable, Writable):
    var name: String
    var age: Int
    var tags: List[Int]


def test_build_with_field_overrides() raises:
    def adult(p: Person) raises:
        assert_true(p.age >= 18 and p.age <= 99, String(p.age))
        assert_equal(p.name, "bob")

    given(
        build[Person](
            field["age"](integers(18, 99)), field["name"](just(String("bob")))
        ),
        adult,
        fast(),
    )

    # unnamed fields come from from_type, and every field shrinks
    def many_tags(p: Person) -> Bool:
        return len(p.tags) >= 2 and p.age > 50

    var found = find(build[Person](field["age"](integers(18, 99))), many_tags)
    assert_equal(found.age, 51)
    assert_equal(found.tags, [0, 0])
    assert_equal(found.name, "")


def _point(x: Int, y: Int) -> Tuple[Int, Int]:
    return (x, y)


def _sum3(a: Int, b: Int, c: Int) -> Int:
    return a + b + c


def test_apply() raises:
    def ordered(p: Tuple[Int, Int]) raises:
        assert_true(p[0] < 10 and p[1] >= 10)

    given(apply(integers(0, 9), integers(10, 20), _point), ordered, fast())

    def big(s: Int) -> Bool:
        return s >= 10

    assert_equal(
        find(apply(integers(0, 9), integers(0, 9), integers(0, 9), _sum3), big),
        10,
    )


def test_weighted_sampled_from() raises:
    var counts: List[Int] = [0, 0, 0]

    def tally(c: Int, x: Int) raises {mut counts}:
        counts[c] += 1

    # the integer keeps the search space from running out
    given(
        sampled_from([0, 1, 2], weights=[1, 1, 18]),
        integers(),
        tally,
        Settings(database=None, max_examples=400),
    )
    var total = counts[0] + counts[1] + counts[2]
    assert_true(counts[2] * 10 > total * 7, String(counts))

    def is_one(x: Int) -> Bool:
        return x == 1

    # still shrinks towards the first element
    assert_equal(find(sampled_from([5, 1, 7], weights=[1, 1, 18]), is_one), 1)

    var msg = String()
    try:
        _ = sampled_from([1, 2], weights=[1])
    except e:
        msg = String(e)
    assert_true("sampled_from() got 1 weights for 2 elements" in msg, msg)


def test_before_minimal_test_case_is_callable() raises:
    # a breakpoint target; calling it has no effect
    before_minimal_test_case("here")


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
