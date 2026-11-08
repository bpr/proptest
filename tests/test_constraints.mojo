# Constraint types (Bounded, Positive, NonEmpty, Sorted, Blind, Via, ...):
# their values satisfy the constraint, keep it while shrinking, and compose
# with check, from_type and reflected struct fields. proptest-specific (from
# QuickCheck's modifiers); Hypothesis has no equivalent.

from std.testing import TestSuite, assert_equal, assert_true
from std.collections import Set, Dict

from proptest import *


def fast() -> Settings:
    return Settings(database=None, max_examples=200)


def test_bounded() raises:
    def prop(
        a: Bounded[-3, 7],
        b: Bounded[10, 20, UInt8],
        c: Bounded[-1, 1, Float64],
        d: Bounded[0, 5, Float32],
        e: Bounded[4, 4, Int64],
    ) -> Bool:
        return (
            a.value >= -3
            and a.value <= 7
            and b.value >= 10
            and b.value <= 20
            and c.value >= -1.0
            and c.value <= 1.0
            and d.value >= 0
            and d.value <= 5
            and e.value == 4
        )

    check(prop, fast())

    def big(x: Bounded[-50, 50]) -> Bool:
        return x.value > 10

    assert_equal(find(from_type[Bounded[-50, 50]](), big).value, 11)


def test_signs() raises:
    def prop(
        a: Positive[Int],
        b: Positive[Float64],
        c: Positive[Float32],
        d: Positive[UInt16],
        e: NonNegative[Int8],
        f: NonNegative[Float64],
    ) -> Bool:
        return (
            a.value > 0
            and b.value > 0
            and c.value > 0
            and d.value > 0
            and e.value >= 0
            and f.value >= 0
        )

    check(prop, fast())

    def nonzero(
        a: NonZero[Int], b: NonZero[Float64], c: NonZero[Float32]
    ) -> Bool:
        return a.value != 0 and b.value != 0 and c.value != 0

    check(nonzero, fast())


def test_numeric_constraints_shrink_to_the_boundary() raises:
    def anything_int(x: Positive[Int]) -> Bool:
        return True

    assert_equal(find(from_type[Positive[Int]](), anything_int).value, 1)

    def anything_nonzero(x: NonZero[Int]) -> Bool:
        return True

    assert_equal(find(from_type[NonZero[Int]](), anything_nonzero).value, 1)

    def negative(x: NonZero[Int]) -> Bool:
        return x.value < 0

    assert_equal(find(from_type[NonZero[Int]](), negative).value, -1)

    def anything_nonneg(x: NonNegative[Float64]) -> Bool:
        return True

    assert_equal(
        find(from_type[NonNegative[Float64]](), anything_nonneg).value, 0.0
    )


def test_non_empty() raises:
    def prop(
        a: NonEmpty[List[Int]],
        b: NonEmpty[String],
        c: NonEmpty[Set[Int]],
        d: NonEmpty[Dict[Int, Bool]],
    ) -> Bool:
        return (
            len(a.value) > 0
            and b.value.byte_length() > 0
            and len(c.value) > 0
            and len(d.value) > 0
        )

    check(prop, fast())

    def anything(xs: NonEmpty[List[UInt8]]) -> Bool:
        return True

    var m = find(from_type[NonEmpty[List[UInt8]]](), anything)
    assert_equal(len(m.value), 1)
    assert_equal(m.value[0], 0)


def test_sorted() raises:
    def prop(xs: Sorted[List[Int]], ys: Sorted[List[String]]) -> Bool:
        for i in range(1, len(xs.value)):
            if xs.value[i - 1] > xs.value[i]:
                return False
        for i in range(1, len(ys.value)):
            if ys.value[i - 1] > ys.value[i]:
                return False
        return True

    check(prop, fast())

    def has_negative(xs: Sorted[List[Int]]) -> Bool:
        return len(xs.value) >= 3 and xs.value[0] < 0

    var m = find(from_type[Sorted[List[Int]]](), has_negative)
    assert_equal(m.value, [-1, 0, 0])


def test_blind_hides_the_value_in_reports() raises:
    def prop(x: Blind[List[Int]], y: Int) raises:
        if y > 5:
            fail("too big")

    var msg = String()
    try:
        check(prop, fast())
    except e:
        msg = String(e)
    assert_true("<hidden>" in msg, msg)
    assert_true("6," in msg, msg)


def digits(mut data: ConjectureData) raises -> List[Int]:
    return data.draw(lists(integers(0, 9), max_size=4))


def test_via() raises:
    def prop(xs: Via[digits]) -> Bool:
        if len(xs.value) > 4:
            return False
        for x in xs.value:
            if x < 0 or x > 9:
                return False
        return True

    check(prop, fast())

    def long(xs: Via[digits]) -> Bool:
        return len(xs.value) >= 3

    assert_equal(find(from_type[Via[digits]](), long).value, [0, 0, 0])


@fieldwise_init
struct Account(Copyable, Writable):
    var id: Positive[UInt32]
    var owner: NonEmpty[String]
    var history: Sorted[List[Int]]


def test_constraints_compose_with_from_type() raises:
    def prop(a: Account, xs: List[NonZero[Int8]]) -> Bool:
        for x in xs:
            if x.value == 0:
                return False
        return a.id.value > 0 and a.owner.value.byte_length() > 0

    check(prop, fast())

    def report(a: Account) raises:
        if len(a.history.value) >= 2:
            fail("long history")

    var msg = String()
    try:
        check(report, fast())
    except e:
        msg = String(e)
    # wrappers print their values (strings quoted), not the wrapper
    assert_true("given(Account(id=1, owner='0', history=[0, 0]))" in msg, msg)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
