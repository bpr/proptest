# Checking a hand-written sort against its specification: the output is
# ordered and is a permutation of the input. The insertion sort below drops
# duplicates of the first element, and proptest shrinks the failure to the
# minimal input [0, 0].
#
#   pixi run mojo run -I . examples/sorting.mojo

from std.testing import assert_equal, assert_true

from proptest import given, lists, integers, Settings


def my_sort(xs: List[Int]) -> List[Int]:
    var out = List[Int]()
    for x in xs:
        var i = 0
        while i < len(out) and out[i] < x:
            i += 1
        if i < len(out) and out[i] == x and i == 0:
            continue  # BUG: "deduplicates" the smallest element
        out.insert(i, x)
    return out^


def count(xs: List[Int], v: Int) -> Int:
    var n = 0
    for x in xs:
        if x == v:
            n += 1
    return n


def main():
    def sorted_permutation(xs: List[Int]) raises:
        var ys = my_sort(xs)
        for i in range(1, len(ys)):
            assert_true(ys[i - 1] <= ys[i], "output is not sorted")
        assert_equal(len(ys), len(xs), "output has the wrong length")
        for x in xs:
            assert_equal(count(xs, x), count(ys, x), "counts differ")

    try:
        given(lists(integers()), sorted_permutation, Settings(database=None))
    except e:
        print(e)
