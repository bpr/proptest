# Smoke test for the packaged proptest (run by conda.recipe/recipe.yaml):
# imports the installed proptest.mojoc, checks a passing property, and checks
# that a failing one is found and shrunk.

from std.testing import assert_equal, assert_true

from proptest import Settings, given, integers, lists


def main() raises:
    def reverse_twice(xs: List[Int]) raises:
        var r = List[Int](reversed(xs))
        assert_equal(List[Int](reversed(r)), xs)

    given(lists(integers()), reverse_twice, Settings(database=None))

    def small(x: Int) raises:
        assert_true(x < 1000)

    var failed = False
    try:
        given(integers(), small, Settings(database=None))
    except e:
        failed = True
        assert_true("1000" in String(e), String("not shrunk to 1000: ", e))
    assert_true(failed, "a failing property passed")
    print("proptest package OK")
