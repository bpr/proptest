# Introduction to proptest

This page introduces proptest and property-based testing: how to install
proptest, write a test, and read its reports.

## Installing proptest

proptest needs Mojo 1.3 or later; until Mojo 1.3.0 is released, that means
the nightly channel. The repository uses [pixi](https://pixi.sh):

```sh
git clone https://github.com/bpr/proptest
cd proptest
pixi install
pixi run test        # proptest's own test suite
pixi run package     # writes build/proptest.mojoc
```

To use proptest from your project, either put the repository on the
include path (`mojo run -I path/to/proptest ...`) or put the directory
containing `proptest.mojoc` there. proptest will be published on the
modular-community channel once Mojo 1.3.0 is released; then
`pixi add proptest` will be enough.

## Defining a simple test

A property-based test has two parts: a *test function* that checks a
property for one input, and *strategies* that describe which inputs to try.
`given` connects them:

```mojo
from std.testing import assert_equal
from proptest import given, integers

def main() raises:
    def addition_commutes(a: Int, b: Int) raises:
        assert_equal(a + b, b + a)

    given(integers(), integers(), addition_commutes)
    print("passed")
```

`integers()` is a strategy for `Int` values. `given` draws a value for each
strategy, calls the test, and repeats, 100 times by default. If the test
raises for some input, `given` shrinks that input and raises an error
describing it. If it never does, `given` returns.

The test is an ordinary nested function. Its parameters must have the types
the strategies produce, in order; the compiler checks this.

## Testing a sorting algorithm

Suppose we want to test a sorting function. Rather than write out a few
lists and their sorted forms, we state what's true of *every* sorted list:
it's in order, and it has the same elements as the input.

```mojo
from std.testing import assert_true, assert_equal
from proptest import given, lists, integers

def my_sort[T: Comparable & Copyable](xs: List[T]) -> List[T]:
    var ys = xs.copy()
    sort(ys)
    return ys^

def main() raises:
    def sorts(xs: List[Int]) raises:
        var ys = my_sort(xs)
        assert_equal(len(ys), len(xs))
        for i in range(1, len(ys)):
            assert_true(ys[i - 1] <= ys[i])
        for x in xs:
            assert_true(x in ys)

    given(lists(integers()), sorts)
    print("passed")
```

`lists(integers())` generates lists of integers. Strategies combine like
this: `lists` takes a strategy for its elements, and
[many others](builtin-strategies.md) take strategies too.

## Adding floats to our test

Does it work for floats? Change the element strategy:

```mojo
from std.testing import assert_true
from proptest import given, lists, floats, Settings

def my_sort[T: Comparable & Copyable](xs: List[T]) -> List[T]:
    var ys = xs.copy()
    sort(ys)
    return ys^

def main():
    def ordered(xs: List[Float64]) raises:
        var ys = my_sort(xs)
        for i in range(1, len(ys)):
            assert_true(ys[i - 1] <= ys[i], String(ys[i - 1], " > ", ys[i]))

    try:
        given(lists(floats()), ordered, Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (sorting.mojo:16:14):
    given([0.0, nan])
At sorting.mojo:13:24: AssertionError: 0.0 > nan
```

proptest found that `NaN` isn't ordered with respect to anything, so no
list containing it can be in order. It shrank whatever list it first found
to the simplest one with this problem.

### Preventing `floats()` from generating `NaN`

Whether this is a bug depends on what `my_sort` promises. If it isn't meant
to handle `NaN`, say so in the strategy:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    def ordered(xs: List[Float64]) raises:
~        var ys = xs.copy()
~        sort(ys)
~        for i in range(1, len(ys)):
~            assert_true(ys[i - 1] <= ys[i])
~
    given(lists(floats(allow_nan=False)), ordered)
```

This is typical of property-based testing: a failure makes you decide
precisely what your code should do.

## Tests with multiple arguments

`given` takes up to six strategies. When a test with several arguments
fails, all of them are shrunk:

```text
Falsifying example (two.mojo:24:14):
    given([0, 0], '00')
both
```

Each value is printed as its type writes itself (`Writable`), with strings
quoted.

## Letting the types choose: `check`

When the plain types of the test's parameters say enough, `check` infers
the strategies from them:

```mojo
from proptest import check

def main() raises:
    def reverse_twice(xs: List[Int]) -> Bool:
        var ys = xs.copy()
        ys.reverse()
        ys.reverse()
        return ys == xs

    check(reverse_twice)
    print("passed")
```

A property passed to `check` can raise, like a `given` test, or return
`Bool`. [Strategies from types](types.md) covers `check`, and how to put
constraints such as "non-empty" or "positive" in the parameter types.

## Running proptest tests

A test that calls `given` or `check` raises when the property fails, so it
works with any way of running Mojo tests. With `std.testing.TestSuite`:

```mojo
from std.testing import TestSuite, assert_equal
from proptest import given, integers

def test_addition_commutes() raises:
    def prop(a: Int, b: Int) raises:
        assert_equal(a + b, b + a)
    given(integers(), integers(), prop)

def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
```

A failing example is saved in the *example database*, a directory named
`.proptest/examples` under the working directory, and is tried first the
next time the test runs. See [Replaying failures](replaying-failures.md).

## When to use property-based testing

Property-based testing is useful when you can say what should be true of a
result without computing the result by hand. Common kinds of property:

- **Round trips:** `decode(encode(x)) == x`; parsing what you printed.
- **Invariants:** a sorted list is ordered; a balanced tree stays
  balanced; a count is never negative.
- **Equivalence with a model:** a fast implementation agrees with a slow,
  obviously correct one, or with the same operation on a simpler data
  structure.
- **Algebraic laws:** an operation is commutative, associative, or
  idempotent.
- **No crashes:** the code doesn't raise, or raises only documented errors,
  for any valid input.

It complements example-based tests rather than replacing them. A handful of
examples documents behavior you care about; properties find the inputs you
didn't think of.
