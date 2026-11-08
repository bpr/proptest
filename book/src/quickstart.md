# Quickstart

This is a short guide to the basics of proptest. The
[tutorial](tutorial/introduction.md) covers the same ground in more depth.

## Install proptest

proptest needs Mojo 1.3 or later. Clone the repository and put it on your
include path:

```sh
git clone https://github.com/bpr/proptest
mojo run -I path/to/proptest my_tests.mojo
```

Or build a package once with `pixi run package` (in the proptest
repository), and put `build/proptest.mojoc` on the include path.

## Write your first test

Here is a run-length encoder with a bug:

```mojo
from std.testing import assert_equal
from proptest import given, text, Settings

def encode(s: String) -> List[Tuple[String, Int]]:
    var out = List[Tuple[String, Int]]()
    var prev = String()
    var count = 0
    for cp in s.codepoints():
        var c = String(cp)
        if c != prev and count > 0:
            out.append((prev, count))
            count = 0
        prev = c
        count += 1
    # BUG: the last run is never appended
    return out^

def decode(runs: List[Tuple[String, Int]]) -> String:
    var s = String()
    for r in runs:
        for _ in range(r[1]):
            s += r[0]
    return s^

def main():
    def decode_inverts_encode(s: String) raises:
        assert_equal(decode(encode(s)), s)

    try:
        given(text(), decode_inverts_encode, Settings(database=None))
    except e:
        print(e)
```

`given(text(), decode_inverts_encode)` runs the test on 100 strings drawn
from the `text()` strategy. The test fails, and proptest reports the
simplest string it fails for:

```text
Falsifying example (quickstart.mojo:41:14):
    given('0')
At quickstart.mojo:38:21: AssertionError: `left == right` comparison failed:
   left:
  right: 0
```

proptest found some long, complicated string that broke the test, then
*shrank* it to `'0'`. The one-character string is easier to debug: the
final run is missing.

## Running in a test suite

A `given` call raises an `Error` when its test fails, so a property test is
an ordinary Mojo test function. With `std.testing.TestSuite`:

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

The property is a nested function. It can capture values from the
enclosing function with a capture list: `def prop(x: Int) raises {var limit}:`.

## Arguments to `given`

`given` takes one to six strategies, then the test, then optional
`Settings`. The test's parameters must have the types the strategies
produce:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    def prop(xs: List[Int], s: String, b: Bool) raises:
~        pass
~
    given(lists(integers()), text(), booleans(), prop)  # prop(xs: List[Int], s: String, b: Bool)
```

To let proptest choose the strategies from the parameter types instead, use
`check`:

```mojo
from proptest import check

def test_reverse_twice() raises:
    def prop(xs: List[Int]) -> Bool:
        var ys = xs.copy()
        ys.reverse()
        ys.reverse()
        return ys == xs
    check(prop)
~
~def main() raises:
~    test_reverse_twice()
```

## Filtering inside a test

Sometimes a test only makes sense for some inputs. `assume(condition)`
discards the current input if the condition is false:

```mojo
~from std.testing import assert_equal
from proptest import given, integers, assume

def test_division() raises:
    def prop(a: Int, b: Int) raises:
        assume(b != 0)
        assert_equal((a // b) * b + a % b, a)
    given(integers(), integers(), prop)
~
~def main() raises:
~    test_division()
```

Discarded inputs don't count towards the 100 examples. If you discard too
many, proptest fails the test with a health check, because it isn't really
testing anything. It's better to generate only valid inputs: here,
`filter(integers(), lambda (b: Int) -> Bool: b != 0)`, or the constraint
type `NonZero[Int]`.

## Dependent generation

When one input depends on another, draw them inside the test. `given_data`
passes the test a `ConjectureData`, from which it can draw as it goes:

```mojo
~from std.testing import assert_true
from proptest import given_data, lists, integers, ConjectureData

def test_index() raises:
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(), min_size=1), "xs")
        var i = data.draw(integers(0, len(xs) - 1), "i")
        assert_true(xs[i] in xs)
    given_data(prop)
~
~def main() raises:
~    test_index()
```

The second argument to `draw` is a label, printed with the value in a
failure report.

## Where to go next

- [Built-in strategies](tutorial/builtin-strategies.md) lists what proptest
  can generate.
- [Configuring test settings](tutorial/settings.md) covers the number of
  examples, seeds, and the other settings.
- [Stateful testing](tutorial/stateful.md) tests whole sequences of
  operations.
