# Adapting strategies

The built-in strategies rarely produce exactly the values a test needs.
This page shows how to transform them: mapping, filtering, combining, and
choosing between them.

proptest's combinators are free functions that take the strategy as their
first argument: `map(s, f)` where Hypothesis writes `s.map(f)`. (Mojo
traits can't yet have default methods that are generic over closures of the
strategy's value type; see [Why the API looks the way it does](../explanation/mojo-api.md).)
The functions you pass can be top-level functions, nested functions, or
lambdas.

## Mapping strategy inputs

`map(s, f)` applies `f` to each value drawn from `s`:

```mojo
from proptest import map, integers, example

def main() raises:
    var evens = map(integers(0, 50), lambda (x: Int) -> Int: x * 2)
    print(example(evens))
```

The mapped value shrinks as the original does: `evens` shrinks towards
`0`, because `integers(0, 50)` does. Mapping is how you get values with a
structure the built-in strategies don't have, such as even numbers,
sorted lists, or a struct built from a few fields.

`apply(s1, ..., sN, f)` maps a function of several arguments over several
strategies (two to six). The function comes last, as in `given`:

```mojo
from proptest import apply, integers, example

@fieldwise_init
struct Point(Copyable, Writable):
    var x: Int
    var y: Int

def make_point(x: Int, y: Int) -> Point:
    return Point(x, y)

def main() raises:
    var points = apply(integers(0, 99), integers(0, 99), make_point)
    print(example(points))
```

## Filtering strategy inputs

`filter(s, pred)` keeps only the values for which `pred` holds:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
    var odd = filter(integers(), lambda (x: Int) -> Bool: x % 2 == 1)
~    assert_true(example(odd) % 2 != 0)
```

Filtering works by rejection: proptest draws a value, and if `pred` rejects
it, tries again, up to three times per test case before giving up on that
test case. It works well when the condition usually holds, and badly when
it rarely does. Prefer constructing the values you want: `map(integers(),
lambda (x: Int) -> Int: 2 * x + 1)` generates odd numbers without any
rejection, though it can overflow at the extremes of `Int`.

If a filter rejects most values, proptest fails the test with a health
check rather than silently running a test that checks almost nothing. A
`reason` names the condition in that report:

```mojo
from proptest import given, filter, integers, Settings

def main() raises:
    def prop(x: Int) raises:
        pass

    var rare = filter(
        integers(),
        lambda (x: Int) -> Bool: x % 1000 == 7,
        reason="ends in 007",
    )
    try:
        given(rare, prop, Settings(database=None))
    except e:
        print(e)
```

```text
FailedHealthCheck: It looks like this test is filtering out a lot of inputs. 0 inputs
were generated successfully, while 50 inputs were filtered out. Try to construct values
that satisfy the conditions directly instead of using filter() or assume(). Most
rejections were by: ends in 007 (50). (suppress with HealthCheck.filter_too_much)
```

### `filter_map`

When checking a value and converting it are the same work, `filter_map(s,
f)` does both: `f` returns an `Optional`, and `None` rejects the value.

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
def parse_digit(s: String) raises -> Optional[Int]:
    if s.byte_length() == 1 and s >= "0" and s <= "9":
        return Int(s)
    return None

~def main() raises:
    var digits = filter_map(text(max_size=1), parse_digit)
~    var d = example(digits)
~    assert_true(d >= 0 and d <= 9)
```

## Assuming away test cases

`assume(condition)` is a filter inside the test. It discards the current
test case when the condition is false:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
def prop(a: Int, b: Int) raises:
    assume(b != 0)
    assert_equal((a // b) * b + a % b, a)
~
~def main() raises:
~    given(integers(), integers(), prop, Settings(database=None))
```

### `assume` versus `filter`

They do the same job in different places:

- `filter` applies to one strategy, and retries just that draw, up to three
  times, before giving up on the test case. Use it when the condition is
  about one value.
- `assume` discards the whole test case. Use it when the condition involves
  several arguments, or values computed in the test.

Discarded test cases don't count towards `max_examples`, and both count
towards the `filter_too_much` health check.

### `assume` versus returning early

You could also `return` from the test when an input doesn't apply. Don't:
proptest then counts the input as a passing test case, so a test that
returns early for almost every input passes while testing almost nothing.
`assume` tells proptest the input didn't count, so it generates others,
and the health check fires if it can't find enough.

## Choosing between strategies

`one_of` draws from one of two to six strategies, which must produce the
same type:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
    var small_or_huge = one_of(integers(-10, 10), integers(1_000_000, 2_000_000))
~    var x = example(small_or_huge)
~    assert_true(x <= 10 or x >= 1_000_000)
```

It shrinks towards the first strategy. `weights=[...]` biases the choice
without changing how values shrink:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
    var mostly_small = one_of(
        integers(-10, 10), integers(1_000_000, 2_000_000), weights=[9, 1]
    )
~    var x = example(mostly_small)
~    assert_true(x <= 10 or x >= 1_000_000)
```

For more than six strategies, or a number only known at run time, pass a
`List` of `BoxedStrategy` values, made with `boxed(s)`:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
    var choices: List[BoxedStrategy[Int]] = [
        boxed(just(0)), boxed(integers(1, 9)), boxed(integers(100, 999))
    ]
    var s = one_of(choices^)
~    assert_true(example(s) <= 999)
```

`sampled_from([a, b, c])` chooses among fixed values rather than
strategies.

## Optional values

`optionals(s)` generates `None` or a value from `s`, shrinking towards
`None`. It's Hypothesis's `none() | s`.
