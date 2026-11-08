# Built-in strategies

A *strategy* describes the values a test should be given. proptest has
strategies for numbers, text, and collections, and combinators that build
strategies out of other strategies.

Strategies are values: `integers(0, 10)` returns a strategy, which you can
store in a variable and pass to several tests. Strategy constructors that
check their arguments raise on invalid ones (for example
`integers(10, 0)`), so call them from a `raises` function.

## Exploring a strategy

`example(strategy)` returns one random value, which is handy for seeing
what a strategy produces:

```mojo
from proptest import example, lists, integers, text

def main() raises:
    for _ in range(3):
        print(example(lists(integers(0, 9), max_size=5)))
    print(example(text("abc", min_size=2, max_size=4)))
```

Use `example` for exploring, not in tests: a test should let `given` draw
its values, so that failures can be shrunk and replayed.

`find(strategy, condition)` searches for a value satisfying a condition and
returns the simplest one it finds:

```mojo
from proptest import find, lists, integers

def main() raises:
    def sums_over_100(xs: List[Int]) -> Bool:
        var total = 0
        for x in xs:
            total += x
        return total > 100

    print(find(lists(integers(0, 50)), sums_over_100))   # [1, 50, 50]
```

## Numbers

| Strategy | Values |
|---|---|
| `integers(min_value, max_value)` | `Int`; either bound can be omitted |
| `integers_of[DType.uint8](min_value, max_value)` | `Scalar[dtype]`, for any integer `DType` |
| `floats(min_value, max_value, allow_nan=, allow_infinity=, allow_subnormal=, exclude_min=, exclude_max=)` | `Float64` |
| `floats32(...)` | `Float32` |
| `booleans()` | `Bool` |

Integers shrink towards zero, or towards the bound nearest zero. Floats
shrink towards simple values: small integers first, then simple fractions.
`floats()` generates `NaN` and the infinities unless bounds or the `allow_`
arguments exclude them.

## Text

| Strategy | Values |
|---|---|
| `text(alphabet, min_size=, max_size=)` | `String`; by default any codepoint except surrogates |
| `characters(categories=, exclude_categories=, min_codepoint=, max_codepoint=, include_characters=, exclude_characters=, codec=)` | one-character `String` |
| `from_regex(pattern, fullmatch=)` | `String` matching a regular expression |
| `binary(min_size=, max_size=)` | `List[UInt8]` |

`alphabet` can be a `String` of allowed characters or a `characters(...)`
strategy:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    var hex = (
text("0123456789abcdef", min_size=1)          # hex digits
~    )
~    var upper = (
text(characters(categories=["Lu", "Nd"]))     # uppercase letters and digits
~    )
~    var email = (
from_regex("[a-z]+@[a-z]+\\.com", fullmatch=True)
~    )
~    print(example(hex), example(upper), example(email))
```

Categories are Unicode general categories (`"Lu"`, `"Nd"`, or a whole class
like `"L"`), from Unicode 17.0. Without `fullmatch=True`, `from_regex`
generates strings that *contain* a match, as Hypothesis does.

## Collections

| Strategy | Values |
|---|---|
| `lists(elements, min_size=, max_size=)` | `List[T]` |
| `unique_lists(elements, ...)` | `List[T]` with distinct elements |
| `unique_lists_by(elements, key, ...)` | `List[T]` with distinct `key(x)` |
| `sets(elements, ...)` | `Set[T]` |
| `dictionaries(keys, values, ...)` | `Dict[K, V]` |
| `tuples(s1, s2, ...)` | `Tuple[...]` of two to six elements |
| `optionals(s)` | `Optional[T]`, shrinking towards `None` |

Collections shrink by deleting elements, then by shrinking the elements
that remain.

## Choosing among values

| Strategy | Values |
|---|---|
| `just(x)` | always `x` |
| `lazy_just(f)` | `f()`, called afresh for each test case |
| `sampled_from([a, b, c], weights=)` | one of the elements |
| `one_of(s1, ..., s6, weights=)` | a value from one of the strategies |
| `permutations(xs)` | a reordering of `xs` |
| `subsequence(xs, min_size=, max_size=)` | a sublist of `xs`, in order |

`sampled_from` and `one_of` shrink towards their first option. The
optional `weights` are positive integers that bias generation (`weights=[1,
1, 8]` picks the third option 80% of the time); they don't change how
values shrink.

## Combinators

These build a strategy from other strategies; the next two pages cover
them.

| Combinator | Values |
|---|---|
| `map(s, f)` | `f(x)` for `x` from `s` |
| `apply(s1, ..., sN, f)` | `f(a1, ..., aN)` |
| `filter(s, pred)` | `x` from `s` with `pred(x)` |
| `filter_map(s, f)` | `f(x)` where it isn't `None` |
| `flatmap(s, f)` | a value from the strategy `f(x)` |
| `composite(f)` | whatever `f(data)` draws and returns |
| `recursive(base, extend)` | recursive data, such as trees |
| `shared(s, key=)` | one value per test case, shared by every draw |
| `boxed(s)` | the same values, as a `BoxedStrategy[T]` |

## Types

`from_type[T]()` chooses a strategy from a type: scalars, `String`,
`List`, `Optional`, `Set`, `Dict`, tuples, and your own structs. See
[Strategies from types](types.md).

## Everything else

The [strategies reference](../reference/strategies.md) lists every
strategy and its arguments. NuMojo arrays have their own package; see
[Generate NuMojo arrays](../how-to/numojo.md).
