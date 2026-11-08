# Custom strategies

Sometimes the built-in strategies and combinators aren't enough, or a
strategy gets complicated enough to deserve a name. This page shows the
ways to define your own.

## Writing helper functions

The simplest custom strategy is a function that returns one:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
def small_lists() raises -> Lists[Integers]:
    return lists(integers(-10, 10), max_size=5)
~
~def main() raises:
~    assert_true(len(example(small_lists())) <= 5)
```

The return type is the strategy's struct type. Every strategy function has
one (`integers` returns `Integers`, `lists` returns `Lists[S]`, `map`
returns `Mapped[S, R, F]`), and the reference lists them. When the type is
awkward to spell, as it is for a strategy built from a closure, you can
erase it: `boxed(s)` returns a `BoxedStrategy[T]`, whose type mentions only
the value type.

## Writing your own strategy with `composite`

`composite(f)` turns a function that draws values into a strategy. The
function receives a `ConjectureData` and draws from other strategies with
`data.draw(...)`:

```mojo
from proptest import composite, lists, integers, example, ConjectureData

def list_and_index(mut data: ConjectureData) raises -> Tuple[List[Int], Int]:
    var xs = data.draw(lists(integers(), min_size=1))
    var i = data.draw(integers(0, len(xs) - 1))
    return (xs^, i)

def main() raises:
    var s = composite(list_and_index)
    var pair = example(s)
    print(len(pair[0]), pair[1])
```

This is Hypothesis's `@composite`. The values drawn inside `f` are shrunk
together, so a failing `(xs, i)` shrinks to a short list and a small index
that still fail.

## Dependent generation

`list_and_index` is an example of *dependent generation*: the index's range
depends on the list. There are three ways to do it.

- **`composite`**, as above. The most flexible.
- **`flatmap(s, f)`**: draw `x` from `s`, then a value from the strategy
  `f(x)`:

  ```mojo
  def lists_of_length(n: Int) raises -> Lists[Integers]:
      return lists(integers(), min_size=n, max_size=n)

  var square_lists = flatmap(integers(0, 5), lists_of_length)
  ```

- **`given_data`**, in the test itself; see below.

## Mixing data generation and test code

`given_data(test)` passes the test the `ConjectureData`, so it can draw
values in the middle of running (Hypothesis's `st.data()`):

```mojo
from std.testing import assert_true
from proptest import given_data, lists, integers, ConjectureData

def main() raises:
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(), min_size=1), "xs")
        var i = data.draw(integers(0, len(xs) - 1), "i")
        xs.append(xs[i])
        assert_true(xs[i] == xs[len(xs) - 1])

    given_data(prop)
    print("passed")
```

The label (`"xs"`, `"i"`) names the value in a failure report, which lists
each draw. If the test instead failed whenever `xs[i] > 5`, the report
would be:

```text
Falsifying example (test.mojo:10:15):
    Draw 1 (xs): [6]
    Draw 2 (i): 0  # or any other generated value
too big
```

The comment comes from the *explain* phase: after shrinking, proptest
checks which draws can vary without changing the failure. Use
`given_data` when what to draw depends on what the code under test did.
Otherwise, prefer `given` or `composite`, which keep generation separate
from the test.

## Writing a strategy struct

A strategy is any struct that conforms to the `Strategy` trait. It names
the type it produces, `Value`, and implements `do_draw`:

```mojo
from proptest import Strategy, ConjectureData, integers, example

@fieldwise_init
struct Point(Copyable, Writable):
    var x: Int
    var y: Int

struct Points(Copyable, Strategy):
    comptime Value = Point
    var limit: Int

    def __init__(out self, limit: Int):
        self.limit = limit

    def do_draw(self, mut data: ConjectureData) raises -> Point:
        var x = data.draw(integers(0, self.limit))
        var y = data.draw(integers(0, self.limit))
        return Point(x, y)

def main() raises:
    print(example(Points(10)))
```

Inside `do_draw`, draw from other strategies with `data.draw(...)`, not by
calling their `do_draw` directly: `data.draw` records the structure of the
draw, which the shrinker uses. A strategy can also make primitive choices
with `data.draw_integer`, `data.draw_boolean` and the like; see
[Writing strategies: the low-level API](../reference/internals.md).

A struct is worth writing when the strategy has parameters you want to
name, or when you want a strategy type that doesn't mention closures.
Otherwise `composite` is shorter.

### Values must be printable

A strategy's `Value` must be `Movable` and `Writable`, so that proptest
can print failing examples. It doesn't have to be `Copyable`: proptest
rebuilds values from their choices rather than copying them, so move-only
types such as unique handles work too. A few strategies that hand out the
same value more than once (`just`, `sampled_from`, `permutations`,
`shared`, set elements and dictionary keys) need `Copyable` values;
`lazy_just(f)` makes a fresh value per test case instead.

## Recursive data

`recursive(base, extend)` generates recursive structures such as trees or
JSON-like values. `base` generates the leaves; `extend` receives a
strategy for the whole recursive type and returns a strategy for one more
level:

```mojo
from proptest import recursive, lists, integers, boxed, map, example, BoxedStrategy

def leaf(x: Int) -> List[Int]:
    return [x]

def flatten(xss: List[List[Int]]) -> List[Int]:
    var out = List[Int]()
    for xs in xss:
        out.extend(xs.copy())
    return out^

def extend(inner: BoxedStrategy[List[Int]]) raises -> BoxedStrategy[List[Int]]:
    return boxed(map(lists(inner.copy(), max_size=3), flatten))

def main() raises:
    var s = recursive(map(integers(0, 9), leaf), extend, max_leaves=10)
    print(example(s))
```

Mojo structs can't contain themselves directly, so recursive values are
usually stored with indices into a list, or behind `ArcPointer`.
