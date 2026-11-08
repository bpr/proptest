# Strategies from types

Often the type of a value says most of what a test needs: a `List[Int]`,
a `String`, a struct of a few fields. proptest can derive a strategy from a
type at compile time, and run a property whose inputs are drawn from its
parameter types. This page covers `from_type`, `Arbitrary`, `check`, the
constraint types, and `build`.

## `from_type`

`from_type[T]()` is a strategy for values of type `T`:

```mojo
from proptest import from_type, example

def main() raises:
    print(example(from_type[List[Tuple[Bool, Optional[Int8]]]]()))
```

It supports:

- integer scalars (`Int`, `UInt8`, ..., `Int128`), `Float64`, `Float32`,
  `Bool`, and `String`;
- `List`, `Optional`, `Set`, `Dict`, and tuples of up to six elements,
  nested to any depth;
- any type that implements `Arbitrary` (below), including the constraint
  types;
- any other struct, built field by field, recursively.

The strategy is chosen at compile time, so an unsupported type is a
compile error, not a run-time one.

### Structs, field by field

A struct without an `Arbitrary` implementation is built by drawing each
field with `from_type`, using Mojo's reflection:

```mojo
from proptest import from_type, example

@fieldwise_init
struct Point(Copyable, Writable):
    var x: UInt16
    var y: UInt16

@fieldwise_init
struct Sprite(Copyable, Writable):
    var position: Point
    var tags: List[String]
    var layer: Optional[Int8]

def main() raises:
    print(example(from_type[Sprite]()))
```

Each field is drawn in its own span, so failing structs shrink field by
field. This bypasses the struct's `__init__`: Mojo can reflect on a
struct's fields but not on its initializers. So a struct with invariants
between its fields (`lo <= hi`, say) should implement `Arbitrary` instead.

## `Arbitrary`: a type's own strategy

A type that implements `Arbitrary` provides its own way to be drawn, with a
static `arbitrary` method. `from_type` (and therefore `check`, and struct
fields of this type) uses it:

```mojo
from proptest import Arbitrary, ConjectureData, integers, from_type, example

@fieldwise_init
struct Interval(Arbitrary, Copyable, Writable):
    var lo: Int
    var hi: Int

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        var lo = data.draw(integers(-100, 100))
        return Self(lo, data.draw(integers(lo, 100)))

def main() raises:
    print(example(from_type[Interval]()))
```

This is Hypothesis's `register_type_strategy`, attached to the type
instead of registered at run time. For a type you don't own, see
[Generate values of your own types](../how-to/type-strategies.md).

## `check`: properties over types

`check(prop)` draws each argument of `prop` with `from_type`, so the
parameter types are the whole specification (Rust quickcheck's
`quickcheck(prop)`):

```mojo
from proptest import check

def main() raises:
    def concat_length(a: List[Int], b: List[Int]) -> Bool:
        var c = a.copy()
        c.extend(b.copy())
        return len(c) == len(a) + len(b)

    check(concat_length)
    print("passed")
```

The property takes one to six arguments and can:

- raise on failure, like a `given` test;
- return `Bool`, where `False` is a failure;
- return an `Outcome`: `Outcome.passed()`, `Outcome.discard()` (like
  `assume(False)`), `Outcome.fail("why")`, or `Outcome.of(condition, "why")`.

```mojo
from proptest import check, Outcome

def main() raises:
    def division(a: Int8, b: Int8) -> Outcome:
        if b == 0:
            return Outcome.discard()
        var q = Int(a) // Int(b)
        return Outcome.of(q * Int(b) + Int(a) % Int(b) == Int(a), "a == q*b + r")

    check(division)
    print("passed")
```

Failures are reported like `given`'s; a `Bool` property that returns
`False` reports `check: the property returned False`.

## Constraint types

The plain types often say too little: a test might need a non-empty list,
or a positive number. Constraint types put the constraint in the type
(Haskell QuickCheck's *modifiers*). Each implements `Arbitrary`, so it
works with `check`, `from_type`, and struct fields; the underlying value is
`.value`; and shrinking never breaks the constraint, because the value is
always drawn through the constrained strategy.

```mojo
from proptest import check, NonEmpty, NonNegative

def main() raises:
    def index_is_in_range(xs: NonEmpty[List[Int]], i: NonNegative[Int]) -> Bool:
        var k = i.value % len(xs.value)
        return xs.value[k] in xs.value

    check(index_is_in_range)
    print("passed")
```

| Type | Values |
|---|---|
| `Bounded[lo, hi]`, `Bounded[lo, hi, UInt8]` | `lo <= value <= hi` (the type defaults to `Int`) |
| `Positive[T]`, `NonNegative[T]`, `NonZero[T]` | integer scalars, `Float64`, `Float32` (floats are finite) |
| `NonEmpty[T]` | a `List`, `String`, `Set`, or `Dict` with at least one element |
| `Sorted[List[T]]` | an ascending list |
| `Blind[T]` | any `T`, printed as `<hidden>` in reports |
| `Via[f]` | whatever `f(data)` draws |

Reports print the value without the wrapper. Constraints in types catch
real bugs:

```mojo
from proptest import check, NonZero

def main():
    def abs_is_positive(x: NonZero[Int8]) -> Bool:
        return abs(x.value) > 0

    try:
        check(abs_is_positive)
    except e:
        print(e)
```

```text
Falsifying example (abs.mojo:8:14):
    given(-128)
check: the property returned False
```

### `Via`: any strategy as a type

`Via[f]` names a draw function in a type, so any strategy can be a
parameter type:

```mojo
from proptest import check, Via, Positive, ConjectureData, lists, integers

def digits(mut data: ConjectureData) raises -> List[Int]:
    return data.draw(lists(integers(0, 9), max_size=4))

def main() raises:
    def prop(xs: Via[digits], n: Positive[UInt8]) -> Bool:
        for x in xs.value:
            if x < 0 or x > 9:
                return False
        return n.value > 0

    check(prop)
    print("passed")
```

When strategies depend on each other or on values only known at run time,
use `given` with explicit strategies instead.

## `build`: from_type with some fields given

`build[T](field["name"](strategy), ...)` builds a struct field by field,
like `from_type`, but draws the named fields from the given strategies
(RapidCheck's `gen::build`, Hypothesis's `builds(Cls, name=strategy)`):

```mojo
from proptest import build, field, integers, text, just, example

@fieldwise_init
struct Person(Copyable, Writable):
    var name: String
    var age: Int
    var tags: List[Int]

def main() raises:
    var adults = build[Person](
        field["age"](integers(18, 99)),
        field["name"](text(min_size=1, max_size=10)),
    )
    print(example(adults))
```

The other fields (`tags` here) come from `from_type`. The field names, and
the types of the strategies, are checked at compile time: a misspelled
field, a field given twice, or a strategy of the wrong type fails to
compile, with a message naming the field.
