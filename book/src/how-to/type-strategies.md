# Generate values of your own types

There are several ways to generate values of a struct. Which to use
depends on whether the struct has invariants, whether you own it, and
whether one strategy fits every test.

## A struct without invariants: nothing to do

If any combination of field values is valid, `from_type[T]()` (and `check`)
already handles it, by drawing each field with `from_type`:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
@fieldwise_init
struct Color(Copyable, Writable):
    var r: UInt8
    var g: UInt8
    var b: UInt8

~def main() raises:
~    def prop(c: Color) -> Bool:
~        return Int(c.r) + Int(c.g) + Int(c.b) <= 765
~
    check(prop)   # prop(c: Color) -> Bool
```

## A struct with invariants: implement `Arbitrary`

Building from fields bypasses `__init__`, so it can produce values that the
constructor would reject. Give such a type its own strategy by implementing
`Arbitrary`:

```mojo
from proptest import Arbitrary, ConjectureData, integers, check

@fieldwise_init
struct Interval(Arbitrary, Copyable, Writable):
    var lo: Int
    var hi: Int

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        var lo = data.draw(integers(-100, 100))
        return Self(lo, data.draw(integers(lo, 100)))

def main() raises:
    def prop(i: Interval) -> Bool:
        return i.lo <= i.hi

    check(prop)
    print("passed")
```

Draw in an order that makes later choices depend on earlier ones (`hi` is
drawn after `lo`, from `lo` up), rather than drawing freely and filtering.
Values built this way shrink well: here, towards `lo == hi == 0`.

## Some fields need particular strategies: `build`

When the default for most fields is fine but a few need constraints, use
`build` and name the fields:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~@fieldwise_init
~struct Person(Copyable, Writable):
~    var name: String
~    var age: Int
~    var email: String
~
~def main() raises:
    var people = build[Person](
        field["age"](integers(0, 120)),
        field["email"](from_regex("[a-z]+@example\\.com", fullmatch=True)),
    )
~    print(example(people))
```

Field names and the strategies' types are checked at compile time.

## A type you don't own

You can't add `Arbitrary` to a type from another package. (Mojo's struct
extensions can't currently satisfy a trait method that returns `Self`
from another module.) Instead:

- **Wrap it.** A small struct implementing `Arbitrary`, holding the value,
  works with `check` and `from_type`, like proptest's own constraint types:

  ```mojo
  struct AnyCelsius(Arbitrary, Copyable, Writable):
      var value: Celsius

      def __init__(out self, var value: Celsius):
          self.value = value^

      @staticmethod
      def arbitrary(mut data: ConjectureData) raises -> Self:
          return Self(Celsius(data.draw(floats(-273.15, 1000.0))))

      def write_to(self, mut writer: Some[Writer]):
          writer.write(self.value)
  ```

- **Name a draw function in the type** with `Via[f]`:
  `def prop(c: Via[draw_celsius]) -> Bool`.
- **Use an explicit strategy** with `given`, built with `apply`,
  `composite`, or a strategy struct.

## Several strategies for one type

`Arbitrary` gives a type one canonical strategy. When different tests need
different kinds of value (small and large, valid and invalid), write
strategy functions, and pass them to `given`:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~@fieldwise_init
~struct Interval(Copyable, Writable):
~    var lo: Int
~    var hi: Int
~
def draw_small(mut data: ConjectureData) raises -> Interval:
    var lo = data.draw(integers(-10, 10))
    return Interval(lo, data.draw(integers(lo, 10)))

def draw_huge(mut data: ConjectureData) raises -> Interval:
    var lo = data.draw(integers())
    return Interval(lo, data.draw(integers(lo)))

def small_intervals() -> BoxedStrategy[Interval]:
    return boxed(composite(draw_small))

def huge_intervals() -> BoxedStrategy[Interval]:
    return boxed(composite(draw_huge))
~
~def main() raises:
~    def ordered(i: Interval) raises:
~        assert_true(i.lo <= i.hi)
~
~    given(small_intervals(), ordered, Settings(database=None))
~    given(huge_intervals(), ordered, Settings(database=None))
```

A function returning a strategy has to spell the strategy's type. For
strategies built with closures, that type is long; `boxed(...)` hides it
behind `BoxedStrategy[Interval]`, at the cost of an indirect call per
draw. A strategy struct (see [Custom strategies](../tutorial/custom-strategies.md#writing-a-strategy-struct))
gives a short, named type and can take parameters.

## Make the type printable

Every generated value must be `Writable`, so failures can show it. For a
`@fieldwise_init` struct whose fields are all `Writable`, declaring the
conformance is enough: Mojo provides `write_to`, which prints
`Interval(lo=0, hi=0)`. Write your own `write_to` when a shorter form reads
better in reports.
