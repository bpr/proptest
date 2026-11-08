# Types

## `from_type`

`from_type[T]()` chooses a strategy for `T` at compile time, in this
order:

1. If `T` implements `Arbitrary`, its `arbitrary(data)` method.
2. If `T` is a standard type, its built-in strategy:

   | Type | Strategy |
   |---|---|
   | `Int`, `UInt`, `Int8` ... `Int128`, `UInt8` ... `UInt128` | `integers_of` over the type's range |
   | `Float64`, `Float32` | `floats()`, `floats32()` |
   | `Bool` | `booleans()` |
   | `String` | `text()` |
   | `List[T]` | `lists(from_type[T]())` |
   | `Optional[T]` | `optionals(from_type[T]())` |
   | `Set[T]` | `sets(from_type[T]())` |
   | `Dict[K, V]` | `dictionaries(from_type[K](), from_type[V]())` |
   | `Tuple[...]` (one to six elements) | `tuples(...)` |

3. Otherwise, if `T` is a struct, each field drawn with `from_type`, in
   declaration order, each in its own span. The struct's `__init__` is
   not called.

A type that matches none of these is a compile error.

### `draw_from_type`

```mojo-sig
draw_from_type[T](mut data: ConjectureData) raises -> T
```

The function behind `from_type`, for drawing a value of a type inside a
strategy or test.

## `Arbitrary`

```mojo-sig
trait Arbitrary:
    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self: ...
```

A type's own strategy, used by `from_type`, `check`, and struct fields of
the type.

## `build` and `field`

```mojo-sig
build[T: Drawable](*fields: FieldBinding & Copyable) -> Built[T, *Fs]
field[name: StaticString](strategy: S) -> Field[name, S]
```

`T` built field by field, as in step 3 above, with each field named by a
`field` binding drawn from its strategy instead (RapidCheck's
`gen::build`). Compile errors, each naming the field, for:

- a name that isn't a field of `T`;
- a field bound twice;
- a strategy whose value type isn't the field's type.

`build` always works field by field, even if `T` implements `Arbitrary`.

## Constraint types

Each implements `Arbitrary`, holds its value in `.value`, and prints as the
value alone. All are `Copyable` when the value type is.

| Type | Values |
|---|---|
| `Bounded[lo: Int, hi: Int, T = Int]` | `T` values in `[lo, hi]`; `T` is a numeric scalar type, such as `UInt8` or `Float64` |
| `Positive[T]` | values `> 0`; `T` is an integer scalar, `Float64`, or `Float32` (finite) |
| `NonNegative[T]` | values `>= 0`; as for `Positive` |
| `NonZero[T]` | values `!= 0`; as for `Positive` |
| `NonEmpty[T]` | `List`, `String`, `Set`, or `Dict` values with at least one element |
| `Sorted[List[T]]` | lists in ascending order; `T` is `Comparable` |
| `Blind[T]` | any `T`, printed as `<hidden>` |
| `Via[f]` | the value `f(data)` returns, for `f: def(mut ConjectureData) raises thin -> T` |

Constraint types can be nested where the types allow it, such as
`NonEmpty[List[Positive[Int]]]`.

## Test types

### `PolyA`, `PolyB`, `PolyC`, `Poly[tag]`

Opaque stand-in types for testing generic code (QuickCheck's `Poly`). Each
wraps an `Int` (`.value`), and supports only equality, ordering, hashing,
and printing: `PolyA` prints as `A(3)`. `Poly[tag]` makes more, with any
`StaticString` tag.

### `Index`

A position in a collection whose length isn't known when the index is
drawn (Rust proptest's `sample::Index`). `index.get(size)` returns a
position in `[0, size)` and raises if `size <= 0`. Shrinks towards the
first position. Prints as a fraction of the way through the collection,
such as `Index(0.25)`.

### `Function[A, R]`

A generated function from `functions[A](returns)`. Call it as `f(x)`
(which raises after its test case has ended). It's memoized, and prints as
the table of calls made: `{1->1, 2->0}`. `A` must be `KeyElement`,
`Copyable`, and `Writable`.
