# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Strategies inferred from types: `from_type[T]()` and `Arbitrary`.

Port of Hypothesis's `from_type`, `builds` and `register_type_strategy`, as
far as Mojo allows (see docs/differences-from-hypothesis.md, section 3.5).
Hypothesis inspects type annotations and `__init__` signatures at runtime;
proptest resolves the type at compile time:

1. a type that implements `Arbitrary` draws itself with its own
   `arbitrary(data)` (Hypothesis's `register_type_strategy`). This module
   implements `Arbitrary` for the standard types through struct
   extensions, recursively over their parameters:
   - integer and floating-point scalars (`Int`, `UInt8`, `Float32`, ...),
     `Bool` and `String`;
   - `List[T]`, `Optional[T]`, `Set[T]` and `Dict[K, V]`;
   - `Tuple[*Ts]` of one to six elements;
   so `Dict[Int8, List[Optional[Tuple[Bool, String]]]]` works like `Int`.
2. any other struct is built field by field (like Hypothesis's
   `builds(Cls)` with every argument inferred), recursively, using
   compile-time reflection on its fields.

Building a struct from its fields writes each field directly: it does not
call `__init__`, so any invariant that `__init__` would establish is not.
Give such types an `Arbitrary` implementation instead. Types that contain
anything else (pointers, SIMD vectors, MLIR types) are a compile-time
error.
"""

from std.collections import Set, Dict
from std.hash.hasher import default_hasher
from std.iter import downcast
from std.memory.alloc import unsafe_alloc
from std.reflection import reflect

from proptest.internal.data import ConjectureData, calc_label_from_name
from proptest.strategies.strategy import Strategy, Drawable
from proptest.strategies.core import (
    tuples,
    integers,
    integers_of,
    floats,
    floats32,
    booleans,
    text,
    lists,
    optionals,
    sets,
    dictionaries,
)


trait Arbitrary:
    """A type that knows how to draw itself (Hypothesis's
    `register_type_strategy`). `from_type` uses it in preference to
    anything else, including for fields of other structs.

    ```mojo
    @fieldwise_init
    struct Interval(Arbitrary, Copyable, Writable):
        var lo: Int
        var hi: Int

        @staticmethod
        def arbitrary(mut data: ConjectureData) raises -> Self:
            var lo = data.draw(integers(-100, 100))
            return Self(lo, data.draw(integers(lo, 100)))
    ```
    """

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        """Draw a value of this type."""
        ...


def draw_from_type[
    T: Movable & Deinitable
](mut data: ConjectureData) raises -> T:
    """Draw a value of type `T`, choosing the strategy at compile time."""
    comptime if conforms_to(T, Arbitrary):
        return rebind_var[T](downcast[T, Arbitrary].arbitrary(data))
    elif conforms_to(T, _StandardArbitrary):
        return downcast[T, _StandardArbitrary].draw_as[T](data)
    else:
        comptime assert reflect[
            T
        ].is_struct(), (
            "from_type: no strategy for this type; implement Arbitrary for it"
        )
        comptime types = reflect[T].field_types()
        comptime names = reflect[T].field_names()
        var p = unsafe_alloc[T](1)
        var base = p.unsafe_bitcast[UInt8]()
        try:
            comptime for i in range(reflect[T].field_count()):
                comptime FT = downcast[types[i], Movable & Deinitable]
                # one span per field, so the shrinker can work field by field
                comptime field_name = names[i]
                data.start_span(calc_label_from_name(field_name))
                var v = draw_from_type[FT](data)
                data.stop_span()
                comptime offset = reflect[T].field_offset[index=i]()
                base.unsafe_offset(offset).unsafe_bitcast[FT]().unsafe_write(v^)
        except e:
            # The fields written so far are leaked rather than destroyed:
            # this only happens when a test case is abandoned (overrun or
            # filtered out), and the memory is small.
            p.unsafe_free()
            raise e^
        var out = p.unsafe_take_pointee()
        p.unsafe_free()
        return out^


# ===----------------------------------------------------------------------=== #
# Arbitrary for the standard types
# ===----------------------------------------------------------------------=== #


trait _StandardArbitrary:
    """`Arbitrary` for the standard types, added by the extensions below.

    Separate from `Arbitrary` because some standard types (`Optional`,
    `Tuple`) are only conditionally movable, so their draw is generic over
    the (movable) type `Out` that `draw_from_type` asks for, which is always
    `Self`."""

    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        ...


comptime _Of[T: AnyType] = FromType[downcast[T, Drawable]]
"""The `from_type` strategy for a type parameter of a standard type (which
the standard types declare with weaker bounds than `Drawable`)."""


__extension SIMD(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime assert (
            Self.length == 1
        ), "from_type: SIMD vectors aren't supported, only scalars"
        comptime if Self.dtype == DType.int:
            return rebind_var[Out](data.draw(integers()))
        elif Self.dtype == DType.float64:
            return rebind_var[Out](data.draw(floats()))
        elif Self.dtype == DType.float32:
            return rebind_var[Out](data.draw(floats32()))
        else:
            comptime assert Self.dtype.is_integral(), (
                "from_type: only integer, Float64 and Float32 scalars are"
                " supported"
            )
            return rebind_var[Out](data.draw(integers_of[Self.dtype]()))


__extension Bool(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        return rebind_var[Out](data.draw(booleans()))


__extension String(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        return rebind_var[Out](data.draw(text()))


__extension List(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        return rebind_var[Out](data.draw(lists(_Of[Self.T]())))


__extension Optional(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        return rebind_var[Out](data.draw(optionals(_Of[Self.T]())))


__extension Set(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime assert (
            Self.H == default_hasher
        ), "from_type: only Sets with the default hasher are supported"
        comptime E = downcast[Self.T, Drawable & KeyElement & Copyable]
        return rebind_var[Out](data.draw(sets(FromType[E]())))


__extension Dict(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime assert (
            Self.H == default_hasher
        ), "from_type: only Dicts with the default hasher are supported"
        comptime K = downcast[Self.K, Drawable & KeyElement & Copyable]
        return rebind_var[Out](
            data.draw(dictionaries(FromType[K](), _Of[Self.V]()))
        )


__extension Tuple(_StandardArbitrary):
    @staticmethod
    def draw_as[
        Out: Movable & Deinitable
    ](mut data: ConjectureData) raises -> Out:
        comptime n = len(Self.Ts)
        comptime assert (
            n >= 1 and n <= 6
        ), "from_type: tuples of one to six elements are supported"
        comptime if n == 1:
            return rebind_var[Out](
                (draw_from_type[downcast[Self.Ts[0], Drawable]](data),)
            )
        elif n == 2:
            return rebind_var[Out](
                data.draw(tuples(_Of[Self.Ts[0]](), _Of[Self.Ts[1]]()))
            )
        elif n == 3:
            return rebind_var[Out](
                data.draw(
                    tuples(
                        _Of[Self.Ts[0]](),
                        _Of[Self.Ts[1]](),
                        _Of[Self.Ts[2]](),
                    )
                )
            )
        elif n == 4:
            return rebind_var[Out](
                data.draw(
                    tuples(
                        _Of[Self.Ts[0]](),
                        _Of[Self.Ts[1]](),
                        _Of[Self.Ts[2]](),
                        _Of[Self.Ts[3]](),
                    )
                )
            )
        elif n == 5:
            return rebind_var[Out](
                data.draw(
                    tuples(
                        _Of[Self.Ts[0]](),
                        _Of[Self.Ts[1]](),
                        _Of[Self.Ts[2]](),
                        _Of[Self.Ts[3]](),
                        _Of[Self.Ts[4]](),
                    )
                )
            )
        else:
            return rebind_var[Out](
                data.draw(
                    tuples(
                        _Of[Self.Ts[0]](),
                        _Of[Self.Ts[1]](),
                        _Of[Self.Ts[2]](),
                        _Of[Self.Ts[3]](),
                        _Of[Self.Ts[4]](),
                        _Of[Self.Ts[5]](),
                    )
                )
            )


# ===----------------------------------------------------------------------=== #
# from_type
# ===----------------------------------------------------------------------=== #


struct FromType[T: Drawable](Copyable, Strategy):
    """Values of type `T`; see `from_type()`."""

    comptime Value = Self.T

    def __init__(out self):
        pass

    def label(self) -> UInt64:
        return calc_label_from_name(
            String("from_type:", reflect[Self.T].name())
        )

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        return draw_from_type[Self.T](data)


def from_type[T: Drawable]() -> FromType[T]:
    """A strategy for values of type `T`, inferred from the type (Hypothesis's
    `from_type`; see this module's documentation for what is supported)."""
    return FromType[T]()


# ===----------------------------------------------------------------------=== #
# build: from_type with some fields drawn from given strategies
# ===----------------------------------------------------------------------=== #


trait FieldBinding(Deinitable, Movable):
    """A strategy for one named field of a struct; see `field()` and
    `build()`."""

    comptime field_name: StaticString
    """The field this binding fills."""
    comptime Value: Movable & Deinitable
    """The type of value it draws, which must be the field's type."""

    def draw_field(self, mut data: ConjectureData) raises -> Self.Value:
        """Draw the field's value."""
        ...


struct Field[name: StaticString, S: Strategy](
    Copyable where conforms_to(S, Copyable), FieldBinding
):
    """Field `name` drawn from strategy `S`; see `field()`."""

    comptime field_name = Self.name
    comptime Value = Self.S.Value
    var strategy: Self.S

    def __init__(out self, var strategy: Self.S):
        self.strategy = strategy^

    def draw_field(self, mut data: ConjectureData) raises -> Self.Value:
        return data.draw(self.strategy)


def field[name: StaticString, S: Strategy](var strategy: S) -> Field[name, S]:
    """Draw the field called `name` from `strategy`, in `build()`
    (RapidCheck's `gen::set(&T::member, gen)`)."""
    return Field[name, S](strategy^)


def _field_index[T: AnyType, name: StaticString]() -> Int:
    """The index of `T`'s field called `name`, or -1."""
    comptime names = reflect[T].field_names()
    comptime for i in range(reflect[T].field_count()):
        comptime if names[i] == name:
            return i
    return -1


def _binding_index[name: StaticString, *Fs: FieldBinding]() -> Int:
    """The index of the first binding for the field `name`, or -1."""
    comptime for j in range(len(Fs)):
        comptime if Fs[j].field_name == name:
            return j
    return -1


struct Built[T: Drawable, *Fs: FieldBinding](
    Copyable where Fs.all_conforms_to[Copyable](), Strategy
):
    """Values of struct `T` with some fields drawn from given strategies;
    see `build()`."""

    comptime Value = Self.T
    var fields: Tuple[*Self.Fs]

    def __init__(out self, var fields: Tuple[*Self.Fs]):
        comptime assert reflect[
            Self.T
        ].is_struct(), "build: the type must be a struct"
        comptime for j in range(len(Self.Fs)):
            comptime name = Self.Fs[j].field_name
            comptime i = _field_index[Self.T, name]()
            comptime assert i >= 0, String(
                "build: ", reflect[Self.T].name(), " has no field '", name, "'"
            )
            comptime assert _binding_index[name, *Self.Fs]() == j, String(
                "build: field '", name, "' is given twice"
            )
        self.fields = fields^

    def label(self) -> UInt64:
        return calc_label_from_name(String("build:", reflect[Self.T].name()))

    def do_draw(self, mut data: ConjectureData) raises -> Self.T:
        comptime types = reflect[Self.T].field_types()
        comptime names = reflect[Self.T].field_names()
        var p = unsafe_alloc[Self.T](1)
        var base = p.unsafe_bitcast[UInt8]()
        try:
            comptime for i in range(reflect[Self.T].field_count()):
                comptime FT = downcast[types[i], Movable & Deinitable]
                comptime field_name = names[i]
                comptime j = _binding_index[field_name, *Self.Fs]()
                data.start_span(calc_label_from_name(field_name))
                var v: FT
                comptime if j >= 0:
                    comptime assert Self.Fs[j].Value == FT, String(
                        "build: the strategy for field '",
                        field_name,
                        "' draws a different type from the field's",
                    )
                    v = rebind_var[FT](self.fields[j].draw_field(data))
                else:
                    v = draw_from_type[FT](data)
                data.stop_span()
                comptime offset = reflect[Self.T].field_offset[index=i]()
                base.unsafe_offset(offset).unsafe_bitcast[FT]().unsafe_write(v^)
        except e:
            # as in draw_from_type: fields written so far are leaked
            p.unsafe_free()
            raise e^
        var out = p.unsafe_take_pointee()
        p.unsafe_free()
        return out^


def build[
    T: Drawable, *Fs: FieldBinding & Copyable
](var *fields: *Fs) -> Built[T, *Fs]:
    """Values of struct `T` built field by field, drawing the fields named
    with `field()` from the given strategies.

    This is `from_type`'s construction for structs, with overrides
    (RapidCheck's `gen::build`):

    ```mojo
    build[Person](field["age"](integers(0, 120)), field["name"](text()))
    ```

    Field names and the strategies' types are checked at compile time.
    `build` always works field by field, even if `T` implements
    `Arbitrary`, so the fields must be valid in any combination."""
    return Built[T, *Fs](
        Tuple[*Fs](init_with=lambda [i: Int]() -> Fs[i]: fields[i].copy())
    )
