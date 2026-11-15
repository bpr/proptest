# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""`Traced` values: integers and strings that record their comparisons.

`traced(s)` draws a value from `s` (integers or text) wrapped in a
`Traced`, which compares, hashes and prints like the value but records
each comparison it takes part in (`==`, `!=`, `<`, `<=`, `>`, `>=`, and
for strings `startswith`, `endswith` and `in`). The fuzz loop
(`FuzzTarget.fuzz`) uses them to get past checks like `x == 4242` or
`cmd == "PUSH"`, and generation tries the compared-with values; see
`internal/comparisons.mojo`.

```mojo
def prop(x: Traced[Int]) raises:
    if x == 4242:
        fail("found the magic number")

var target = fuzz_target(traced(integers()), prop)
_ = target.fuzz(10)
```

`Traced[T]` conforms to `Comparable` and `Hashable` when `T` does, so it can
be passed to generic code written against those traits: comparisons made
there are recorded too. The plain value is `x.value`.
"""

from std.hash import Hasher
from std.iter import downcast
from std.memory import ArcPointer
from std.reflection import call_location, SourceLocation

from proptest.internal.choice import ChoiceValue
from proptest.internal.comparisons import (
    ComparisonLog,
    MAX_COMPARISONS,
    int_closeness,
    mix,
    text_closeness,
)
from proptest.internal.data import ConjectureData
from proptest.internal.intervals import string_to_codepoints
from proptest.strategies.strategy import QuotedInReports, Strategy


comptime _Value = Comparable & Copyable & Deinitable & Hashable & Writable
"""What `Traced` requires of its type (the supported types, integer scalars
and `String`, are checked with `_Traceable`, whose conformances are only
visible in this module)."""


trait _Traceable(_Value):
    """The types `Traced` supports: integer scalars and `String`."""

    def _trace_choice(self) -> ChoiceValue:
        """This value as the choice that would produce it."""
        ...

    def _trace_closeness(self, other: Self) -> Int:
        """How close this value is to `other` (higher is closer)."""
        ...


__extension SIMD(_Traceable):
    def _trace_choice(self) -> ChoiceValue:
        comptime assert (
            Self.length == 1 and Self.dtype.is_integral()
        ), "Traced: only integer scalars and String are supported"
        return ChoiceValue(integer=rebind[Int128](self.cast[DType.int128]()))

    def _trace_closeness(self, other: Self) -> Int:
        return int_closeness(
            rebind[Int128](self.cast[DType.int128]()),
            rebind[Int128](other.cast[DType.int128]()),
        )


__extension String(_Traceable):
    def _trace_choice(self) -> ChoiceValue:
        return ChoiceValue(string=string_to_codepoints(self))

    def _trace_closeness(self, other: Self) -> Int:
        return text_closeness(
            string_to_codepoints(self), string_to_codepoints(other)
        )


@always_inline
def _choice[T: _Value](v: T) -> ChoiceValue:
    comptime assert conforms_to(
        T, _Traceable
    ), "Traced: only integer scalars and String are supported"
    return rebind[downcast[T, _Traceable]](v)._trace_choice()


@always_inline
def _closeness[T: _Value](a: T, b: T) -> Int:
    comptime D = downcast[T, _Traceable]
    return rebind[D](a)._trace_closeness(rebind[D](b))


@always_inline
def _site(loc: SourceLocation) -> UInt64:
    return mix(
        mix(UInt64(loc.line()), UInt64(loc.column())),
        UInt64(hash(loc.file_name())),
    )


struct Traced[T: _Value](
    Comparable,
    Copyable,
    Hashable,
    Intable where conforms_to(T, Intable),
    QuotedInReports where T == String,
    Writable,
):
    """A value that records the comparisons it takes part in; see
    `traced()`."""

    var value: Self.T
    """The plain value."""
    var _log: ArcPointer[ComparisonLog]

    def __init__(out self, var value: Self.T, log: ArcPointer[ComparisonLog]):
        """Wrap `value`, recording its comparisons in `log` (a test case's
        `ConjectureData.comparisons`)."""
        self.value = value^
        self._log = log

    def __init__(out self, var value: Self.T):
        """Wrap `value`, recording its comparisons nowhere in particular
        (for calling code that takes a `Traced` outside a test)."""
        self.value = value^
        self._log = ArcPointer(ComparisonLog())

    @always_inline
    def _record(self, other: Self.T, loc: SourceLocation):
        if len(self._log[].entries) >= MAX_COMPARISONS:
            return
        self._log[].record(
            _site(loc),
            _choice(self.value),
            _choice(other),
            _closeness(self.value, other),
        )

    @always_inline
    def _record_both(self, other: Self, loc: SourceLocation):
        self._record(other.value, loc)
        other._record(self.value, loc)

    # comparisons with plain values

    @always_inline
    def __eq__(self, other: Self.T) -> Bool:
        self._record(other, call_location())
        return self.value == other

    @always_inline
    def __ne__(self, other: Self.T) -> Bool:
        self._record(other, call_location())
        return self.value != other

    @always_inline
    def __lt__(self, other: Self.T) -> Bool:
        self._record(other, call_location())
        return self.value < other

    @always_inline
    def __le__(self, other: Self.T) -> Bool:
        self._record(other, call_location())
        return self.value <= other

    @always_inline
    def __gt__(self, other: Self.T) -> Bool:
        self._record(other, call_location())
        return self.value > other

    @always_inline
    def __ge__(self, other: Self.T) -> Bool:
        self._record(other, call_location())
        return self.value >= other

    # comparisons with other traced values: both record

    @always_inline
    def __eq__(self, other: Self) -> Bool:
        self._record_both(other, call_location())
        return self.value == other.value

    @always_inline
    def __ne__(self, other: Self) -> Bool:
        self._record_both(other, call_location())
        return self.value != other.value

    @always_inline
    def __lt__(self, other: Self) -> Bool:
        self._record_both(other, call_location())
        return self.value < other.value

    @always_inline
    def __le__(self, other: Self) -> Bool:
        self._record_both(other, call_location())
        return self.value <= other.value

    @always_inline
    def __gt__(self, other: Self) -> Bool:
        self._record_both(other, call_location())
        return self.value > other.value

    @always_inline
    def __ge__(self, other: Self) -> Bool:
        self._record_both(other, call_location())
        return self.value >= other.value

    # strings

    @always_inline
    def startswith(self, prefix: String) -> Bool where Self.T == String:
        """Whether the string starts with `prefix` (recorded as a
        comparison with `prefix`)."""
        var s = rebind[String](self.value)
        self._record(rebind[Self.T](prefix), call_location())
        return s.startswith(prefix)

    @always_inline
    def endswith(self, suffix: String) -> Bool where Self.T == String:
        """Whether the string ends with `suffix` (recorded as a
        comparison with `suffix`)."""
        var s = rebind[String](self.value)
        self._record(rebind[Self.T](suffix), call_location())
        return s.endswith(suffix)

    @always_inline
    def __contains__(self, substr: String) -> Bool where Self.T == String:
        """Whether the string contains `substr` (recorded as a comparison
        with `substr`)."""
        var s = rebind[String](self.value)
        self._record(rebind[Self.T](substr), call_location())
        return substr in s

    def byte_length(self) -> Int where Self.T == String:
        return rebind[String](self.value).byte_length()

    # integers

    def __int__(self) -> Int where conforms_to(Self.T, Intable):
        return Int(_choice(self.value).i)

    def __hash__[H: Hasher](self, mut hasher: H):
        self.value.__hash__(hasher)

    def write_to(self, mut writer: Some[Writer]):
        self.value.write_to(writer)

    def write_repr_to(self, mut writer: Some[Writer]):
        self.value.write_repr_to(writer)


struct TracedStrategy[S: Strategy](
    Copyable where conforms_to(S, Copyable), Strategy
):
    """Values from a strategy, wrapped in `Traced`; see `traced()`."""

    comptime Value = Traced[downcast[Self.S.Value, _Value]]
    var inner: Self.S

    def __init__(out self, var inner: Self.S):
        self.inner = inner^

    def label(self) -> UInt64:
        return self.inner.label() ^ 0x7472616365640A

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var v = data.draw(self.inner)
        return Traced(
            rebind_var[downcast[Self.S.Value, _Value]](v^),
            data.comparisons,
        )


def traced[S: Strategy](var strategy: S) -> TracedStrategy[S]:
    """Values from `strategy` (integers or text), wrapped in `Traced` so
    that the fuzz loop sees what they're compared with."""
    comptime assert conforms_to(
        S.Value, _Traceable
    ), "traced: the strategy must produce integers or String"
    return TracedStrategy[S](strategy^)
