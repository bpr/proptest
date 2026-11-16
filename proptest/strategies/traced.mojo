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

Arithmetic on a `Traced` value gives a `Traced` value. While the result
is an invertible function of one drawn value (adding, subtracting,
multiplying, shifting left, XOR, `-` and `~` for integers; text added at
either end for strings), each of its comparisons also records the drawn
value against the one that would make the result equal the compared-with
value, so input-to-state replacement still applies. Other operations
(`//`, `%`, `&`, `|`, `>>`) lose that link; their results still record
comparisons.

`Traced[T]` conforms to `Comparable` and `Hashable` when `T` does, so it can
be passed to generic code written against those traits: comparisons made
there are recorded too. The plain value is `x.value`.
"""

from std.hash import Hasher
from std.iter import downcast
from std.memory import ArcPointer
from std.reflection import call_location, SourceLocation

from proptest.internal.choice import ChoiceValue, INTEGER
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

    def _trace_op[op: StaticString](self, other: Self) -> Self:
        """`self <op> other` (`~` ignores `other`; for strings, only
        `+`)."""
        ...

    def _trace_wrap(self, i: Int128) -> Int128:
        """`i` wrapped to this type's range, as its arithmetic wraps."""
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

    def _trace_op[op: StaticString](self, other: Self) -> Self:
        comptime if op == "+":
            return self + other
        elif op == "-":
            return self - other
        elif op == "*":
            return self * other
        elif op == "//":
            return self // other
        elif op == "%":
            return self % other
        elif op == "&":
            return self & other
        elif op == "|":
            return self | other
        elif op == "^":
            return self ^ other
        elif op == "<<":
            return self << other
        elif op == "~":
            return ~self
        else:
            comptime assert op == ">>", "Traced: unknown operator"
            return self >> other

    def _trace_wrap(self, i: Int128) -> Int128:
        return rebind[Int128](
            Scalar[DType.int128](i).cast[Self.dtype]().cast[DType.int128]()
        )


__extension String(_Traceable):
    def _trace_choice(self) -> ChoiceValue:
        return ChoiceValue(string=string_to_codepoints(self))

    def _trace_closeness(self, other: Self) -> Int:
        return text_closeness(
            string_to_codepoints(self), string_to_codepoints(other)
        )

    def _trace_op[op: StaticString](self, other: Self) -> Self:
        comptime assert op == "+", "Traced: strings only support +"
        return self + other

    def _trace_wrap(self, i: Int128) -> Int128:
        return i


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
def _op[op: StaticString, T: _Value](a: T, b: T) -> T:
    comptime D = downcast[T, _Traceable]
    return rebind_var[T](rebind[D](a)._trace_op[op](rebind[D](b)))


@always_inline
def _wrap[T: _Value](v: T, i: Int128) -> Int128:
    return rebind[downcast[T, _Traceable]](v)._trace_wrap(i)


comptime _SAME = 0
"""The value is the source itself (e.g. as drawn)."""
comptime _STEPS = 1
"""The value is the source after `steps` (integers)."""
comptime _AFFIX = 2
"""value = pre + source + suf (strings)."""
comptime _LOST = 3
"""The value isn't an invertible function of one source."""

comptime _ADD: UInt8 = 0
comptime _MUL: UInt8 = 1
comptime _XOR: UInt8 = 2

comptime _MAX_STEPS = 16
"""Longer computations are given up on."""


struct _Origin(Copyable):
    """How a `Traced` value was computed from a source value (the value of
    a choice, if it was drawn by `traced`), so that the value a comparison
    wanted can be translated back into the source value that produces it.
    """

    var kind: Int
    var source: ChoiceValue
    var ops: List[UInt8]
    """For integers: each step's operation (`_ADD`, `_MUL`, `_XOR`)..."""
    var ks: List[Int128]
    """... and its operand."""
    var pre: List[UInt32]
    var suf: List[UInt32]

    def __init__(out self, kind: Int, var source: ChoiceValue):
        self.kind = kind
        self.source = source^
        self.ops = List[UInt8]()
        self.ks = List[Int128]()
        self.pre = List[UInt32]()
        self.suf = List[UInt32]()

    @staticmethod
    def same() -> Self:
        return Self(_SAME, ChoiceValue(integer=0))

    @staticmethod
    def lost() -> Self:
        return Self(_LOST, ChoiceValue(integer=0))

    @staticmethod
    def of(var value: ChoiceValue) -> Self:
        """No steps yet, from `value` as the source."""
        var k = _STEPS if value.kind == INTEGER else _AFFIX
        return Self(k, value^)

    def then(self, op: UInt8, k: Int128) -> Self:
        """This, followed by `op k`."""
        if self.kind != _STEPS or len(self.ops) >= _MAX_STEPS:
            return Self.lost()
        if op == _MUL and k == 0:
            return Self.lost()
        var o = self.copy()
        o.ops.append(op)
        o.ks.append(k)
        return o^

    def affixed(self, pre: List[UInt32], suf: List[UInt32]) -> Self:
        if self.kind != _AFFIX:
            return Self.lost()
        var o = self.copy()
        var p = pre.copy()
        p.extend(o.pre^)
        o.pre = p^
        o.suf.extend(suf.copy())
        return o^

    def solve[T: _Value](self, rhs: ChoiceValue, like: T) -> Optional[Int128]:
        """The source integer whose value would be `rhs`: the steps undone
        in reverse, wrapping to `T` as its arithmetic does."""
        if rhs.kind != INTEGER:
            return None
        var v = rhs.i
        for i in reversed(range(len(self.ops))):
            var k = self.ks[i]
            if self.ops[i] == _ADD:
                if v >= _BOUND or v <= -_BOUND or k >= _BOUND or k <= -_BOUND:
                    return None
                v = _wrap(like, v - k)
            elif self.ops[i] == _MUL:
                if v % k != 0:
                    return None
                v = _wrap(like, v // k)
            else:
                v = _wrap(like, v ^ k)
        return v

    def solve_text(self, rhs: ChoiceValue) -> Optional[ChoiceValue]:
        """The source string whose value would be `rhs`: `rhs` without the
        prefix (which it must start with) and suffix (if it ends with it;
        a `startswith` operand needn't)."""
        if self.kind != _AFFIX or rhs.kind != self.source.kind:
            return None
        ref r = rhs.seq
        var n = len(self.pre)
        if len(r) < n:
            return None
        for i in range(n):
            if r[i] != self.pre[i]:
                return None
        var end = len(r)
        var m = len(self.suf)
        if m > 0 and end - n >= m:
            var ok = True
            for i in range(m):
                if r[end - m + i] != self.suf[i]:
                    ok = False
                    break
            if ok:
                end -= m
        var seq = List[UInt32]()
        for i in range(n, end):
            seq.append(r[i])
        return ChoiceValue(string=seq^)


comptime _BOUND: Int128 = Int128(1) << 120


def _derive[
    op: StaticString, T: _Value
](var o: _Origin, other: T, variable_on_left: Bool) -> _Origin:
    """The origin of `v <op> other` (or `other <op> v`) given `v`'s."""
    var c = _choice(other)
    if c.kind != INTEGER:  # strings: only +
        if variable_on_left:
            return o.affixed(List[UInt32](), c.seq)
        return o.affixed(c.seq, List[UInt32]())
    var k = c.i
    comptime if op == "+":
        return o.then(_ADD, k)
    elif op == "-":
        if variable_on_left:
            return o.then(_ADD, -k)
        return o.then(_MUL, -1).then(_ADD, k)
    elif op == "*":
        return o.then(_MUL, k)
    elif op == "^":
        return o.then(_XOR, k)
    elif op == "<<":
        if variable_on_left and k >= 0 and k < 100:
            return o.then(_MUL, Int128(1) << k)
        return _Origin.lost()
    else:
        return _Origin.lost()


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
    var _origin: _Origin

    def __init__(out self, var value: Self.T, log: ArcPointer[ComparisonLog]):
        """Wrap `value`, recording its comparisons in `log` (a test case's
        `ConjectureData.comparisons`)."""
        self.value = value^
        self._log = log
        self._origin = _Origin.same()

    def __init__(out self, var value: Self.T):
        """Wrap `value`, recording its comparisons nowhere in particular
        (for calling code that takes a `Traced` outside a test)."""
        self.value = value^
        self._log = ArcPointer(ComparisonLog())
        self._origin = _Origin.same()

    def __init__(
        out self,
        *,
        var _value: Self.T,
        _log: ArcPointer[ComparisonLog],
        var _origin: _Origin,
    ):
        self.value = _value^
        self._log = _log
        self._origin = _origin^

    @always_inline
    def _record(self, other: Self.T, loc: SourceLocation):
        if len(self._log[].entries) >= MAX_COMPARISONS:
            return
        var site = _site(loc)
        var rhs = _choice(other)
        var closeness = _closeness(self.value, other)
        self._log[].record(site, _choice(self.value), rhs.copy(), closeness)
        # computed from a source: also record what the source would need
        # to be, for input-to-state replacement
        ref o = self._origin
        if o.kind == _SAME or o.kind == _LOST:
            return
        var wanted: Optional[ChoiceValue] = None
        if o.kind == _AFFIX:
            wanted = o.solve_text(rhs)
        else:
            var solved = o.solve(rhs, self.value)
            if solved:
                wanted = ChoiceValue(integer=solved.value())
        if wanted:
            self._log[].record(site, o.source.copy(), wanted.take(), closeness)

    # arithmetic: the result is traced too, and remembers how it was
    # computed from a drawn value (see `_Origin`)

    def _lifted(self) -> _Origin:
        if self._origin.kind == _SAME:
            return _Origin.of(_choice(self.value))
        return self._origin.copy()

    def _make(self, var value: Self.T, var origin: _Origin) -> Self:
        return Self(_value=value^, _log=self._log, _origin=origin^)

    def _arith[op: StaticString](self, other: Self.T) -> Self:
        return self._make(
            _op[op](self.value, other),
            _derive[op](self._lifted(), other, True),
        )

    def _rarith[op: StaticString](self, other: Self.T) -> Self:
        return self._make(
            _op[op](other, self.value),
            _derive[op](self._lifted(), other, False),
        )

    def _arith2[op: StaticString](self, other: Self) -> Self:
        var v = _op[op](self.value, other.value)
        if self._origin.kind != _LOST:
            return self._make(
                v^, _derive[op](self._lifted(), other.value, True)
            )
        return self._make(v^, _derive[op](other._lifted(), self.value, False))

    def __add__(self, other: Self.T) -> Self:
        return self._arith["+"](other)

    def __add__(self, other: Self) -> Self:
        return self._arith2["+"](other)

    def __radd__(self, other: Self.T) -> Self:
        return self._rarith["+"](other)

    def __iadd__(mut self, other: Self.T):
        self = self + other

    def __sub__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._arith["-"](other)

    def __sub__(self, other: Self) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["-"](other)

    def __rsub__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["-"](other)

    def __isub__(mut self, other: Self.T) where conforms_to(Self.T, Intable):
        self = self - other

    def __mul__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._arith["*"](other)

    def __mul__(self, other: Self) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["*"](other)

    def __rmul__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["*"](other)

    def __imul__(mut self, other: Self.T) where conforms_to(Self.T, Intable):
        self = self * other

    def __floordiv__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._arith["//"](other)

    def __floordiv__(
        self, other: Self
    ) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["//"](other)

    def __rfloordiv__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["//"](other)

    def __mod__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._arith["%"](other)

    def __mod__(self, other: Self) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["%"](other)

    def __rmod__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["%"](other)

    def __and__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._arith["&"](other)

    def __and__(self, other: Self) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["&"](other)

    def __rand__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["&"](other)

    def __or__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._arith["|"](other)

    def __or__(self, other: Self) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["|"](other)

    def __ror__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["|"](other)

    def __xor__(self, other: Self.T) -> Self where conforms_to(Self.T, Intable):
        return self._arith["^"](other)

    def __xor__(self, other: Self) -> Self where conforms_to(Self.T, Intable):
        return self._arith2["^"](other)

    def __rxor__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._rarith["^"](other)

    def __lshift__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._arith["<<"](other)

    def __rshift__(
        self, other: Self.T
    ) -> Self where conforms_to(Self.T, Intable):
        return self._arith[">>"](other)

    def __neg__(self) -> Self where conforms_to(Self.T, Intable):
        var zero = _op["-"](self.value, self.value)
        return self._rarith["-"](zero)

    def __invert__(self) -> Self where conforms_to(Self.T, Intable):
        return self._make(
            _op["~"](self.value, self.value),
            self._lifted().then(_XOR, -1),
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
