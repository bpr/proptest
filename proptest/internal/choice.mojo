# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The choice sequence: typed choices, their constraints and their order.

Port of `hypothesis.internal.conjecture.choice`. A test case is a sequence
of *choices*, each an integer, float, boolean, byte string or (codepoint)
string, drawn under some *constraints*. Every choice type has a total
"simplicity" order (`choice_to_index` in Hypothesis), which the shrinker
uses to decide which of two test cases is simpler.

Differences from Hypothesis:

- Integers are 128-bit (`Int128`) rather than arbitrary precision, which
  covers every Mojo integer type including `UInt64` and `Int64`.
- Strings are stored as lists of codepoints and bytes as lists of byte
  values, in the same `seq` field.
- Integer `weights` are a list of probabilities for `min_value`,
  `min_value + 1`, ... (summing to 1), not Hypothesis's mapping of some
  values to probabilities with the rest uniform. They only change how
  values are generated; the simplicity order ignores them.
- Collection choices are compared structurally (shortlex) instead of by
  materialising their (possibly enormous) index.
"""

from std.memory import ArcPointer
from std.hash import Hasher
from std.math import isnan, isinf, ceil, floor, copysign

from proptest.internal.floats import (
    float_to_int,
    int_to_float,
    float_to_lex,
    lex_to_float,
    float_permitted,
    clamp_float,
    is_negative,
    pos_inf,
    neg_inf,
    smallest_subnormal,
)
from proptest.internal.intervals import IntervalSet, codepoints_to_string


comptime INTEGER: UInt8 = 0
comptime FLOAT: UInt8 = 1
comptime BOOLEAN: UInt8 = 2
comptime BYTES: UInt8 = 3
comptime STRING: UInt8 = 4

comptime COLLECTION_DEFAULT_MAX_SIZE = 1 << 40
"""Stands in for Hypothesis's "arbitrarily large" collection maximum."""


def kind_name(kind: UInt8) -> StaticString:
    if kind == INTEGER:
        return "integer"
    if kind == FLOAT:
        return "float"
    if kind == BOOLEAN:
        return "boolean"
    if kind == BYTES:
        return "bytes"
    return "string"


struct ChoiceTooLarge(Writable):
    def write_to(self, mut writer: Some[Writer]):
        writer.write("ChoiceTooLarge")


# ===----------------------------------------------------------------------=== #
# Values
# ===----------------------------------------------------------------------=== #


struct ChoiceValue(Copyable, Equatable, Hashable, Writable):
    """One choice: a tagged union of the five choice types."""

    var kind: UInt8
    var i: Int128
    """The value of an integer choice, or 0/1 for a boolean."""
    var f: Float64
    """The value of a float choice."""
    var seq: List[UInt32]
    """Byte values of a bytes choice, or codepoints of a string choice."""

    def __init__(out self, *, integer: Int128):
        self.kind = INTEGER
        self.i = integer
        self.f = 0
        self.seq = List[UInt32]()

    def __init__(out self, *, float: Float64):
        self.kind = FLOAT
        self.i = 0
        self.f = float
        self.seq = List[UInt32]()

    def __init__(out self, *, boolean: Bool):
        self.kind = BOOLEAN
        self.i = Int128(1) if boolean else Int128(0)
        self.f = 0
        self.seq = List[UInt32]()

    def __init__(out self, *, var bytes: List[UInt32]):
        self.kind = BYTES
        self.i = 0
        self.f = 0
        self.seq = bytes^

    def __init__(out self, *, var string: List[UInt32]):
        self.kind = STRING
        self.i = 0
        self.f = 0
        self.seq = string^

    def as_bool(self) -> Bool:
        return self.i != 0

    def __eq__(self, other: Self) -> Bool:
        """Equality by choice key: floats compare bitwise (so -0.0 != 0.0
        and a NaN equals itself)."""
        if self.kind != other.kind:
            return False
        if self.kind == FLOAT:
            return float_to_int(self.f) == float_to_int(other.f)
        if self.kind == BYTES or self.kind == STRING:
            return self.seq == other.seq
        return self.i == other.i

    def __hash__[H: Hasher](self, mut hasher: H):
        (self.kind).__hash__(hasher)
        if self.kind == FLOAT:
            (float_to_int(self.f)).__hash__(hasher)
        elif self.kind == BYTES or self.kind == STRING:
            (self.seq).__hash__(hasher)
        else:
            (UInt64(UInt128(self.i) & UInt128(UInt64.MAX))).__hash__(hasher)
            (UInt64(UInt128(self.i) >> 64)).__hash__(hasher)

    def write_to(self, mut writer: Some[Writer]):
        if self.kind == INTEGER:
            writer.write(self.i)
        elif self.kind == FLOAT:
            writer.write(self.f)
        elif self.kind == BOOLEAN:
            writer.write("True" if self.i != 0 else "False")
        elif self.kind == BYTES:
            writer.write("b[")
            for k in range(len(self.seq)):
                if k > 0:
                    writer.write(", ")
                writer.write(self.seq[k])
            writer.write("]")
        else:
            writer.write(repr(codepoints_to_string(self.seq)))


# ===----------------------------------------------------------------------=== #
# Constraints
# ===----------------------------------------------------------------------=== #


def _same_weights(
    a: Optional[ArcPointer[List[Float64]]],
    b: Optional[ArcPointer[List[Float64]]],
) -> Bool:
    if not a or not b:
        return not a and not b
    return a.value()[] == b.value()[]


struct Constraints(Copyable, Equatable, Writable):
    """The constraints a choice was drawn under. Only the fields relevant to
    `kind` are meaningful."""

    var kind: UInt8
    # integer
    var has_min: Bool
    var has_max: Bool
    var min_value: Int128
    var max_value: Int128
    var shrink_towards: Int128
    var weights: Optional[ArcPointer[List[Float64]]]
    """Probabilities of `min_value`, `min_value + 1`, ..., or None."""
    # float
    var fmin: Float64
    var fmax: Float64
    var allow_nan: Bool
    var smallest_nonzero_magnitude: Float64
    # boolean
    var p: Float64
    # bytes / string
    var min_size: Int
    var max_size: Int
    var intervals: Optional[ArcPointer[IntervalSet]]

    def __init__(out self, kind: UInt8):
        self.kind = kind
        self.has_min = False
        self.has_max = False
        self.min_value = 0
        self.max_value = 0
        self.shrink_towards = 0
        self.weights = None
        self.fmin = neg_inf()
        self.fmax = pos_inf()
        self.allow_nan = True
        self.smallest_nonzero_magnitude = smallest_subnormal()
        self.p = 0.5
        self.min_size = 0
        self.max_size = COLLECTION_DEFAULT_MAX_SIZE
        self.intervals = None

    @staticmethod
    def integer(
        min_value: Optional[Int128] = None,
        max_value: Optional[Int128] = None,
        shrink_towards: Int128 = 0,
        weights: Optional[ArcPointer[List[Float64]]] = None,
    ) -> Self:
        var c = Self(INTEGER)
        c.weights = weights
        if min_value:
            c.has_min = True
            c.min_value = min_value.value()
        if max_value:
            c.has_max = True
            c.max_value = max_value.value()
        c.shrink_towards = shrink_towards
        return c^

    @staticmethod
    def float(
        min_value: Float64,
        max_value: Float64,
        allow_nan: Bool,
        smallest_nonzero_magnitude: Float64,
    ) -> Self:
        var c = Self(FLOAT)
        c.fmin = min_value
        c.fmax = max_value
        c.allow_nan = allow_nan
        c.smallest_nonzero_magnitude = smallest_nonzero_magnitude
        return c^

    @staticmethod
    def boolean(p: Float64) -> Self:
        var c = Self(BOOLEAN)
        c.p = p
        return c^

    @staticmethod
    def bytes(min_size: Int, max_size: Int) -> Self:
        var c = Self(BYTES)
        c.min_size = min_size
        c.max_size = max_size
        return c^

    @staticmethod
    def string(
        intervals: ArcPointer[IntervalSet], min_size: Int, max_size: Int
    ) -> Self:
        var c = Self(STRING)
        c.min_size = min_size
        c.max_size = max_size
        c.intervals = intervals
        return c^

    def alphabet(self) -> ref[self.intervals.value()[]] IntervalSet:
        return self.intervals.value()[]

    def alphabet_size(self) -> Int:
        if self.kind == BYTES:
            return 256
        return len(self.intervals.value()[])

    def __eq__(self, other: Self) -> Bool:
        if self.kind != other.kind:
            return False
        if self.kind == INTEGER:
            return (
                self.has_min == other.has_min
                and self.has_max == other.has_max
                and (not self.has_min or self.min_value == other.min_value)
                and (not self.has_max or self.max_value == other.max_value)
                and self.shrink_towards == other.shrink_towards
                and _same_weights(self.weights, other.weights)
            )
        if self.kind == FLOAT:
            return (
                float_to_int(self.fmin) == float_to_int(other.fmin)
                and float_to_int(self.fmax) == float_to_int(other.fmax)
                and self.allow_nan == other.allow_nan
                and self.smallest_nonzero_magnitude
                == other.smallest_nonzero_magnitude
            )
        if self.kind == BOOLEAN:
            return self.p == other.p
        if self.min_size != other.min_size or self.max_size != other.max_size:
            return False
        if self.kind == STRING:
            return self.alphabet() == other.alphabet()
        return True

    def write_to(self, mut writer: Some[Writer]):
        if self.kind == INTEGER:
            writer.write("{min_value: ")
            if self.has_min:
                writer.write(self.min_value)
            else:
                writer.write("None")
            writer.write(", max_value: ")
            if self.has_max:
                writer.write(self.max_value)
            else:
                writer.write("None")
            writer.write(", shrink_towards: ", self.shrink_towards, "}")
        elif self.kind == FLOAT:
            writer.write(
                "{min_value: ",
                self.fmin,
                ", max_value: ",
                self.fmax,
                ", allow_nan: ",
                self.allow_nan,
                "}",
            )
        elif self.kind == BOOLEAN:
            writer.write("{p: ", self.p, "}")
        else:
            writer.write(
                "{min_size: ", self.min_size, ", max_size: ", self.max_size, "}"
            )


# ===----------------------------------------------------------------------=== #
# Nodes
# ===----------------------------------------------------------------------=== #


struct ChoiceNode(Copyable, Writable):
    """A choice together with the constraints it was drawn under."""

    var value: ChoiceValue
    var constraints: Constraints
    var was_forced: Bool
    var index: Int

    def __init__(
        out self,
        var value: ChoiceValue,
        var constraints: Constraints,
        was_forced: Bool,
        index: Int = -1,
    ):
        self.value = value^
        self.constraints = constraints^
        self.was_forced = was_forced
        self.index = index

    @always_inline
    def kind(self) -> UInt8:
        return self.value.kind

    def with_value(self, var value: ChoiceValue) -> Self:
        """A copy with a different value (and no index)."""
        return Self(value^, self.constraints.copy(), self.was_forced)

    def trivial(self) -> Bool:
        """Whether this node is as simple as it can be on its own."""
        if self.was_forced:
            return True
        if self.kind() != FLOAT:
            return self.value == choice_simplest(self.constraints)
        var c = self.constraints.copy()
        var target = 0.0
        if isinf(c.fmin) and c.fmin < 0 and isinf(c.fmax) and c.fmax > 0:
            return self.value == ChoiceValue(float=target)
        if (
            not isinf(c.fmin)
            and not isinf(c.fmax)
            and ceil(c.fmin) <= floor(c.fmax)
        ):
            target = max(ceil(c.fmin), target)
            target = min(floor(c.fmax), target)
            return self.value == ChoiceValue(float=target)
        return False

    def write_to(self, mut writer: Some[Writer]):
        writer.write(kind_name(self.kind()), " ", self.value)
        if self.was_forced:
            writer.write(" [forced]")
        writer.write(" ", self.constraints)


# ===----------------------------------------------------------------------=== #
# Ordering
# ===----------------------------------------------------------------------=== #


def zigzag_index(value: Int128, shrink_towards: Int128) -> UInt128:
    """The zigzag order around `shrink_towards`.

    value | 0  1 -1  2 -2 ...  ->  index | 0  1  2  3  4 ...
    """
    var d = shrink_towards - value
    var ad = UInt128(-d) if d < 0 else UInt128(d)
    var index = 2 * ad
    if value > shrink_towards:
        index -= 1
    return index


def zigzag_value(index: UInt128, shrink_towards: Int128) -> Int128:
    var n = Int128((index + 1) // 2)
    if index % 2 == 0:
        n = -n
    return shrink_towards + n


def _effective_shrink_towards(c: Constraints) -> Int128:
    var s = c.shrink_towards
    if c.has_min:
        s = max(c.min_value, s)
    if c.has_max:
        s = min(c.max_value, s)
    return s


def integer_index(value: Int128, c: Constraints) -> UInt128:
    """Port of the integer case of `choice_to_index`."""
    var s = _effective_shrink_towards(c)
    var dist = UInt128(value - s) if value >= s else UInt128(s - value)
    if not c.has_min and not c.has_max:
        return zigzag_index(value, s)
    if c.has_min and not c.has_max:
        if dist <= UInt128(s - c.min_value):
            return zigzag_index(value, s)
        return UInt128(value - c.min_value)
    if c.has_max and not c.has_min:
        if dist <= UInt128(c.max_value - s):
            return zigzag_index(value, s)
        return UInt128(c.max_value - value)
    if UInt128(s - c.min_value) < UInt128(c.max_value - s):
        if dist <= UInt128(s - c.min_value):
            return zigzag_index(value, s)
        return UInt128(value - c.min_value)
    if dist <= UInt128(c.max_value - s):
        return zigzag_index(value, s)
    return UInt128(c.max_value - value)


def integer_from_index(index: UInt128, c: Constraints) -> Int128:
    """Port of the integer case of `choice_from_index`."""
    var s = _effective_shrink_towards(c)
    if not c.has_min and not c.has_max:
        return zigzag_value(index, s)
    if c.has_min and not c.has_max:
        if index <= zigzag_index(c.min_value, s):
            return zigzag_value(index, s)
        return Int128(index) + c.min_value
    if c.has_max and not c.has_min:
        if index <= zigzag_index(c.max_value, s):
            return zigzag_value(index, s)
        return c.max_value - Int128(index)
    if UInt128(s - c.min_value) < UInt128(c.max_value - s):
        if index <= zigzag_index(c.min_value, s):
            return zigzag_value(index, s)
        return Int128(index) + c.min_value
    if index <= zigzag_index(c.max_value, s):
        return zigzag_value(index, s)
    return c.max_value - Int128(index)


def float_index(f: Float64) -> UInt128:
    """`(sign << 64) | float_to_lex(abs(f))`."""
    var sign = UInt128(1) if is_negative(f) else UInt128(0)
    return (sign << 64) | UInt128(float_to_lex(abs(f)))


def float_from_index(index: UInt128, c: Constraints) -> Float64:
    var sign = -1.0 if (index >> 64) != 0 else 1.0
    var result = sign * lex_to_float(UInt64(index & UInt128(UInt64.MAX)))
    return clamp_float(
        result, c.fmin, c.fmax, c.allow_nan, c.smallest_nonzero_magnitude
    )


def element_order(c: Constraints, x: UInt32) -> Int:
    """The shrink-order index of one element of a bytes/string choice."""
    if c.kind == BYTES:
        return Int(x)
    return c.alphabet().index_from_char_in_shrink_order(x)


def element_from_order(c: Constraints, n: Int) -> UInt32:
    if c.kind == BYTES:
        return UInt32(n)
    return c.alphabet().char_in_shrink_order(n)


def simple_index(v: ChoiceValue, c: Constraints) -> UInt128:
    """The index of an integer, float or boolean choice."""
    if v.kind == INTEGER:
        return integer_index(v.i, c)
    if v.kind == FLOAT:
        return float_index(v.f)
    # boolean
    if not (c.p > 5.421010862427522e-20 and c.p < 1 - 5.421010862427522e-20):
        return 0
    return UInt128(v.i)


def choice_compare(
    a: ChoiceValue, ca: Constraints, b: ChoiceValue, cb: Constraints
) -> Int:
    """-1, 0 or 1 as `a` (drawn under `ca`) is simpler than, as simple as, or
    less simple than `b` (drawn under `cb`). Equivalent to comparing
    `choice_to_index` in Hypothesis."""
    if a.kind != b.kind:
        return -1 if a.kind < b.kind else 1
    if a.kind == BYTES or a.kind == STRING:
        if len(a.seq) != len(b.seq):
            return -1 if len(a.seq) < len(b.seq) else 1
        for k in range(len(a.seq)):
            if a.seq[k] == b.seq[k]:
                continue
            var oa = element_order(ca, a.seq[k])
            var ob = element_order(cb, b.seq[k])
            if oa != ob:
                return -1 if oa < ob else 1
        return 0
    var ia = simple_index(a, ca)
    var ib = simple_index(b, cb)
    if ia < ib:
        return -1
    if ia > ib:
        return 1
    return 0


def choice_simplest(c: Constraints) -> ChoiceValue:
    """The choice at index 0."""
    if c.kind == INTEGER:
        return ChoiceValue(integer=_effective_shrink_towards(c))
    if c.kind == FLOAT:
        return ChoiceValue(float=float_from_index(0, c))
    if c.kind == BOOLEAN:
        return ChoiceValue(boolean=c.p >= 1 - 5.421010862427522e-20)
    var zero = element_from_order(c, 0) if c.alphabet_size() > 0 else UInt32(0)
    var s = List[UInt32](length=c.min_size, fill=zero)
    if c.kind == BYTES:
        return ChoiceValue(bytes=s^)
    return ChoiceValue(string=s^)


def choice_from_index(index: UInt128, c: Constraints) raises -> ChoiceValue:
    """Port of `choice_from_index`. Collections are decoded with 128-bit
    arithmetic, which suffices for the small indices used in practice;
    larger ones raise (Hypothesis's `ChoiceTooLarge`)."""
    if c.kind == INTEGER:
        return ChoiceValue(integer=integer_from_index(index, c))
    if c.kind == FLOAT:
        return ChoiceValue(float=float_from_index(index, c))
    if c.kind == BOOLEAN:
        var simplest = choice_simplest(c)
        if index == 0:
            return simplest^
        return ChoiceValue(boolean=True)
    var a = UInt128(c.alphabet_size())
    var idx = index
    if a == 0:
        return choice_simplest(c)
    # skip collections shorter than min_size
    var size = c.min_size
    var count = UInt128(1)
    for _ in range(c.min_size):
        if count > UInt128(1) << 100:
            raise Error("ChoiceTooLarge")
        count *= a
    while idx >= count:
        idx -= count
        size += 1
        if size > 8 * 1024 or count > UInt128(1) << 100:
            raise Error("ChoiceTooLarge")
        count *= a
    var vals = List[UInt32](length=size, fill=0)
    for k in range(size - 1, -1, -1):
        vals[k] = element_from_order(c, Int(idx % a))
        idx //= a
    if c.kind == BYTES:
        return ChoiceValue(bytes=vals^)
    return ChoiceValue(string=vals^)


def choice_permitted(v: ChoiceValue, c: Constraints) -> Bool:
    """Whether `v` could have been drawn under `c`."""
    if v.kind != c.kind:
        return False
    if v.kind == INTEGER:
        if c.has_min and v.i < c.min_value:
            return False
        return not (c.has_max and v.i > c.max_value)
    if v.kind == FLOAT:
        return float_permitted(
            v.f, c.fmin, c.fmax, c.allow_nan, c.smallest_nonzero_magnitude
        )
    if v.kind == BOOLEAN:
        if c.p <= 0:
            return v.i == 0
        if c.p >= 1:
            return v.i != 0
        return True
    if len(v.seq) < c.min_size or len(v.seq) > c.max_size:
        return False
    if v.kind == STRING:
        ref alpha = c.alphabet()
        for x in v.seq:
            if x not in alpha:
                return False
    else:
        for x in v.seq:
            if x > 255:
                return False
    return True


def _bit_length(x: UInt128) -> Int:
    var n = 0
    var y = x
    while y != 0:
        y >>= 1
        n += 1
    return n


def choice_size(v: ChoiceValue) -> Int:
    """The serialized size of one choice (Hypothesis's `choice_size`), used to
    bound the total size of a test case."""
    if v.kind == BOOLEAN:
        return 1
    var size: Int
    if v.kind == FLOAT:
        size = 8
    elif v.kind == INTEGER:
        var mag = UInt128(-v.i) if v.i < 0 else UInt128(v.i)
        size = 1 + _bit_length(mag) // 8
    elif v.kind == BYTES:
        size = len(v.seq)
    else:
        size = 0
        for x in v.seq:
            if x < 0x80:
                size += 1
            elif x < 0x800:
                size += 2
            elif x < 0x10000:
                size += 3
            else:
                size += 4
    if size < 0b11111:
        return 1 + size
    return 1 + max(1, (_bit_length(UInt128(size)) + 6) // 7) + size


def sort_key_less(a: List[ChoiceNode], b: List[ChoiceNode]) -> Bool:
    """Whether node sequence `a` is simpler than `b`: shorter, or the same
    length and lexicographically smaller by choice index (`sort_key`)."""
    if len(a) != len(b):
        return len(a) < len(b)
    for k in range(len(a)):
        var r = choice_compare(
            a[k].value, a[k].constraints, b[k].value, b[k].constraints
        )
        if r != 0:
            return r < 0
    return False
