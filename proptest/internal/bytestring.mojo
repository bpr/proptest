# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Choices read from a byte string, for `fuzz_one_input`.

Port of Hypothesis's `BytestringProvider`: each choice takes the next few
bytes of the input, so a fuzzer's byte-level mutations become changes to
the choices. Integers take just enough bits to span their range (redrawing
when the bits land above it), booleans one byte, floats 65 bits (a sign
and a lex-encoded magnitude, then clamped into range), and strings and
byte strings a continue byte before each optional element. Weights and the
provider's special values are ignored, as in Hypothesis.

`encode_choices` is the inverse: it writes the bytes that decode to a
given choice sequence. Hypothesis returns its database encoding from
`fuzz_one_input` instead, which a later call can't replay.
"""

from std.math import floor

from proptest.internal.choice import (
    ChoiceValue,
    ChoiceNode,
    Constraints,
    INTEGER,
    FLOAT,
    BOOLEAN,
    BYTES,
    STRING,
)
from proptest.internal.floats import (
    lex_to_float,
    float_to_lex,
    clamp_float,
    float_to_int,
    int_to_float,
    is_negative,
)
from proptest.internal.provider import calc_p_continue, average_size

comptime _UNBOUNDED_MIN = Int128.MIN
comptime _UNBOUNDED_MAX = Int128.MAX
comptime _HALF_BOUNDED_SPAN = Int128(1) << 64


def _bit_length(x: UInt128) -> Int:
    var n = 0
    var v = x
    while v != 0:
        v >>= 1
        n += 1
    return n


def _integer_range(c: Constraints) -> Tuple[Int128, Int128]:
    """The range an integer choice is read from: Hypothesis's, with a
    half-bounded range extending 2**64 past its bound."""
    if not c.has_min and not c.has_max:
        return (_UNBOUNDED_MIN, _UNBOUNDED_MAX)
    if not c.has_min:
        var hi = c.max_value
        var lo = (
            hi - _HALF_BOUNDED_SPAN if hi
            >= _UNBOUNDED_MIN + _HALF_BOUNDED_SPAN else _UNBOUNDED_MIN
        )
        return (lo, hi)
    if not c.has_max:
        var lo = c.min_value
        var hi = (
            lo + _HALF_BOUNDED_SPAN if lo
            <= _UNBOUNDED_MAX - _HALF_BOUNDED_SPAN else _UNBOUNDED_MAX
        )
        return (lo, hi)
    return (c.min_value, c.max_value)


def _boolean_threshold(p: Float64) -> Int:
    """A boolean read from byte `n` is true when `n >= threshold`."""
    var falsey = Int(floor(256.0 * (1 - p)))
    return min(max(falsey, 1), 255)


def _p_continue(c: Constraints) -> Float64:
    return calc_p_continue(
        average_size(c.min_size, c.max_size) - Float64(c.min_size),
        Float64(c.max_size - c.min_size),
    )


def _alphabet_size(c: Constraints) -> Int:
    if c.kind == BYTES:
        return 256
    return len(c.intervals.value()[])


struct ByteReader(Movable):
    """Reads choices from a byte string (Hypothesis's `BytestringProvider`).
    Each read returns None once the bytes run out (an overrun)."""

    var bytes: List[UInt8]
    var pos: Int

    def __init__(out self, var bytes: List[UInt8]):
        self.bytes = bytes^
        self.pos = 0

    def _bits(mut self, n: Int) -> Optional[UInt128]:
        """The next `n` bits (`n <= 128`), big-endian, from whole bytes."""
        if n == 0:
            return UInt128(0)
        var n_bytes = (n + 7) // 8
        if self.pos + n_bytes > len(self.bytes):
            return None
        var v = UInt128(0)
        for k in range(n_bytes):
            var b = self.bytes[self.pos + k]
            if k == 0 and n % 8 != 0:
                b &= UInt8((1 << (n % 8)) - 1)
            v = (v << 8) | UInt128(b)
        self.pos += n_bytes
        return v

    def _boolean(mut self, p: Float64) -> Optional[Bool]:
        if p <= 0:
            return False
        if p >= 1:
            return True
        var n = self._bits(8)
        if not n:
            return None
        return Int(n.value()) >= _boolean_threshold(p)

    def _integer(mut self, c: Constraints) -> Optional[Int128]:
        var r = _integer_range(c)
        var lo = r[0]
        var span = UInt128(r[1]) - UInt128(lo)
        if span == 0:
            return lo
        var bits = _bit_length(span)
        while True:
            var v = self._bits(bits)
            if not v:
                return None
            if v.value() <= span:
                return Int128(UInt128(lo) + v.value())

    def _float(mut self, c: Constraints) -> Optional[Float64]:
        var n = self._bits(65)
        if not n:
            return None
        var f = lex_to_float(UInt64(n.value() & UInt128(UInt64.MAX)))
        if (n.value() >> 64) != 0:
            f = -f
        return clamp_float(
            f, c.fmin, c.fmax, c.allow_nan, c.smallest_nonzero_magnitude
        )

    def _sequence(mut self, c: Constraints) -> Optional[List[UInt32]]:
        var out = List[UInt32]()
        var alphabet = _alphabet_size(c)
        if alphabet == 0:
            return out^
        var p = _p_continue(c)
        var element = Constraints.integer(Int128(0), Int128(alphabet - 1))
        while True:
            if len(out) >= c.max_size:
                break
            if len(out) >= c.min_size and c.min_size != c.max_size:
                var more = self._boolean(p)
                if not more:
                    return None
                if not more.value():
                    break
            var i = self._integer(element)
            if not i:
                return None
            if c.kind == BYTES:
                out.append(UInt32(i.value()))
            else:
                out.append(c.intervals.value()[][Int(i.value())])
        return out^

    def draw(mut self, c: Constraints) -> Optional[ChoiceValue]:
        """The next choice under `c`, or None if the bytes ran out."""
        if c.kind == INTEGER:
            var v = self._integer(c)
            return ChoiceValue(integer=v.value()) if v else None
        elif c.kind == FLOAT:
            var v = self._float(c)
            return ChoiceValue(float=v.value()) if v else None
        elif c.kind == BOOLEAN:
            var v = self._boolean(c.p)
            return ChoiceValue(boolean=v.value()) if v else None
        var s = self._sequence(c)
        if not s:
            return None
        if c.kind == BYTES:
            return ChoiceValue(bytes=s.take())
        return ChoiceValue(string=s.take())


def _put_bits(mut out: List[UInt8], v: UInt128, n: Int):
    if n == 0:
        return
    var n_bytes = (n + 7) // 8
    for k in range(n_bytes - 1, -1, -1):
        out.append(UInt8((v >> UInt128(8 * k)) & 0xFF))


def _put_boolean(mut out: List[UInt8], value: Bool, p: Float64):
    if p <= 0 or p >= 1:
        return
    out.append(UInt8(0xFF) if value else UInt8(0))


def _put_integer(mut out: List[UInt8], value: Int128, c: Constraints):
    var r = _integer_range(c)
    var span = UInt128(r[1]) - UInt128(r[0])
    if span == 0:
        return
    _put_bits(out, UInt128(value) - UInt128(r[0]), _bit_length(span))


def _put_float(mut out: List[UInt8], value: Float64):
    var lex = UInt128(
        float_to_lex(int_to_float(float_to_int(value) & ~(UInt64(1) << 63)))
    )
    if is_negative(value):
        lex |= UInt128(1) << 64
    _put_bits(out, lex, 65)


def _put_sequence(mut out: List[UInt8], seq: List[UInt32], c: Constraints):
    var alphabet = _alphabet_size(c)
    if alphabet == 0:
        return
    var p = _p_continue(c)
    var element = Constraints.integer(Int128(0), Int128(alphabet - 1))
    for k in range(len(seq) + 1):
        if k >= c.max_size:
            break
        if k >= c.min_size and c.min_size != c.max_size:
            _put_boolean(out, k < len(seq), p)
        if k == len(seq):
            break
        var i = Int(seq[k]) if c.kind == BYTES else c.intervals.value()[].index(
            seq[k]
        )
        _put_integer(out, Int128(i), element)


def encode_choices(nodes: List[ChoiceNode]) -> List[UInt8]:
    """The bytes that `ByteReader` decodes to these choices (forced choices
    take no bytes)."""
    var out = List[UInt8]()
    for node in nodes:
        if node.was_forced:
            continue
        ref c = node.constraints
        ref v = node.value
        if c.kind == INTEGER:
            _put_integer(out, v.i, c)
        elif c.kind == FLOAT:
            _put_float(out, v.f)
        elif c.kind == BOOLEAN:
            _put_boolean(out, v.i != 0, c.p)
        else:
            _put_sequence(out, v.seq, c)
    return out^
