# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Float utilities and the lexicographic float encoding.

Port of `hypothesis.internal.floats` and `hypothesis.internal.conjecture.floats`.

The lex encoding maps non-negative floats to 64-bit integers such that
"simpler" floats have smaller encodings: integers come first (ordered by
value), then numbers with fractional parts ordered so that the ones with
lower denominators are simpler, then infinity, then NaN. See the module
docstring of Hypothesis's `conjecture/floats.py` for the full description.
"""

from std.math import inf, nan, isnan, isinf, copysign, floor


comptime MAX_EXPONENT = 0x7FF
comptime BIAS = 1023
comptime MANTISSA_MASK: UInt64 = (UInt64(1) << 52) - 1
comptime MAX_PRECISE_INTEGER: Float64 = 9007199254740992.0  # 2**53
comptime FLOAT_MAX: Float64 = 1.7976931348623157e308
comptime FLOAT_MIN_NORMAL: Float64 = 2.2250738585072014e-308


@always_inline
def float_to_int(f: Float64) -> UInt64:
    """The IEEE-754 bit pattern of `f`."""
    return UInt64(f.to_bits())


@always_inline
def int_to_float(i: UInt64) -> Float64:
    """The float with bit pattern `i`."""
    return Float64(from_bits=i)


@always_inline
def pos_inf() -> Float64:
    return inf[DType.float64]()


@always_inline
def neg_inf() -> Float64:
    return -inf[DType.float64]()


@always_inline
def float_nan() -> Float64:
    return nan[DType.float64]()


def smallest_subnormal() -> Float64:
    """The smallest positive float, `next_up(0.0)`."""
    return int_to_float(1)


def signaling_nan() -> Float64:
    """A NaN with a non-zero payload beyond the quiet bit."""
    return int_to_float(0x7FF8_0000_0000_0001)


def is_negative(f: Float64) -> Bool:
    """Whether the sign bit of `f` is set (true for -0.0 and negative NaNs)."""
    return (float_to_int(f) >> 63) != 0


def next_up(f: Float64) -> Float64:
    """The next float above `f` (as `math.nextafter(f, inf)`)."""
    if isnan(f) or (isinf(f) and f > 0):
        return f
    if f == 0.0:
        return smallest_subnormal()
    var n = float_to_int(f)
    if f > 0:
        return int_to_float(n + 1)
    return int_to_float(n - 1)


def next_down(f: Float64) -> Float64:
    """The next float below `f`."""
    return -next_up(-f)


def sign_aware_lte(x: Float64, y: Float64) -> Bool:
    """Less-than-or-equals, but strictly orders -0.0 before 0.0."""
    if x == 0.0 and y == 0.0:
        return copysign(1.0, x) <= copysign(1.0, y)
    return x <= y


def float_key(f: Float64) -> UInt64:
    """A key under which two floats are equal iff they are bitwise equal,
    with all NaNs of the same sign and payload identified."""
    return float_to_int(f)


# ===----------------------------------------------------------------------=== #
# Lexicographic encoding
# ===----------------------------------------------------------------------=== #


def _decode_exponent(e: Int) -> Int:
    """Lex exponent -> IEEE exponent (ENCODING_TABLE[e])."""
    # Inline closed form of the table above.
    if e < MAX_EXPONENT - BIAS:  # 0..1023: positive unbiased exponents
        return BIAS + e
    if e < MAX_EXPONENT:  # then negative unbiased exponents, decreasing
        return BIAS - 1 - (e - (MAX_EXPONENT - BIAS))
    return MAX_EXPONENT


def _encode_exponent(e: Int) -> Int:
    """IEEE exponent -> lex exponent (DECODING_TABLE[e])."""
    if e == MAX_EXPONENT:
        return MAX_EXPONENT
    if e >= BIAS:
        return e - BIAS
    return (MAX_EXPONENT - BIAS) + (BIAS - 1 - e)


def _reverse64(v: UInt64) -> UInt64:
    var x = v
    var r: UInt64 = 0
    for _ in range(64):
        r = (r << 1) | (x & 1)
        x >>= 1
    return r


def _reverse_bits(x: UInt64, n: Int) -> UInt64:
    return _reverse64(x) >> UInt64(64 - n)


def _update_mantissa(unbiased_exponent: Int, mantissa: UInt64) -> UInt64:
    var m = mantissa
    if unbiased_exponent <= 0:
        m = _reverse_bits(m, 52)
    elif unbiased_exponent <= 51:
        var n_fractional_bits = 52 - unbiased_exponent
        var fractional_part = m & ((UInt64(1) << UInt64(n_fractional_bits)) - 1)
        m ^= fractional_part
        m |= _reverse_bits(fractional_part, n_fractional_bits)
    return m


def lex_to_float(i: UInt64) -> Float64:
    """Decode a lex-encoded non-negative float."""
    var has_fractional_part = i >> 63
    if has_fractional_part != 0:
        var exponent = Int((i >> 52) & ((UInt64(1) << 11) - 1))
        exponent = _decode_exponent(exponent)
        var mantissa = i & MANTISSA_MASK
        mantissa = _update_mantissa(exponent - BIAS, mantissa)
        return int_to_float((UInt64(exponent) << 52) | mantissa)
    var integral_part = i & ((UInt64(1) << 56) - 1)
    return Float64(integral_part)


def is_simple_float(f: Float64) -> Bool:
    """Whether `f` is a non-negative integer of at most 56 bits."""
    if isnan(f) or isinf(f):
        return False
    if floor(f) != f:
        return False
    if f < 0:
        return False
    return f < 72057594037927936.0  # 2**56


def base_float_to_lex(f: Float64) -> UInt64:
    var i = float_to_int(f)
    i &= (UInt64(1) << 63) - 1
    var exponent = Int(i >> 52)
    var mantissa = i & MANTISSA_MASK
    mantissa = _update_mantissa(exponent - BIAS, mantissa)
    var enc = UInt64(_encode_exponent(exponent))
    return (UInt64(1) << 63) | (enc << 52) | mantissa


def float_to_lex(f: Float64) -> UInt64:
    """Encode a non-negative float so that simpler floats sort first."""
    if is_simple_float(f):
        return UInt64(f)
    return base_float_to_lex(f)


# ===----------------------------------------------------------------------=== #
# Clamping
# ===----------------------------------------------------------------------=== #


def float_permitted(
    f: Float64,
    min_value: Float64,
    max_value: Float64,
    allow_nan: Bool,
    smallest_nonzero_magnitude: Float64,
) -> Bool:
    """Whether `f` satisfies the float choice constraints."""
    if isnan(f):
        return allow_nan
    if abs(f) > 0 and abs(f) < smallest_nonzero_magnitude:
        return False
    return sign_aware_lte(min_value, f) and sign_aware_lte(f, max_value)


def clamp_float(
    f: Float64,
    min_value: Float64,
    max_value: Float64,
    allow_nan: Bool,
    smallest_nonzero_magnitude: Float64,
) -> Float64:
    """Port of `make_float_clamper`: maps an arbitrary float into the
    permitted range, deterministically, using its mantissa bits."""
    if float_permitted(
        f, min_value, max_value, allow_nan, smallest_nonzero_magnitude
    ):
        return f
    var range_size = min(max_value - min_value, FLOAT_MAX)
    var mant = float_to_int(abs(f)) & MANTISSA_MASK
    var g = min_value + range_size * (Float64(mant) / Float64(MANTISSA_MASK))
    if abs(g) > 0 and abs(g) < smallest_nonzero_magnitude:
        g = smallest_nonzero_magnitude
        if smallest_nonzero_magnitude > max_value:
            g *= -1
    if g < min_value:
        g = min_value
    if g > max_value:
        g = max_value
    return g
