# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Random generation of choices.

Port of `HypothesisProvider` from `hypothesis.internal.conjecture.providers`
and the integer distribution from `hypothesis.internal.statistics`.

Generation deliberately over-weights "nasty" values: a few percent of
draws return a constant from a pool of edge cases (large powers of two,
`float_info.max`, subnormals, tricky strings, ...), floats near bounds,
infinities and NaN, and integers follow a heavy-tailed distribution that
is uniform on [-256, 256] and log-Student-t outside it.
"""

from std.memory import ArcPointer
from std.math import (
    sqrt,
    log2,
    expm1,
    copysign,
    isnan,
    isinf,
    log,
)

from proptest.internal.choice import (
    ChoiceValue,
    Constraints,
    INTEGER,
    FLOAT,
    BOOLEAN,
    BYTES,
    STRING,
    choice_permitted,
)
from proptest.internal.floats import (
    lex_to_float,
    clamp_float,
    float_to_int,
    next_up,
    next_down,
    pos_inf,
    neg_inf,
    float_nan,
    signaling_nan,
    smallest_subnormal,
    FLOAT_MAX,
    FLOAT_MIN_NORMAL,
)
from proptest.internal.intervals import IntervalSet, string_to_codepoints
from proptest.internal.random import Random


# ===----------------------------------------------------------------------=== #
# Integer distribution
# ===----------------------------------------------------------------------=== #

comptime _LN2 = 0.6931471805599453
comptime _SCALE_BITS = 13.0
comptime _HALF_WIDTH = 256.0
comptime _SWITCHOVER = 256.0
comptime _T2_COEF = 0.3535533905932738  # 1 / (2 * sqrt(2))


def _stdtr2(t: Float64) -> Float64:
    """CDF of Student's t with 2 degrees of freedom (closed form)."""
    return 0.5 + t / (2.0 * sqrt(2.0 + t * t))


def _stdtrit2(u: Float64) -> Float64:
    """Inverse CDF of Student's t with 2 degrees of freedom."""
    return (2.0 * u - 1.0) / sqrt(2.0 * u * (1.0 - u))


def _uniform_cdf(x: Float64) -> Float64:
    if x < -_HALF_WIDTH:
        return 0.0
    if x > _HALF_WIDTH:
        return 1.0
    return (x + _HALF_WIDTH) / (2 * _HALF_WIDTH)


def _uniform_inverse_cdf(u: Float64) -> Float64:
    return -_HALF_WIDTH + 2 * _HALF_WIDTH * u


def _uniform_pdf(x: Float64) -> Float64:
    if -_HALF_WIDTH <= x and x <= _HALF_WIDTH:
        return 1 / (2 * _HALF_WIDTH)
    return 0.0


def _lst_cdf(x: Float64) -> Float64:
    var y = copysign(log2(1 + abs(x)), x) / _SCALE_BITS
    return _stdtr2(y)


def _lst_inverse_cdf(u: Float64) -> Float64:
    var y = _SCALE_BITS * _stdtrit2(u)
    y = max(-1023.0, min(y, 1023.0))
    return copysign(expm1(abs(y) * _LN2), y)


def _lst_pdf(x: Float64) -> Float64:
    var y = copysign(log2(1 + abs(x)), x) / _SCALE_BITS
    var base = 1 + y * y / 2.0
    var f_t = _T2_COEF / (base * sqrt(base))
    return f_t / (_SCALE_BITS * (1 + abs(x)) * _LN2)


struct IntegerDistribution(Copyable):
    """`PiecewiseDistribution(inner=Uniform(256), outer=LogStudentT(13, 2),
    switchover=256)`."""

    var inner_g_neg: Float64
    var inner_g_pos: Float64
    var outer_g_neg: Float64
    var outer_g_pos: Float64
    var alpha: Float64
    var beta: Float64
    var inner_mass: Float64
    var left_mass: Float64

    def __init__(out self):
        self.inner_g_neg = _uniform_cdf(-_SWITCHOVER)
        self.inner_g_pos = _uniform_cdf(_SWITCHOVER)
        self.outer_g_neg = _lst_cdf(-_SWITCHOVER)
        self.outer_g_pos = _lst_cdf(_SWITCHOVER)
        var outer_outer_mass = 1 - (self.outer_g_pos - self.outer_g_neg)
        var inner_inner_mass = self.inner_g_pos - self.inner_g_neg
        var inner_pdf = _uniform_pdf(_SWITCHOVER)
        var outer_pdf = _lst_pdf(_SWITCHOVER)
        self.alpha = 1 / (
            outer_pdf * inner_inner_mass / inner_pdf + outer_outer_mass
        )
        self.beta = self.alpha * outer_pdf / inner_pdf
        self.inner_mass = self.beta * inner_inner_mass
        self.left_mass = self.alpha * self.outer_g_neg

    def cdf(self, x: Float64) -> Float64:
        if x <= -_SWITCHOVER:
            return self.alpha * _lst_cdf(x)
        if x < _SWITCHOVER:
            return self.left_mass + self.beta * (
                _uniform_cdf(x) - self.inner_g_neg
            )
        return (
            self.left_mass
            + self.inner_mass
            + self.alpha * (_lst_cdf(x) - self.outer_g_pos)
        )

    def inverse_cdf(self, u: Float64) -> Float64:
        if u <= self.left_mass:
            return _lst_inverse_cdf(u / self.alpha)
        if u < self.left_mass + self.inner_mass:
            var target = self.inner_g_neg + (u - self.left_mass) / self.beta
            return _uniform_inverse_cdf(target)
        return _lst_inverse_cdf(
            (u - self.left_mass - self.inner_mass) / self.alpha
            + self.outer_g_pos
        )


# ===----------------------------------------------------------------------=== #
# Constants
# ===----------------------------------------------------------------------=== #


struct Constants(Movable):
    """Pools of "nasty" values that generation occasionally returns."""

    var integers: List[Int128]
    var floats: List[Float64]
    var strings: List[List[UInt32]]

    def __init__(out self):
        var base = List[Int128]()
        for n in range(16, 66):
            base.append(Int128(1) << Int128(n))
        var p10 = Int128(1)
        for n in range(20):
            if n >= 5:
                base.append(p10)
            p10 *= 10
        var fact = Int128(1)
        for n in range(1, 21):
            fact *= Int128(n)
            if n >= 9:
                base.append(fact)
        base.append(510510)
        base.append(6469693230)
        base.append(304250263527210)
        base.append(Int128(3258915847719004473) * 10)  # 32589158477190044730
        var ints = List[Int128]()
        for x in base:
            ints.append(x)
            ints.append(x - 1)
            ints.append(x + 1)
        var n = len(ints)
        for k in range(n):
            ints.append(-ints[k])
        self.integers = ints^

        var fl: List[Float64] = [
            0.5,
            1.1,
            1.5,
            1.9,
            1.0 / 3,
            10e6,
            10e-6,
            1.175494351e-38,
            smallest_subnormal(),
            FLOAT_MIN_NORMAL,
            FLOAT_MAX,
            3.402823466e38,
            9007199254740992.0,
            1 - 10e-6,
            2 + 10e-6,
            1.192092896e-07,
            2.2204460492503131e-016,
            5.960464477539063e-08,  # 2**-24
            6.103515625e-05,  # 2**-14
            1.401298464324817e-45,  # 2**-149
            1.1754943508222875e-38,  # 2**-126
            FLOAT_MIN_NORMAL / 2,
            FLOAT_MIN_NORMAL / 10,
            FLOAT_MIN_NORMAL / 1000,
            FLOAT_MIN_NORMAL / 100_000,
        ]
        var m = len(fl)
        for k in range(m):
            fl.append(-fl[k])
        self.floats = fl^

        var strs: List[String] = [
            "undefined",
            "null",
            "NULL",
            "nil",
            "NIL",
            "true",
            "false",
            "True",
            "False",
            "TRUE",
            "FALSE",
            "None",
            "none",
            "if",
            "then",
            "else",
            "__dict__",
            "__proto__",
            "0",
            "1e100",
            "0..0",
            "0/0",
            "1/0",
            "+0.0",
            "Infinity",
            "-Infinity",
            "Inf",
            "INF",
            "NaN",
            "999999999999999999999999999999",
            ",./;'[]\\-=<>?:\"{}|_+!@#$%^&*()`~",
            "Ω≈ç√∫˜µ≤≥÷åß∂ƒ©˙∆˚¬…æœ∑´®†¥¨ˆøπ“‘¡™£¢∞§¶•ªº–≠¸˛Ç◊ı˜Â¯˘¿ÅÍÎÏ˝ÓÔÒÚÆ☃Œ„´‰ˇÁ¨ˆØ∏”’`⁄€‹›ﬁﬂ‡°·‚—±",
            "Ⱥ",
            "Ⱦ",
            "æœÆŒﬀʤʨß",
            "(╯°□°）╯︵ ┻━┻)",
            "😍",
            "🇺🇸",
            "🏻",
            "👍🏻",
            "الكل في المجمو عة",
            "᚛ᚄᚓᚐᚋᚒᚄ ᚑᚄᚂᚑᚏᚅ᚜",
            "กา",
            "𝐓𝐡𝐞 𝐪𝐮𝐢𝐜𝐤 𝐛𝐫𝐨𝐰𝐧 𝐟𝐨𝐱",
            "ʇǝɯɐ ʇᴉs ɹolop ɯnsdᴉ ɯǝɹo˥",
            "NUL",
            "COM1",
            "LPT1",
            "Scunthorpe",
            "Ṱ̺̺̕o͞ ̷i̲̬͇̪͙n̝̗͕v̟̜̘̦͟o̶̙̰̠kè͚̮̺̪̹̱̤",
            "मनीष منش",
            "lorem لا بسم الله ipsum 你好1234你好",
            "a\nb\rc\u0085d\u000be\u000cf g h\r\ni",
        ]
        self.strings = List[List[UInt32]]()
        for s in strs:
            self.strings.append(string_to_codepoints(s))


# ===----------------------------------------------------------------------=== #
# Collection sizes
# ===----------------------------------------------------------------------=== #


def _p_continue_to_avg(p_continue: Float64, max_size: Float64) -> Float64:
    if p_continue >= 1:
        return max_size
    return (1.0 / (1 - p_continue) - 1) * (1 - p_continue**max_size)


def calc_p_continue(desired_avg: Float64, max_size: Float64) -> Float64:
    """The continuation probability that gives collections the desired
    average size (port of `_calc_p_continue`)."""
    if desired_avg >= max_size:
        return 1.0
    var p_continue = 1 - 1.0 / (1 + desired_avg)
    if p_continue == 0 or isinf(max_size) or max_size > 1e15:
        return p_continue
    while _p_continue_to_avg(p_continue, max_size) > desired_avg:
        p_continue -= 0.0001
        if p_continue < smallest_subnormal():
            p_continue = smallest_subnormal()
            break
    var hi = 1.0
    while desired_avg - _p_continue_to_avg(p_continue, max_size) > 0.01:
        var mid = (p_continue + hi) / 2
        if _p_continue_to_avg(mid, max_size) <= desired_avg:
            p_continue = mid
        else:
            hi = mid
    return p_continue


def average_size(min_size: Int, max_size: Int) -> Float64:
    """Hypothesis's default average collection size."""
    return min(
        max(Float64(min_size) * 2, Float64(min_size) + 5),
        0.5 * (Float64(min_size) + Float64(max_size)),
    )


# ===----------------------------------------------------------------------=== #
# The provider
# ===----------------------------------------------------------------------=== #


struct Provider(Movable):
    """Draws random choices (port of `HypothesisProvider`)."""

    var random: Random
    var constants: ArcPointer[Constants]
    var dist: IntegerDistribution

    def __init__(
        out self, var random: Random, constants: ArcPointer[Constants]
    ):
        self.random = random^
        self.constants = constants
        self.dist = IntegerDistribution()

    def draw(mut self, c: Constraints) -> ChoiceValue:
        if c.kind == INTEGER:
            return ChoiceValue(integer=self.draw_integer(c))
        if c.kind == FLOAT:
            return ChoiceValue(float=self.draw_float(c))
        if c.kind == BOOLEAN:
            return ChoiceValue(boolean=self.random.coin(c.p))
        if c.kind == BYTES:
            return ChoiceValue(bytes=self.draw_bytes(c))
        return ChoiceValue(string=self.draw_string(c))

    def _maybe_constant_index(mut self, c: Constraints, p: Float64) -> Int:
        """With probability `p`, the index of a random permitted constant for
        `c` in its pool (-1 if none or not chosen)."""
        if self.random.random() > p:
            return -1
        var permitted = List[Int]()
        ref k = self.constants[]
        if c.kind == INTEGER:
            for i in range(len(k.integers)):
                if choice_permitted(ChoiceValue(integer=k.integers[i]), c):
                    permitted.append(i)
        elif c.kind == FLOAT:
            for i in range(len(k.floats)):
                if choice_permitted(ChoiceValue(float=k.floats[i]), c):
                    permitted.append(i)
        elif c.kind == STRING:
            for i in range(len(k.strings)):
                if choice_permitted(ChoiceValue(string=k.strings[i].copy()), c):
                    permitted.append(i)
        if len(permitted) == 0:
            return -1
        return permitted[Int(self.random.below(UInt64(len(permitted))))]

    def draw_integer(mut self, c: Constraints) -> Int128:
        if c.weights:
            ref w = c.weights.value()[]
            var r = self.random.random()
            for i in range(len(w) - 1):
                r -= w[i]
                if r < 0:
                    return c.min_value + Int128(i)
            return c.min_value + Int128(len(w) - 1)
        var ci = self._maybe_constant_index(c, 0.05)
        if ci >= 0:
            return self.constants[].integers[ci]
        var lo: Int128
        var hi: Int128
        comptime BIG = Int128(1) << 126
        if not c.has_min and not c.has_max:
            lo = -BIG
            hi = BIG
        elif not c.has_min:
            hi = c.max_value
            lo = -BIG
            if hi < -(BIG // 2):
                lo = hi * 2 if hi > Int128.MIN // 2 else Int128.MIN + 1
        elif not c.has_max:
            lo = c.min_value
            hi = BIG
            if lo > BIG // 2:
                hi = lo * 2 if lo < Int128.MAX // 2 else Int128.MAX
        else:
            lo = c.min_value
            hi = c.max_value
        var cdf_lo = self.dist.cdf(Float64(lo) - 0.5)
        var cdf_hi = self.dist.cdf(Float64(hi) + 0.5)
        if cdf_hi - cdf_lo >= 1e-13:
            var p: Float64
            while True:
                p = cdf_lo + self.random.random() * (cdf_hi - cdf_lo)
                if p > 0 and p < 1:
                    break
            var x = self.dist.inverse_cdf(p)
            var r = x.__round__()
            # clamp before converting so huge floats can't overflow Int128
            if r <= Float64(lo):
                return lo
            if r >= Float64(hi):
                return hi
            var n = Int128(r)
            return max(lo, min(n, hi))
        return self.random.randint128(lo, hi)

    def draw_float(mut self, c: Constraints) -> Float64:
        var ci = self._maybe_constant_index(c, 0.15)
        if ci >= 0:
            return self.constants[].floats[ci]
        var weird: List[Float64] = [
            0.0,
            -0.0,
            pos_inf(),
            neg_inf(),
            float_nan(),
            -float_nan(),
            signaling_nan(),
            -signaling_nan(),
            c.fmin,
            next_up(c.fmin),
            c.fmin + 1,
            c.fmax - 1,
            next_down(c.fmax),
            c.fmax,
        ]
        var permitted = List[Float64]()
        for f in weird:
            if choice_permitted(ChoiceValue(float=f), c):
                permitted.append(f)
        if len(permitted) > 0 and self.random.random() < 0.05:
            return permitted[Int(self.random.below(UInt64(len(permitted))))]
        var result = lex_to_float(self.random.next_u64())
        if self.random.getrandbits(1) == 0:
            result = -result
        if c.allow_nan and isnan(result):
            return result
        var clamped = clamp_float(
            result, c.fmin, c.fmax, c.allow_nan, c.smallest_nonzero_magnitude
        )
        return clamped

    def _draw_size(mut self, min_size: Int, max_size: Int) -> Int:
        """A collection size, drawn as `many()` would: forced continuation up
        to `min_size`, then geometric with the default average size."""
        if min_size == max_size:
            return min_size
        var p = calc_p_continue(
            average_size(min_size, max_size) - Float64(min_size),
            Float64(max_size - min_size),
        )
        var count = min_size
        while count < max_size and self.random.coin(p):
            count += 1
        return count

    def draw_string(mut self, c: Constraints) -> List[UInt32]:
        ref alpha = c.alphabet()
        var n = len(alpha)
        if n == 0:
            return List[UInt32]()
        var ci = self._maybe_constant_index(c, 0.05)
        if ci >= 0:
            return self.constants[].strings[ci].copy()
        var size = self._draw_size(c.min_size, c.max_size)
        var out = List[UInt32](capacity=size)
        for _ in range(size):
            var i: Int
            if n > 256:
                if self.random.coin(0.2):
                    i = 256 + Int(self.random.below(UInt64(n - 256)))
                else:
                    i = Int(self.random.below(256))
            else:
                i = Int(self.random.below(UInt64(n)))
            out.append(alpha.char_in_shrink_order(i))
        return out^

    def draw_bytes(mut self, c: Constraints) -> List[UInt32]:
        var size = self._draw_size(c.min_size, c.max_size)
        var out = List[UInt32](capacity=size)
        for _ in range(size):
            out.append(UInt32(self.random.below(256)))
        return out^
