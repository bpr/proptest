# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""A small, seedable pseudo-random number generator.

Hypothesis uses Python's `random.Random` (a Mersenne Twister); proptest uses
xoshiro256** seeded through SplitMix64. Only determinism for a given seed
matters, not bit-compatibility with Hypothesis.
"""

from std.time import perf_counter_ns


@always_inline
def _rotl(x: UInt64, k: UInt64) -> UInt64:
    return (x << k) | (x >> (64 - k))


def splitmix64(mut state: UInt64) -> UInt64:
    """Advances a SplitMix64 state and returns the next output."""
    state += 0x9E3779B97F4A7C15
    var z = state
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ^ (z >> 27)) * 0x94D049BB133111EB
    return z ^ (z >> 31)


struct Random(Copyable):
    """A xoshiro256** generator."""

    var s0: UInt64
    var s1: UInt64
    var s2: UInt64
    var s3: UInt64

    def __init__(out self, seed: UInt64):
        """A generator seeded with `seed`."""
        var st = seed
        self.s0 = splitmix64(st)
        self.s1 = splitmix64(st)
        self.s2 = splitmix64(st)
        self.s3 = splitmix64(st)

    @staticmethod
    def from_time() -> Self:
        """A generator seeded from the clock."""
        return Self(UInt64(perf_counter_ns()))

    def next_u64(mut self) -> UInt64:
        """The next 64 random bits."""
        var result = _rotl(self.s1 * 5, 7) * 9
        var t = self.s1 << 17
        self.s2 ^= self.s0
        self.s3 ^= self.s1
        self.s1 ^= self.s2
        self.s0 ^= self.s3
        self.s2 ^= t
        self.s3 = _rotl(self.s3, 45)
        return result

    def getrandbits(mut self, k: Int) -> UInt64:
        """`k` (0..64) random bits."""
        if k <= 0:
            return 0
        if k >= 64:
            return self.next_u64()
        return self.next_u64() >> UInt64(64 - k)

    def random(mut self) -> Float64:
        """A uniform float in [0, 1)."""
        return Float64(self.next_u64() >> 11) * (1.0 / 9007199254740992.0)

    def below(mut self, n: UInt64) -> UInt64:
        """A uniform integer in [0, n). `n` must be positive."""
        if n == 0:
            return 0
        # Lemire-style rejection to avoid modulo bias.
        var threshold = (0 - n) % n
        while True:
            var r = self.next_u64()
            if r >= threshold:
                return r % n

    def below128(mut self, n: UInt128) -> UInt128:
        """A uniform integer in [0, n) for a 128-bit bound."""
        if n <= UInt128(UInt64.MAX):
            return UInt128(self.below(UInt64(n)))
        var threshold = (0 - n) % n
        while True:
            var r = (UInt128(self.next_u64()) << 64) | UInt128(self.next_u64())
            if r >= threshold:
                return r % n

    def randint(mut self, lo: Int, hi: Int) -> Int:
        """A uniform integer in [lo, hi] (inclusive)."""
        if hi <= lo:
            return lo
        var span = UInt64(Int64(hi) - Int64(lo)) + 1
        if span == 0:  # the full 64-bit range
            return Int(Int64(self.next_u64()))
        return lo + Int(self.below(span))

    def randint128(mut self, lo: Int128, hi: Int128) -> Int128:
        """A uniform integer in [lo, hi] (inclusive) over 128-bit values."""
        if hi <= lo:
            return lo
        var span = UInt128(hi - lo) + 1
        if span == 0:
            return Int128(
                (UInt128(self.next_u64()) << 64) | UInt128(self.next_u64())
            )
        return lo + Int128(self.below128(span))

    def coin(mut self, p: Float64) -> Bool:
        """True with probability `p`."""
        if p <= 0:
            return False
        if p >= 1:
            return True
        return self.random() < p
