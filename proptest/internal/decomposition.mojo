# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Unicode decompositions, for the `normalize_unicode_chars` shrink pass.

Hypothesis uses `unicodedata.normalize("NFD"/"NFKD", c)` and `c.casefold()`;
Mojo's standard library has neither, so the components are generated into
`decomposition_data.mojo` by `tools/gen_unicode.mojo`, except for Hangul
syllables, which are decomposed with the algorithm from the Unicode
standard (section 3.12) to keep the table small.
"""

from std.collections import Dict

from proptest.internal.decomposition_data import DECOMPOSITION_DATA

comptime _S_BASE: UInt32 = 0xAC00
comptime _L_BASE: UInt32 = 0x1100
comptime _V_BASE: UInt32 = 0x1161
comptime _T_BASE: UInt32 = 0x11A7
comptime _T_COUNT: UInt32 = 28
comptime _N_COUNT: UInt32 = 588  # V_COUNT * T_COUNT
comptime _S_COUNT: UInt32 = 11172


def _hex(s: StringSlice) -> UInt32:
    var v = UInt32(0)
    for b in s.as_bytes():
        var d = UInt32(b)
        if d >= UInt32(ord("a")):
            d = d - UInt32(ord("a")) + 10
        else:
            d = d - UInt32(ord("0"))
        v = v * 16 + d
    return v


struct Decompositions(Movable):
    """Lookup of the decomposition and casefold components of codepoints.
    Parsing the table takes a few milliseconds, so the shrinker builds one
    only when it meets a non-ASCII character."""

    var table: Dict[UInt32, List[UInt32]]

    def __init__(out self):
        self.table = Dict[UInt32, List[UInt32]]()
        for entry in DECOMPOSITION_DATA.split(" "):
            if entry.byte_length() == 0:
                continue
            var colon = entry.find(":")
            var comps = List[UInt32]()
            for part in entry[byte = colon + 1 :].split(","):
                comps.append(_hex(part))
            self.table[_hex(entry[byte=0:colon])] = comps^

    def components(self, c: UInt32) -> List[UInt32]:
        """The distinct characters (other than `c`) of the NFD and NFKD
        forms and the casefold of `c`."""
        if c >= _S_BASE and c < _S_BASE + _S_COUNT:
            var s = c - _S_BASE
            var out = List[UInt32]()
            out.append(_L_BASE + s // _N_COUNT)
            out.append(_V_BASE + (s % _N_COUNT) // _T_COUNT)
            var t = s % _T_COUNT
            if t != 0:
                out.append(_T_BASE + t)
            return out^
        try:
            if c in self.table:
                return self.table[c].copy()
        except:
            pass
        return List[UInt32]()
