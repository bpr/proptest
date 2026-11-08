# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Generate proptest's Unicode tables from the Unicode Character Database.

    pixi run gen-unicode

downloads `UnicodeData.txt` and `CaseFolding.txt` for the version pinned in
pixi.toml into `build/ucd/`, then runs

    mojo run tools/gen_unicode.mojo build/ucd

which writes

- `proptest/internal/charmap_data.mojo`: the codepoint ranges of every
  general category. This plays the role of Hypothesis's
  `hypothesis/internal/charmap.py`, which builds the same table from
  Python's `unicodedata` at run time; Mojo's standard library has no
  Unicode category data, so the table is generated and checked in.
- `proptest/internal/decomposition_data.mojo`: for each codepoint, the
  distinct characters of its NFD and NFKD forms and of its full case
  folding, for the shrinker's `normalize_unicode_chars` pass (Hypothesis's
  `_natural_simpler_chars`). Hangul syllables are left out: they decompose
  algorithmically at run time.

The task then runs `mojo format` on both files.
"""

from std.collections import Dict
from std.sys import argv

comptime MAX_CODEPOINT = 0x10FFFF
comptime HANGUL_S_BASE = 0xAC00
comptime HANGUL_S_COUNT = 11172
comptime HANGUL_L_BASE = 0x1100
comptime HANGUL_V_BASE = 0x1161
comptime HANGUL_T_BASE = 0x11A7
comptime HANGUL_T_COUNT = 28
comptime HANGUL_N_COUNT = 588  # V count (21) * T count

comptime HEADER = (
    "# ===----------------------------------------------------------------------=== #\n"
    "# proptest: property-based testing for Mojo.\n"
    "# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis)."
    " MIT License; see LICENSE.\n"
    "# ===----------------------------------------------------------------------=== #\n"
)


def _hex(x: Int) -> String:
    return hex(x, prefix="")


struct Ucd(Movable):
    """The parts of the Unicode Character Database the tables need."""

    var version: String
    var category_names: List[String]
    var category: List[UInt8]
    """Index into `category_names` for every codepoint (unlisted: Cn)."""
    var ccc: List[UInt8]
    """Canonical combining class of every codepoint."""
    var decomposition: Dict[Int, List[Int]]
    """The one-step decomposition mapping of each codepoint that has one."""
    var is_compat: Dict[Int, Bool]
    """Whether that mapping is a compatibility (`<tag>`) one."""
    var folding: Dict[Int, List[Int]]
    """Full case folding (statuses C and F)."""

    def __init__(out self, dir: String) raises:
        self.version = String()
        self.category_names = List[String]()
        self.category_names.append("Cn")
        self.category = List[UInt8](length=MAX_CODEPOINT + 1, fill=0)
        self.ccc = List[UInt8](length=MAX_CODEPOINT + 1, fill=0)
        self.decomposition = Dict[Int, List[Int]]()
        self.is_compat = Dict[Int, Bool]()
        self.folding = Dict[Int, List[Int]]()
        self._read_unicode_data(dir + "/UnicodeData.txt")
        self._read_case_folding(dir + "/CaseFolding.txt")

    def _category_index(mut self, name: String) -> UInt8:
        for i in range(len(self.category_names)):
            if self.category_names[i] == name:
                return UInt8(i)
        self.category_names.append(name)
        return UInt8(len(self.category_names) - 1)

    def _read_unicode_data(mut self, path: String) raises:
        var text: String
        with open(path, "r") as f:
            text = f.read()
        var range_start = -1
        for line in text.split("\n"):
            if line.byte_length() == 0:
                continue
            var fields = line.split(";")
            var cp = atol(fields[0], base=16)
            var name = String(fields[1])
            var cat = self._category_index(String(fields[2]))
            if name.endswith(", First>"):
                range_start = cp
                continue
            var lo = range_start if name.endswith(", Last>") else cp
            range_start = -1
            for c in range(lo, cp + 1):
                self.category[c] = cat
                self.ccc[c] = UInt8(atol(fields[3]))
            var decomp = String(fields[5])
            if decomp.byte_length() == 0:
                continue
            var compat = decomp.startswith("<")
            var parts = List[Int]()
            for p in decomp.split(" "):
                if p.byte_length() > 0 and not p.startswith("<"):
                    parts.append(atol(p, base=16))
            self.decomposition[cp] = parts^
            self.is_compat[cp] = compat

    def _read_case_folding(mut self, path: String) raises:
        var text: String
        with open(path, "r") as f:
            text = f.read()
        for line in text.split("\n"):
            if line.startswith("# CaseFolding-"):
                # "# CaseFolding-17.0.0.txt"
                var v = String(line).removeprefix("# CaseFolding-")
                self.version = String(v.removesuffix(".txt"))
            if line.byte_length() == 0 or line.startswith("#"):
                continue
            var fields = line.split("; ")
            var status = String(fields[1])
            if status != "C" and status != "F":
                continue
            var parts = List[Int]()
            for p in fields[2].split(" "):
                parts.append(atol(p, base=16))
            self.folding[atol(fields[0], base=16)] = parts^
        if self.version.byte_length() == 0:
            raise Error("no version line in CaseFolding.txt")

    def decompose(self, cp: Int, compat: Bool, mut out: List[Int]) raises:
        """Append the full (canonical, or compatibility if `compat`)
        decomposition of `cp` to `out`, not yet canonically ordered."""
        var s = cp - HANGUL_S_BASE
        if s >= 0 and s < HANGUL_S_COUNT:
            out.append(HANGUL_L_BASE + s // HANGUL_N_COUNT)
            out.append(HANGUL_V_BASE + (s % HANGUL_N_COUNT) // HANGUL_T_COUNT)
            if s % HANGUL_T_COUNT != 0:
                out.append(HANGUL_T_BASE + s % HANGUL_T_COUNT)
            return
        if cp in self.decomposition and (compat or not self.is_compat[cp]):
            for d in self.decomposition[cp]:
                self.decompose(d, compat, out)
            return
        out.append(cp)

    def normalized(self, cp: Int, compat: Bool) raises -> List[Int]:
        """NFD (or NFKD if `compat`) of the single character `cp`."""
        var out = List[Int]()
        self.decompose(cp, compat, out)
        # Canonical ordering: stable sort of each run of non-starters by
        # combining class.
        var changed = True
        while changed:
            changed = False
            for i in range(1, len(out)):
                var a = self.ccc[out[i - 1]]
                var b = self.ccc[out[i]]
                if a > b and b != 0:
                    var t = out[i - 1]
                    out[i - 1] = out[i]
                    out[i] = t
                    changed = True
        return out^


def write_categories(ucd: Ucd, path: String) raises:
    var ranges = List[List[String]]()
    for _ in range(len(ucd.category_names)):
        ranges.append(List[String]())
    var start = 0
    for cp in range(1, MAX_CODEPOINT + 2):
        if cp <= MAX_CODEPOINT and ucd.category[cp] == ucd.category[start]:
            continue
        var r = _hex(start) if start == cp - 1 else String(
            _hex(start), "-", _hex(cp - 1)
        )
        ranges[Int(ucd.category[start])].append(r^)
        start = cp
    var order = List[Int]()
    for i in range(len(ucd.category_names)):
        var j = len(order)
        while (
            j > 0 and ucd.category_names[order[j - 1]] > ucd.category_names[i]
        ):
            j -= 1
        order.insert(j, i)
    var total = 0
    var lines = String()
    for i in order:
        if len(ranges[i]) == 0:
            continue
        total += len(ranges[i])
        lines += String(
            '    "', ucd.category_names[i], " ", " ".join(ranges[i]), '\\n"\n'
        )
    var src = String(
        HEADER,
        '"""Codepoint ranges of each Unicode general category.\n\n',
        "Generated by tools/gen_unicode.mojo from Unicode ",
        ucd.version,
        "\n(",
        len(order),
        " categories, ",
        total,
        ' ranges). Do not edit by hand.\n"""\n\n',
        'comptime UNICODE_VERSION = "',
        ucd.version,
        '"\n\n',
        "comptime CATEGORY_DATA: StaticString = (\n",
        lines,
        ")\n",
    )
    with open(path, "w") as f:
        f.write(src)
    print("wrote", path, ":", len(order), "categories,", total, "ranges")


def write_decompositions(ucd: Ucd, path: String) raises:
    var entries = List[String]()
    for cp in range(MAX_CODEPOINT + 1):
        if cp >= 0xD800 and cp <= 0xDFFF:
            continue
        if cp >= HANGUL_S_BASE and cp < HANGUL_S_BASE + HANGUL_S_COUNT:
            continue
        var found = List[Int]()
        var forms = List[List[Int]]()
        forms.append(ucd.normalized(cp, False))
        forms.append(ucd.normalized(cp, True))
        if cp in ucd.folding:
            forms.append(ucd.folding[cp].copy())
        for form in forms:
            for d in form:
                if d != cp and d not in found:
                    found.append(d)
        if len(found) == 0:
            continue
        var parts = List[String]()
        for d in found:
            parts.append(_hex(d))
        entries.append(String(_hex(cp), ":", ",".join(parts)))
    var lines = String()
    var i = 0
    while i < len(entries):
        var chunk = List[String]()
        for j in range(i, min(i + 12, len(entries))):
            chunk.append(entries[j])
        lines += String('    "', " ".join(chunk), ' "\n')
        i += 12
    var src = String(
        HEADER,
        '"""Characters in the NFD/NFKD decomposition and casefold of each',
        " codepoint.\n\n",
        "Generated by tools/gen_unicode.mojo from Unicode ",
        ucd.version,
        "\n(",
        len(entries),
        " codepoints). Do not edit by hand. Each entry is\n",
        "`codepoint:component,component,...` in hex, entries separated by",
        ' spaces.\n"""\n\n',
        "comptime DECOMPOSITION_DATA: StaticString = (\n",
        lines,
        ")\n",
    )
    with open(path, "w") as f:
        f.write(src)
    print("wrote", path, ":", len(entries), "codepoints")


def main() raises:
    var args = argv()
    if len(args) < 2:
        raise Error("usage: mojo run tools/gen_unicode.mojo <ucd directory>")
    var ucd = Ucd(String(args[len(args) - 1]))
    write_categories(ucd, "proptest/internal/charmap_data.mojo")
    write_decompositions(ucd, "proptest/internal/decomposition_data.mojo")
