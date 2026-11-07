# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Strings matching a regular expression: `from_regex`.

Port of `hypothesis.strategies._internal.regex`. Hypothesis parses the
pattern with Python's `sre_parse` and builds a strategy per node; Mojo has
no regex module, so proptest has its own parser for the common subset of
Python regex syntax:

- literals and escapes: `\\n \\t \\r \\f \\v \\0 \\xHH \\uHHHH \\UHHHHHHHH`,
  and backslash before any punctuation;
- `.`, character classes `[abc]`, `[a-z]`, `[^...]`, and the class escapes
  `\\d \\D \\w \\W \\s \\S` (Unicode, as in Python: `\\d` is category `Nd`,
  `\\w` is letters, numbers and `_`, `\\s` is whitespace);
- groups `( )`, `(?: )`, `(?P<name> )`, alternation `|`;
- quantifiers `* + ? {n} {n,} {n,m} {,m}`, lazy (`*?`) and possessive
  (`*+`) forms (which match the same strings);
- anchors `^ $ \\A \\Z` and the inline flags `(?i)` and `(?s)` at the start.

Not supported (they raise `InvalidArgument`): backreferences, lookaround,
word boundaries `\\b \\B`, conditionals, and the other flags. Because
every supported construct is generated exactly, no filtering by a regex
engine is needed (Hypothesis filters with `re.search`/`re.fullmatch`).
"""

from std.memory import ArcPointer

from proptest.internal.data import ConjectureData, calc_label_from_name
from proptest.internal.choice import COLLECTION_DEFAULT_MAX_SIZE
from proptest.internal.intervals import (
    IntervalSet,
    codepoints_to_string,
    string_to_codepoints,
    MAX_CODEPOINT,
)
from proptest.internal.charmap import as_general_categories, category_intervals
from proptest.strategies.strategy import Strategy, Many

comptime _CLASS = 0
comptime _SEQ = 1
comptime _ALT = 2
comptime _REPEAT = 3
comptime _BEGIN = 4  # ^ or \A
comptime _END = 5  # $ or \Z

comptime _REGEX_LABEL: UInt64 = 0x7265676578


struct _Node(Copyable):
    var kind: Int
    var chars: IntervalSet
    var children: List[Int]
    var min: Int
    var max: Int
    var strict_end: Bool
    """For `_END`: `\\Z` (no trailing newline allowed) rather than `$`."""

    def __init__(out self, kind: Int):
        self.kind = kind
        self.chars = IntervalSet()
        self.children = List[Int]()
        self.min = 0
        self.max = 0
        self.strict_end = False


def _all_chars() -> IntervalSet:
    return IntervalSet.default_text()


def _digit() raises -> IntervalSet:
    return category_intervals(as_general_categories(["Nd"]))


def _word() raises -> IntervalSet:
    return category_intervals(as_general_categories(["L", "N"])).union(
        IntervalSet.from_string("_")
    )


def _space() raises -> IntervalSet:
    return category_intervals(as_general_categories(["Z"])).union(
        IntervalSet.from_string(" \t\n\r\f\v\x1c\x1d\x1e\x1f\x85")
    )


def _complement(s: IntervalSet) -> IntervalSet:
    return _all_chars().difference(s)


def _case_variants(s: IntervalSet) -> IntervalSet:
    """`s` plus the single-codepoint upper/lowercase forms of its members
    (for `(?i)`); very large sets are returned unchanged."""
    if len(s) > 5000:
        return s.copy()
    var extra = List[Tuple[UInt32, UInt32]]()
    for i in range(len(s)):
        var c = s[i]
        var cp = Codepoint.from_u32(c)
        if not cp:
            continue
        var t = String(cp.value())
        for form in [t.upper(), t.lower()]:
            var cps = string_to_codepoints(form)
            if len(cps) == 1:
                extra.append((cps[0], cps[0]))
    return s.union(IntervalSet(extra^))


struct _Parser:
    var src: List[UInt32]
    var pos: Int
    var nodes: List[_Node]
    var ignore_case: Bool
    var dotall: Bool
    var pattern: String

    def __init__(out self, pattern: String):
        self.src = string_to_codepoints(pattern)
        self.pos = 0
        self.nodes = List[_Node]()
        self.ignore_case = False
        self.dotall = False
        self.pattern = pattern

    def fail(self, msg: String) -> Error:
        return Error(
            String(
                "InvalidArgument: from_regex(",
                repr(self.pattern),
                "): ",
                msg,
                " at position ",
                self.pos,
            )
        )

    def at_end(self) -> Bool:
        return self.pos >= len(self.src)

    def peek(self) -> UInt32:
        return self.src[self.pos]

    def is_char(self, c: StaticString) -> Bool:
        # metacharacters are all ASCII
        return not self.at_end() and self.src[self.pos] == UInt32(
            c.as_bytes()[0]
        )

    def add(mut self, var node: _Node) -> Int:
        self.nodes.append(node^)
        return len(self.nodes) - 1

    def add_class(mut self, var s: IntervalSet) -> Int:
        var n = _Node(_CLASS)
        n.chars = _case_variants(s) if self.ignore_case else s^
        return self.add(n^)

    # pattern := flags? alternation
    def parse(mut self) raises -> Int:
        self.parse_leading_flags()
        var root = self.parse_alternation()
        if not self.at_end():
            raise self.fail("unbalanced parenthesis")
        return root

    def parse_leading_flags(mut self) raises:
        while (
            self.pos + 2 < len(self.src)
            and self.src[self.pos] == UInt32(ord("("))
            and self.src[self.pos + 1] == UInt32(ord("?"))
        ):
            var k = self.pos + 2
            var flags = List[UInt32]()
            while k < len(self.src) and self.src[k] != UInt32(ord(")")):
                flags.append(self.src[k])
                k += 1
            var all_flags = len(flags) > 0
            for f in flags:
                if f != UInt32(ord("i")) and f != UInt32(ord("s")):
                    all_flags = False
            if not all_flags:
                return
            for f in flags:
                if f == UInt32(ord("i")):
                    self.ignore_case = True
                else:
                    self.dotall = True
            self.pos = k + 1

    def parse_alternation(mut self) raises -> Int:
        var branches = List[Int]()
        branches.append(self.parse_sequence())
        while self.is_char("|"):
            self.pos += 1
            branches.append(self.parse_sequence())
        if len(branches) == 1:
            return branches[0]
        var n = _Node(_ALT)
        n.children = branches^
        return self.add(n^)

    def parse_sequence(mut self) raises -> Int:
        var items = List[Int]()
        while (
            not self.at_end()
            and not self.is_char("|")
            and not self.is_char(")")
        ):
            var atom = self.parse_atom()
            items.append(self.parse_quantifier(atom))
        var n = _Node(_SEQ)
        n.children = items^
        return self.add(n^)

    def parse_quantifier(mut self, atom: Int) raises -> Int:
        if self.at_end():
            return atom
        var lo: Int
        var hi: Int
        if self.is_char("*"):
            lo = 0
            hi = COLLECTION_DEFAULT_MAX_SIZE
            self.pos += 1
        elif self.is_char("+"):
            lo = 1
            hi = COLLECTION_DEFAULT_MAX_SIZE
            self.pos += 1
        elif self.is_char("?"):
            lo = 0
            hi = 1
            self.pos += 1
        elif self.is_char("{"):
            var save = self.pos
            var parsed = self.parse_braces()
            if not parsed:
                self.pos = save
                return atom
            lo = parsed.value()[0]
            hi = parsed.value()[1]
        else:
            return atom
        if self.nodes[atom].kind == _BEGIN or self.nodes[atom].kind == _END:
            raise self.fail("nothing to repeat")
        # lazy or possessive suffix: same set of matches
        if self.is_char("?") or self.is_char("+"):
            self.pos += 1
        if hi < lo:
            raise self.fail("min repeat greater than max repeat")
        var n = _Node(_REPEAT)
        n.children.append(atom)
        n.min = lo
        n.max = hi
        return self.add(n^)

    def parse_number(mut self) -> Int:
        var v = -1
        while (
            not self.at_end()
            and self.peek() >= UInt32(ord("0"))
            and self.peek() <= UInt32(ord("9"))
        ):
            v = max(v, 0) * 10 + Int(self.peek() - UInt32(ord("0")))
            self.pos += 1
        return v

    def parse_braces(mut self) raises -> Optional[Tuple[Int, Int]]:
        """`{n}`, `{n,}`, `{n,m}` or `{,m}`; None if this `{` is a literal."""
        self.pos += 1  # {
        var lo = self.parse_number()
        var hi: Int
        if self.is_char(","):
            self.pos += 1
            hi = self.parse_number()
            if hi < 0:
                hi = COLLECTION_DEFAULT_MAX_SIZE
            if lo < 0:
                lo = 0
        else:
            if lo < 0:
                return None
            hi = lo
        if not self.is_char("}"):
            return None
        self.pos += 1
        return (lo, hi)

    def parse_atom(mut self) raises -> Int:
        var c = self.peek()
        if c == UInt32(ord("(")):
            return self.parse_group()
        if c == UInt32(ord("[")):
            return self.add_class(self.parse_class())
        if c == UInt32(ord(".")):
            self.pos += 1
            var s = _all_chars()
            if not self.dotall:
                s = s.difference(IntervalSet.from_string("\n"))
            var n = _Node(_CLASS)
            n.chars = s^
            return self.add(n^)
        if c == UInt32(ord("^")):
            self.pos += 1
            return self.add(_Node(_BEGIN))
        if c == UInt32(ord("$")):
            self.pos += 1
            return self.add(_Node(_END))
        if c == UInt32(ord("\\")):
            return self.parse_escape_atom()
        if (
            c == UInt32(ord("*"))
            or c == UInt32(ord("+"))
            or c == UInt32(ord("?"))
        ):
            raise self.fail("nothing to repeat")
        self.pos += 1
        return self.add_class(IntervalSet.range(c, c))

    def parse_group(mut self) raises -> Int:
        self.pos += 1  # (
        if self.is_char("?"):
            self.pos += 1
            if self.is_char(":"):
                self.pos += 1
            elif (
                self.is_char("P")
                and self.pos + 1 < len(self.src)
                and self.src[self.pos + 1] == UInt32(ord("<"))
            ):
                while not self.at_end() and not self.is_char(">"):
                    self.pos += 1
                if self.at_end():
                    raise self.fail("unterminated group name")
                self.pos += 1
            else:
                raise self.fail(
                    "unsupported group (lookaround, backreference, conditional"
                    " or inline flag)"
                )
        var inner = self.parse_alternation()
        if not self.is_char(")"):
            raise self.fail("missing )")
        self.pos += 1
        return inner

    def parse_hex(mut self, digits: Int) raises -> UInt32:
        var v = UInt32(0)
        for _ in range(digits):
            if self.at_end():
                raise self.fail("incomplete escape")
            var c = self.peek()
            var d: UInt32
            if c >= UInt32(ord("0")) and c <= UInt32(ord("9")):
                d = c - UInt32(ord("0"))
            elif c >= UInt32(ord("a")) and c <= UInt32(ord("f")):
                d = c - UInt32(ord("a")) + 10
            elif c >= UInt32(ord("A")) and c <= UInt32(ord("F")):
                d = c - UInt32(ord("A")) + 10
            else:
                raise self.fail("bad hex escape")
            v = v * 16 + d
            self.pos += 1
        return v

    def parse_escape(mut self, in_class: Bool) raises -> IntervalSet:
        """The set of characters an escape (after the backslash) stands
        for."""
        if self.at_end():
            raise self.fail("trailing backslash")
        var c = self.peek()
        self.pos += 1
        var ch = String(Codepoint.from_u32(c).value())
        if ch == "d":
            return _digit()
        if ch == "D":
            return _complement(_digit())
        if ch == "w":
            return _word()
        if ch == "W":
            return _complement(_word())
        if ch == "s":
            return _space()
        if ch == "S":
            return _complement(_space())
        var lit: UInt32
        if ch == "n":
            lit = 10
        elif ch == "t":
            lit = 9
        elif ch == "r":
            lit = 13
        elif ch == "f":
            lit = 12
        elif ch == "v":
            lit = 11
        elif ch == "a":
            lit = 7
        elif ch == "0":
            lit = 0
        elif ch == "x":
            lit = self.parse_hex(2)
        elif ch == "u":
            lit = self.parse_hex(4)
        elif ch == "U":
            lit = self.parse_hex(8)
        elif ch == "b" and in_class:
            lit = 8
        elif (
            (c >= UInt32(ord("a")) and c <= UInt32(ord("z")))
            or (c >= UInt32(ord("A")) and c <= UInt32(ord("Z")))
            or (c >= UInt32(ord("1")) and c <= UInt32(ord("9")))
        ):
            raise self.fail(
                String(
                    "unsupported escape \\",
                    ch,
                    " (backreferences and word boundaries are not supported)",
                )
            )
        else:
            lit = c
        if lit > MAX_CODEPOINT:
            raise self.fail("codepoint out of range")
        return IntervalSet.range(lit, lit)

    def parse_escape_atom(mut self) raises -> Int:
        self.pos += 1  # backslash
        if self.is_char("A"):
            self.pos += 1
            return self.add(_Node(_BEGIN))
        if self.is_char("Z"):
            self.pos += 1
            var n = _Node(_END)
            n.strict_end = True
            return self.add(n^)
        return self.add_class(self.parse_escape(False))

    def parse_class(mut self) raises -> IntervalSet:
        self.pos += 1  # [
        var negate = False
        if self.is_char("^"):
            negate = True
            self.pos += 1
        var s = IntervalSet()
        var first = True
        while True:
            if self.at_end():
                raise self.fail("unterminated character set")
            if self.is_char("]") and not first:
                self.pos += 1
                break
            first = False
            var lo_set: IntervalSet
            var lo_single: Optional[UInt32] = None
            if self.is_char("\\"):
                self.pos += 1
                lo_set = self.parse_escape(True)
                if len(lo_set) == 1:
                    lo_single = lo_set[0]
            else:
                var c = self.peek()
                self.pos += 1
                lo_set = IntervalSet.range(c, c)
                lo_single = c
            # a range a-b?
            if (
                lo_single
                and self.is_char("-")
                and self.pos + 1 < len(self.src)
                and self.src[self.pos + 1] != UInt32(ord("]"))
            ):
                self.pos += 1  # -
                var hi: UInt32
                if self.is_char("\\"):
                    self.pos += 1
                    var hs = self.parse_escape(True)
                    if len(hs) != 1:
                        raise self.fail("bad character range")
                    hi = hs[0]
                else:
                    hi = self.peek()
                    self.pos += 1
                if hi < lo_single.value():
                    raise self.fail("bad character range")
                s = s.union(IntervalSet.range(lo_single.value(), hi))
            else:
                s = s.union(lo_set)
        if self.ignore_case:
            s = _case_variants(s)
        if negate:
            s = _complement(s)
        return s^


struct _Regex(Movable):
    var nodes: List[_Node]
    var root: Int
    var starts_anchored: Bool
    var ends_anchored: Bool
    var ends_strict: Bool

    def __init__(out self, pattern: String) raises:
        var p = _Parser(pattern)
        self.root = p.parse()
        self.nodes = p.nodes.copy()
        # leading/trailing anchors (of the top-level sequence) decide padding
        self.starts_anchored = False
        self.ends_anchored = False
        self.ends_strict = False
        ref top = self.nodes[self.root]
        if top.kind == _SEQ and len(top.children) > 0:
            var first = top.children[0]
            var last = top.children[len(top.children) - 1]
            self.starts_anchored = self.nodes[first].kind == _BEGIN
            if self.nodes[last].kind == _END:
                self.ends_anchored = True
                self.ends_strict = self.nodes[last].strict_end

    def check_anchors(self) raises:
        """Anchors other than at the start or end of the whole pattern would
        need a regex engine to honour; reject them."""
        for i in range(len(self.nodes)):
            var k = self.nodes[i].kind
            if k != _BEGIN and k != _END:
                continue
            ref top = self.nodes[self.root]
            var ok = top.kind == _SEQ and (
                (k == _BEGIN and len(top.children) > 0 and top.children[0] == i)
                or (
                    k == _END
                    and len(top.children) > 0
                    and top.children[len(top.children) - 1] == i
                )
            )
            if not ok:
                raise Error(
                    "InvalidArgument: from_regex: anchors (^, $, \\A, \\Z) are"
                    " only supported at the start and end of the pattern"
                )

    def generate(
        self, i: Int, mut data: ConjectureData, mut out: List[UInt32]
    ) raises:
        ref node = self.nodes[i]
        var kind = node.kind
        if kind == _CLASS:
            var one = data.draw_string(ArcPointer(node.chars.copy()), 1, 1)
            out.append(one[0])
        elif kind == _SEQ:
            for c in node.children:
                self.generate(c, data, out)
        elif kind == _ALT:
            var k = data.draw_integer(Int128(0), Int128(len(node.children) - 1))
            self.generate(node.children[Int(k)], data, out)
        elif kind == _REPEAT:
            var child = node.children[0]
            if self.nodes[child].kind == _CLASS:
                # a repeated character class is one string choice, which
                # the string shrinker handles well (as Hypothesis does)
                var s = data.draw_string(
                    ArcPointer(self.nodes[child].chars.copy()),
                    node.min,
                    node.max,
                )
                for c in s:
                    out.append(c)
            else:
                var many = Many(node.min, node.max)
                while many.more(data):
                    self.generate(child, data, out)
        # anchors generate nothing


struct Regex(Copyable, Strategy):
    """Strings matching a regular expression; see `from_regex()`."""

    comptime Value = String
    var regex: ArcPointer[_Regex]
    var fullmatch: Bool
    var padding: ArcPointer[IntervalSet]

    def __init__(out self, pattern: String, fullmatch: Bool) raises:
        var r = _Regex(pattern)
        r.check_anchors()
        self.regex = ArcPointer(r^)
        self.fullmatch = fullmatch
        self.padding = ArcPointer(IntervalSet.default_text())

    def label(self) -> UInt64:
        return _REGEX_LABEL

    def do_draw(self, mut data: ConjectureData) raises -> String:
        ref r = self.regex[]
        var out = List[UInt32]()
        var pad_left = not self.fullmatch and not r.starts_anchored
        var pad_right = not self.fullmatch and not r.ends_anchored
        if pad_left:
            out = data.draw_string(self.padding, 0, COLLECTION_DEFAULT_MAX_SIZE)
        data.start_span(_REGEX_LABEL)
        r.generate(r.root, data, out)
        data.stop_span()
        if pad_right:
            var tail = data.draw_string(
                self.padding, 0, COLLECTION_DEFAULT_MAX_SIZE
            )
            for c in tail:
                out.append(c)
        elif r.ends_anchored and not r.ends_strict and not self.fullmatch:
            # `$` also matches before a final newline
            if data.draw_boolean(0.5):
                out.append(10)
        return codepoints_to_string(out)


def from_regex(pattern: String, *, fullmatch: Bool = False) raises -> Regex:
    """Strings that match `pattern` (Hypothesis's `from_regex`).

    With `fullmatch=False` (the default, as in Hypothesis) the strings
    *contain* a match, so arbitrary text may come before and after it unless
    the pattern is anchored with `^`/`\\A` and `$`/`\\Z`. With
    `fullmatch=True` the whole string matches. See the module documentation
    for the supported syntax; unsupported constructs raise
    `InvalidArgument`.
    """
    return Regex(pattern, fullmatch)
