# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Fuzzing dictionaries: tokens the input format uses.

A `Dictionary` lists tokens (keywords, magic bytes, numbers) that a test's
inputs are likely to need, as AFL++ and libFuzzer dictionaries do. Pass
one as `Settings(dictionary=...)`: generation occasionally returns a token
whole (for strings, bytes and integers), and the fuzz loop inserts tokens
into strings and byte strings, overwrites parts of them with tokens, and
sets integers to the tokens that are numbers.

```mojo
var settings = Settings(dictionary=["GET", "POST", "HTTP/1.1", "\\r\\n"])
var http = Settings(dictionary=load_dictionary("http.dict"))
```
"""

from std.pathlib import Path


struct Dictionary(Copyable, Sized, Writable):
    """Tokens for generation and fuzzing to use; see the module docs."""

    var tokens: List[List[UInt8]]
    """Each token's bytes (which need not be UTF-8: such a token is used
    only for byte strings)."""

    def __init__(out self):
        """An empty dictionary."""
        self.tokens = List[List[UInt8]]()

    @implicit
    def __init__(out self, tokens: List[String]):
        """A dictionary of `tokens`."""
        self.tokens = List[List[UInt8]]()
        for t in tokens:
            self.add(t)

    def __init__(out self, var *tokens: String, __list_literal__: NoneType):
        """A dictionary from a list literal: `["GET", "POST"]`."""
        self.tokens = List[List[UInt8]]()
        for t in tokens:
            self.add(t)

    def add(mut self, token: String):
        """Add `token`."""
        self.add_bytes(token.as_bytes())

    def add_bytes(mut self, token: Span[UInt8, _]):
        """Add a token given as bytes."""
        var b = List[UInt8](token)
        for t in self.tokens:
            if t == b:
                return
        self.tokens.append(b^)

    def add(mut self, other: Dictionary):
        """Add the tokens of `other`."""
        for t in other.tokens:
            self.add_bytes(t)

    def __len__(self) -> Int:
        return len(self.tokens)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Dictionary(", len(self.tokens), " tokens)")


def _hex_digit(b: UInt8) -> Int:
    var c = Int(b)
    if c >= ord("0") and c <= ord("9"):
        return c - ord("0")
    if c >= ord("a") and c <= ord("f"):
        return c - ord("a") + 10
    if c >= ord("A") and c <= ord("F"):
        return c - ord("A") + 10
    return -1


def parse_dictionary(
    text: String, name: String = "<string>"
) raises -> Dictionary:
    """Parse a dictionary in the AFL++/libFuzzer format: one token per
    line, written `"value"` or `name="value"` (AFL++'s `name@level="value"`
    too), with `\\\\`, `\\"` and `\\xNN` escapes; blank lines and lines
    starting with `#` are skipped. Raises on a malformed line."""
    var d = Dictionary()
    var lineno = 0
    for line in text.split("\n"):
        lineno += 1
        var s = String(String(line).strip())
        var b = s.as_bytes()
        if len(b) == 0 or b[0] == UInt8(ord("#")):
            continue
        var first = -1
        for i in range(len(b)):
            if b[i] == UInt8(ord('"')):
                first = i
                break
        if first < 0 or len(b) < first + 2 or b[len(b) - 1] != UInt8(ord('"')):
            raise Error(
                String(name, ":", lineno, ": expected a quoted token: ", s)
            )
        var tok = List[UInt8]()
        var i = first + 1
        var end = len(b) - 1
        while i < end:
            var c = b[i]
            if c != UInt8(ord("\\")):
                tok.append(c)
                i += 1
                continue
            if i + 1 >= end:
                raise Error(String(name, ":", lineno, ": dangling backslash"))
            var e = b[i + 1]
            if e == UInt8(ord("\\")) or e == UInt8(ord('"')):
                tok.append(e)
                i += 2
            elif e == UInt8(ord("x")) and i + 3 < end + 1:
                var hi = _hex_digit(b[i + 2]) if i + 2 < end else -1
                var lo = _hex_digit(b[i + 3]) if i + 3 < end else -1
                if hi < 0 or lo < 0:
                    raise Error(String(name, ":", lineno, ": bad \\x escape"))
                tok.append(UInt8(hi * 16 + lo))
                i += 4
            else:
                raise Error(
                    String(
                        name, ":", lineno, ": unknown escape \\", chr(Int(e))
                    )
                )
        d.add_bytes(tok)
    return d^


def load_dictionary(path: String) raises -> Dictionary:
    """Read a dictionary file in the AFL++/libFuzzer format (see
    `parse_dictionary`), such as those that ship with AFL++
    (`dictionaries/*.dict`)."""
    return parse_dictionary(Path(path).read_text(), path)
