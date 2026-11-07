# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The example database: failing choice sequences saved between runs.

Port of `hypothesis.database` (`DirectoryBasedExampleDatabase` and
`InMemoryExampleDatabase`) and of `choices_to_bytes`/`choices_from_bytes`.

A saved example is a choice sequence, not a value, so it replays through
whatever strategies the test uses. Each test has its own subdirectory,
named by a hash of its key, holding one file per saved example, named by
a hash of its contents. The serialization is a line-oriented text format
(one choice per line) rather than Hypothesis's binary one.
"""

from std.hash import hash
from std.base64 import b64encode, b64decode
from std.os import makedirs, listdir, remove
from std.os.path import exists, join, isdir

from proptest.internal.choice import (
    ChoiceValue,
    INTEGER,
    FLOAT,
    BOOLEAN,
    BYTES,
    STRING,
)
from proptest.internal.floats import float_to_int, int_to_float


def _hex(x: UInt64) -> String:
    comptime digits = "0123456789abcdef"
    var out = String()
    for i in range(15, -1, -1):
        var d = Int((x >> UInt64(4 * i)) & 0xF)
        out += digits[byte=d]
    return out^


def _seq_to_string(seq: List[UInt32]) -> String:
    var s = String()
    for k in range(len(seq)):
        if k > 0:
            s += ","
        s += String(seq[k])
    return s^


def _parse_seq(s: StringSlice) raises -> List[UInt32]:
    var out = List[UInt32]()
    if s.byte_length() == 0:
        return out^
    for part in s.split(","):
        out.append(UInt32(Int(part)))
    return out^


def choices_to_string(choices: List[ChoiceValue]) -> String:
    """Serialize a choice sequence (one choice per line)."""
    var out = String()
    for c in choices:
        if c.kind == INTEGER:
            out += String("i:", c.i, "\n")
        elif c.kind == FLOAT:
            out += String("f:", float_to_int(c.f), "\n")
        elif c.kind == BOOLEAN:
            out += String("b:", 1 if c.i != 0 else 0, "\n")
        elif c.kind == BYTES:
            out += String("y:", _seq_to_string(c.seq), "\n")
        else:
            out += String("s:", _seq_to_string(c.seq), "\n")
    return out^


def _parse_int128(s: StringSlice) raises -> Int128:
    var neg = False
    var start = 0
    var bytes = s.as_bytes()
    if len(bytes) > 0 and bytes[0] == UInt8(ord("-")):
        neg = True
        start = 1
    var v = Int128(0)
    for k in range(start, len(bytes)):
        var d = Int(bytes[k]) - ord("0")
        if d < 0 or d > 9:
            raise Error("bad integer in database entry")
        v = v * 10 + Int128(d)
    return -v if neg else v


def choices_from_string(s: String) raises -> List[ChoiceValue]:
    """Parse a serialized choice sequence; raises if it is malformed."""
    var out = List[ChoiceValue]()
    for line in s.split("\n"):
        if line.byte_length() == 0:
            continue
        if line.byte_length() < 2:
            raise Error("bad database entry")
        var tag = line[byte=0]
        var rest = line[byte=2:]
        if tag == "i":
            out.append(ChoiceValue(integer=_parse_int128(rest)))
        elif tag == "f":
            out.append(
                ChoiceValue(float=int_to_float(UInt64(_parse_int128(rest))))
            )
        elif tag == "b":
            out.append(ChoiceValue(boolean=rest == "1"))
        elif tag == "y":
            out.append(ChoiceValue(bytes=_parse_seq(rest)))
        elif tag == "s":
            out.append(ChoiceValue(string=_parse_seq(rest)))
        else:
            raise Error("bad database entry")
    return out^


comptime _BLOB_PREFIX = "proptest1:"


def encode_blob(choices: List[ChoiceValue]) -> String:
    """A single-line, copy-pasteable encoding of a choice sequence, for
    `Settings(reproduce=...)` (Hypothesis's `@reproduce_failure` blob)."""
    return String(_BLOB_PREFIX, b64encode(choices_to_string(choices)))


def decode_blob(blob: String) raises -> List[ChoiceValue]:
    """Inverse of `encode_blob`; raises on a malformed blob."""
    var b = blob.strip()
    if not b.startswith(_BLOB_PREFIX):
        raise Error(
            "InvalidArgument: not a proptest reproduce blob (expected it to"
            " start with '"
            + String(_BLOB_PREFIX)
            + "')"
        )
    var raw = b64decode(b[byte = StaticString(_BLOB_PREFIX).byte_length() :])
    return choices_from_string(String(from_utf8=raw))


struct ExampleDatabase(Copyable):
    """A directory-backed store of choice sequences, keyed by test.

    With an empty `path` it keeps entries in memory instead (Hypothesis's
    `InMemoryExampleDatabase`), which is useful in tests.
    """

    var path: String
    var memory: Dict[String, List[String]]

    def __init__(out self, path: String):
        self.path = path
        self.memory = Dict[String, List[String]]()

    @staticmethod
    def in_memory() -> Self:
        return Self("")

    def _dir(self, key: String) -> String:
        return join(self.path, _hex(hash(key)))

    def save(mut self, key: String, choices: List[ChoiceValue]):
        """Save a choice sequence under `key` (idempotent)."""
        var text = choices_to_string(choices)
        if self.path.byte_length() == 0:
            if key not in self.memory:
                self.memory[key] = List[String]()
            try:
                for v in self.memory[key]:
                    if v == text:
                        return
                self.memory[key].append(text)
            except:
                pass
            return
        try:
            var d = self._dir(key)
            if not isdir(d):
                makedirs(d, exist_ok=True)
            var f = join(d, _hex(hash(text)))
            if exists(f):
                return
            with open(f, "w") as fh:
                fh.write(text)
        except:
            pass  # the database is best-effort, as in Hypothesis

    def delete(mut self, key: String, choices: List[ChoiceValue]):
        """Remove a choice sequence from `key`, if present."""
        var text = choices_to_string(choices)
        if self.path.byte_length() == 0:
            try:
                if key in self.memory:
                    var kept = List[String]()
                    for v in self.memory[key]:
                        if v != text:
                            kept.append(v)
                    self.memory[key] = kept^
            except:
                pass
            return
        try:
            var f = join(self._dir(key), _hex(hash(text)))
            if exists(f):
                remove(f)
        except:
            pass

    def fetch(self, key: String) -> List[List[ChoiceValue]]:
        """Every choice sequence saved under `key` (unparseable entries are
        skipped)."""
        var out = List[List[ChoiceValue]]()
        if self.path.byte_length() == 0:
            try:
                if key in self.memory:
                    for v in self.memory[key]:
                        try:
                            out.append(choices_from_string(v))
                        except:
                            pass
            except:
                pass
            return out^
        try:
            var d = self._dir(key)
            if not isdir(d):
                return out^
            for name in listdir(d):
                try:
                    with open(join(d, name), "r") as fh:
                        out.append(choices_from_string(fh.read()))
                except:
                    pass
        except:
            pass
        return out^
