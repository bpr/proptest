# Dictionaries: tokens for generation and the fuzz loop.

from std.os import remove, rmdir
from std.pathlib import Path
from std.tempfile import mkdtemp
from std.testing import TestSuite, assert_equal, assert_true, assert_raises

from proptest import *


def test_parse_reads_the_afl_and_libfuzzer_format() raises:
    var d = parse_dictionary(
        "# a comment\n"
        + '"plain"\n'
        + 'kw_get="GET"\n'
        + 'level@2="lvl"\n'
        + '  esc="a\\\\b\\"c"  \n'
        + '\nbin="\\x89P\\x00\\xFf"\n'
        + 'dup="GET"\n'
    )
    assert_equal(len(d), 5)  # the second GET is dropped
    assert_true(d.tokens[0] == List[UInt8]("plain".as_bytes()))
    assert_true(d.tokens[1] == List[UInt8]("GET".as_bytes()))
    assert_true(d.tokens[2] == List[UInt8]("lvl".as_bytes()))
    assert_true(d.tokens[3] == List[UInt8]('a\\b"c'.as_bytes()))
    var bin: List[UInt8] = [0x89, 0x50, 0, 0xFF]
    assert_true(d.tokens[4] == bin)


def test_parse_reports_the_bad_line() raises:
    with assert_raises(contains="d.dict:2: expected a quoted token"):
        _ = parse_dictionary('"ok"\nkw=GET\n', "d.dict")
    with assert_raises(contains="d.dict:1: bad \\x escape"):
        _ = parse_dictionary('"\\x4"\n', "d.dict")
    with assert_raises(contains="d.dict:1: unknown escape \\n"):
        _ = parse_dictionary('"a\\n"\n', "d.dict")


def test_load_reads_a_file() raises:
    var dir = mkdtemp()
    var path = String(dir, "/http.dict")
    Path(path).write_text('get="GET"\npost="POST"\n')
    var d = load_dictionary(path)
    remove(path)
    rmdir(dir)
    assert_equal(len(d), 2)
    var s = Settings(dictionary=d^)
    s.dictionary.add(Dictionary(["PUT", "GET"]))
    assert_equal(len(s.dictionary), 3)
    var t = Settings(dictionary=["a", "b"])
    assert_equal(len(t.dictionary), 2)


def test_generation_returns_tokens() raises:
    var settings = Settings(
        max_examples=2000,
        database=None,
        seed=UInt64(1),
        dictionary=["x-proptest-magic", "0x5EED1234", "\x01\x02\x03\x04\x05"],
    )

    def magic(s: String) -> Bool:
        return s == "x-proptest-magic"

    def number(n: Int) -> Bool:
        return n == 0x5EED1234

    def raw(b: List[UInt8]) -> Bool:
        return b == [UInt8(1), 2, 3, 4, 5]

    assert_equal(find(text(), magic, settings), "x-proptest-magic")
    assert_equal(find(integers(), number, settings), 0x5EED1234)
    assert_equal(len(find(binary(), raw, settings)), 5)


def test_fuzz_puts_tokens_together() raises:
    def prop(req: String) raises:
        if req.startswith("POST /admin"):
            fail("admin")

    var target = fuzz_target(
        text(),
        prop,
        Settings(
            database=None,
            seed=UInt64(1),
            dictionary=["GET", "POST", " ", "/admin", "/index", "HTTP/1.1"],
        ),
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=50_000)
    except e:
        msg = String(e)
    assert_true("given('POST /admin')" in msg, msg)


def test_fuzz_uses_tokens_that_are_not_utf8_in_byte_strings() raises:
    def prop(b: List[UInt8]) raises:
        var sig: List[UInt8] = [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        if len(b) < 12:
            return
        for i in range(8):
            if b[i] != sig[i]:
                return
        var end = "IEND".as_bytes()
        for i in range(4):
            if b[len(b) - 4 + i] != end[i]:
                return
        fail("a PNG")

    var target = fuzz_target(
        binary(max_size=64),
        prop,
        Settings(
            database=None,
            seed=UInt64(2),
            dictionary=parse_dictionary(
                'header="\\x89PNG\\x0d\\x0a\\x1a\\x0a"\nend="IEND"\n'
            ),
        ),
    )
    var msg = String()
    try:
        _ = target.fuzz(max_inputs=20_000)
    except e:
        msg = String(e)
    assert_true("a PNG" in msg, msg)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
