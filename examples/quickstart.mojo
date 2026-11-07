# The run-length encoding example from Hypothesis's quickstart guide.
#
# `encode` has a bug: it never emits the final run. proptest finds a failing
# input and shrinks it to the simplest one, the one-character string "0".
#
#   pixi run mojo run -I . examples/quickstart.mojo

from std.testing import assert_equal

from proptest import given, text, Settings


def encode(s: String) -> List[Tuple[String, Int]]:
    var out = List[Tuple[String, Int]]()
    var prev = String()
    var count = 0
    for cp in s.codepoints():
        var c = String(cp)
        if c != prev and count > 0:
            out.append((prev, count))
            count = 0
        prev = c
        count += 1
    # BUG: the last run is never appended
    return out^


def decode(runs: List[Tuple[String, Int]]) -> String:
    var s = String()
    for r in runs:
        for _ in range(r[1]):
            s += r[0]
    return s^


def main():
    def decode_inverts_encode(s: String) raises:
        assert_equal(decode(encode(s)), s)

    try:
        given(text(), decode_inverts_encode, Settings(database=None))
    except e:
        print(e)
