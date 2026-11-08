# Generated values need only be Movable: strategies, given, check, find and
# typed state machines work with move-only types. proptest-specific (Rust
# proptest only requires `Debug` of its values); in Hypothesis every value
# is a Python object, so the question doesn't arise.

from std.testing import TestSuite, assert_equal, assert_true

from proptest import *


def fast() -> Settings:
    return Settings(database=None, max_examples=100)


struct Handle(Movable, Writable):
    """A unique resource: movable, not copyable."""

    var id: Int

    def __init__(out self, id: Int):
        self.id = id

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Handle(", self.id, ")")


struct Token(Arbitrary, Movable, Writable):
    var n: UInt8

    def __init__(out self, n: UInt8):
        self.n = n

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers_of[DType.uint8]()))

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Token(", self.n, ")")


struct Handles(Copyable, Strategy):
    comptime Value = Handle

    def __init__(out self):
        pass

    def do_draw(self, mut data: ConjectureData) raises -> Handle:
        return Handle(data.draw(integers(0, 1000)))


def handles() -> Handles:
    return Handles()


def test_combinators_with_move_only_values() raises:
    # (no `List[Handle]`: in Mojo 1.3 `List.write_to` copies its elements,
    # so a list of a move-only type can't be printed in a report)
    def prop(h: Handle, o: Optional[Handle]) raises:
        assert_true(h.id >= 0 and h.id <= 1000)
        if o:
            assert_true(o.value().id <= 1000)

    given(handles(), optionals(handles()), prop, fast())

    def count(n: Int) raises:
        assert_true(n <= 100)

    # lists of move-only values can still be drawn and consumed
    given(
        map(
            lists(handles(), max_size=100),
            lambda (hs: List[Handle]) -> Int: len(hs),
        ),
        count,
        fast(),
    )

    def even(h: Handle) raises -> Bool:
        return h.id % 2 == 0

    def pair(t: Tuple[Handle, Handle]) raises:
        assert_true(t[0].id % 2 == 0)

    given(tuples(filter(handles(), even), handles()), pair, fast())

    def either(h: Handle) raises:
        assert_true(h.id <= 1000 or h.id == -1)

    given(
        one_of(handles(), lazy_just(lambda () -> Handle: Handle(-1))),
        either,
        fast(),
    )


def test_failures_report_move_only_values() raises:
    def prop(h: Handle) raises:
        if h.id >= 10:
            fail("too big")

    var msg = String()
    try:
        given(handles(), prop, fast())
    except e:
        msg = String(e)
    assert_true("Handle(10)" in msg and "too big" in msg, msg)

    def big(h: Handle) -> Bool:
        return h.id > 500

    assert_equal(find(handles(), big).id, 501)


def test_check_and_from_type_with_move_only_values() raises:
    def prop(t: Token, u: Optional[Token]) -> Bool:
        return t.n < 7

    var msg = String()
    try:
        check(prop, fast())
    except e:
        msg = String(e)
    assert_true("Token(7)," in msg and "None" in msg, msg)


def test_lazy_just_makes_a_fresh_value_each_time() raises:
    var s = lazy_just(lambda () -> List[Int]: [1, 2, 3])
    var a = example(s)
    a.append(4)
    assert_equal(example(s), [1, 2, 3])


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
