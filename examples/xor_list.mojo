# An XOR linked list: a doubly linked list whose nodes store one link,
# the XOR of the addresses of their two neighbors (0 for none). Walking
# needs the address of the node you came from: next = link ^ prev. The
# same code walks either way, so reversing the list is swapping its head
# and tail, and appending a list is two XORs.
#
# Every link goes through an integer and back
# (Pointer(unsafe_from_address=...)), which hides from the compiler which
# node a pointer points at: a test of how its alias analysis copes with
# integer-to-pointer casts.
#
# Only XorList allocates, links, and frees nodes, in the methods marked
# UNSAFE. It's Movable, not Copyable (a copy would share nodes); copy()
# builds a list of new nodes.
#
# The tests are model-based: after every command the list is walked both
# ways and compared with a plain List. Build with AddressSanitizer to
# check for use after free and leaks:
#
#   pixi run mojo run -I . examples/xor_list.mojo
#   pixi run mojo build -I . --sanitize address -o xor examples/xor_list.mojo && ./xor
#
# A wrong XOR usually makes the next walk dereference a garbage address,
# killing the process before proptest can shrink anything. Run with
# PROPTEST_FORK=1 (Settings(fork=True)) to run each test case in a child
# process: a crash then shrinks like any other failure, e.g. to
#
#   Draw 1: [0, 0]
#   Draw 2: [insert(1, 0)]
#   Crash: the test case was killed by SIGSEGV (signal 11), ...

from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_true

from proptest import *


# ---- the list


struct XorNode[T: Copyable & Deinitable](Movable):
    var value: Self.T
    var link: Int
    """Int(prev) ^ Int(next), with 0 for a missing neighbor."""

    def __init__(out self, var value: Self.T, link: Int):
        self.value = value^
        self.link = link

    def take_value(deinit self) -> Self.T:
        return self.value^


struct XorList[T: Copyable & Deinitable](Movable, Sized):
    """A sequence with O(1) push and pop at both ends, reverse, and
    extend."""

    comptime Node = XorNode[Self.T]
    comptime NodePtr = Pointer[Self.Node, MutUntrackedOrigin]

    var head: Int
    """The first node's address, or 0 when empty."""
    var tail: Int
    """The last node's address, or 0 when empty."""
    var size: Int

    def __init__(out self):
        self.head = 0
        self.tail = 0
        self.size = 0

    def __init__(out self, values: List[Self.T]):
        self = Self()
        for v in values:
            self.push_back(v.copy())

    def __deinit__(deinit self):
        # UNSAFE: frees every node; nothing may use them afterwards
        var prev = 0
        var cur = self.head
        while cur != 0:
            var next = Self._at(cur)[].link ^ prev
            _ = Self._free(cur)
            prev = cur
            cur = next

    def __len__(self) -> Int:
        return self.size

    @staticmethod
    def _at(addr: Int) -> Self.NodePtr:
        # UNSAFE: addr must be a live node of a list
        return Self.NodePtr(unsafe_from_address=addr)

    @staticmethod
    def _new(var value: Self.T, link: Int) -> Int:
        # UNSAFE: a new node; the caller must link it into the list
        var n = unsafe_alloc[Self.Node](1)
        n.unsafe_write(Self.Node(value^, link))
        return Int(n)

    @staticmethod
    def _free(addr: Int) -> Self.T:
        # UNSAFE: addr must be a node already unlinked from the list
        var n = Self._at(addr)
        var value = n.unsafe_take_pointee().take_value()
        n.unsafe_free()
        return value^

    def _walk(self, from_head: Bool, steps: Int) -> Tuple[Int, Int]:
        """The addresses (prev, cur) after `steps` steps from the head or
        the tail; prev is 0 at the start."""
        var prev = 0
        var cur = self.head if from_head else self.tail
        for _ in range(steps):
            var next = Self._at(cur)[].link ^ prev
            prev = cur
            cur = next
        return (prev, cur)

    def _locate(self, i: Int) -> Tuple[Int, Int, Int]:
        """The addresses (prev, cur, next) of the node at index i, walking
        from the nearer end."""
        if i <= self.size // 2:
            var w = self._walk(True, i)
            return (w[0], w[1], Self._at(w[1])[].link ^ w[0])
        var w = self._walk(False, self.size - 1 - i)
        # walking from the tail, "prev" is the next node
        return (Self._at(w[1])[].link ^ w[0], w[1], w[0])

    def push_front(mut self, var value: Self.T):
        var a = Self._new(value^, self.head)
        if self.head != 0:
            Self._at(self.head)[].link ^= a  # its prev was 0
        else:
            self.tail = a
        self.head = a
        self.size += 1

    def push_back(mut self, var value: Self.T):
        var a = Self._new(value^, self.tail)
        if self.tail != 0:
            Self._at(self.tail)[].link ^= a  # its next was 0
        else:
            self.head = a
        self.tail = a
        self.size += 1

    def pop_front(mut self) -> Optional[Self.T]:
        if self.head == 0:
            return None
        var a = self.head
        var next = Self._at(a)[].link
        if next != 0:
            Self._at(next)[].link ^= a
        else:
            self.tail = 0
        self.head = next
        self.size -= 1
        return Self._free(a)

    def pop_back(mut self) -> Optional[Self.T]:
        if self.tail == 0:
            return None
        var a = self.tail
        var prev = Self._at(a)[].link
        if prev != 0:
            Self._at(prev)[].link ^= a
        else:
            self.head = 0
        self.tail = prev
        self.size -= 1
        return Self._free(a)

    def insert(mut self, i: Int, var value: Self.T):
        """Insert before index i (0 <= i <= len)."""
        debug_assert(0 <= i <= self.size, "XorList.insert: bad index")
        if i == 0:
            self.push_front(value^)
            return
        if i == self.size:
            self.push_back(value^)
            return
        var at = self._locate(i)
        var prev = at[0]
        var cur = at[1]
        var a = Self._new(value^, prev ^ cur)
        Self._at(prev)[].link ^= cur ^ a
        Self._at(cur)[].link ^= prev ^ a
        self.size += 1

    def remove(mut self, i: Int) -> Self.T:
        """Remove and return the value at index i (0 <= i < len)."""
        debug_assert(0 <= i < self.size, "XorList.remove: bad index")
        var at = self._locate(i)
        var prev = at[0]
        var cur = at[1]
        var next = at[2]
        if prev != 0:
            Self._at(prev)[].link ^= cur ^ next
        else:
            self.head = next
        if next != 0:
            Self._at(next)[].link ^= cur ^ prev
        else:
            self.tail = prev
        self.size -= 1
        return Self._free(cur)

    def __getitem__(self, i: Int) -> Self.T:
        debug_assert(0 <= i < self.size, "XorList: bad index")
        return Self._at(self._locate(i)[1])[].value.copy()

    def reverse(mut self):
        """O(1): the links read the same either way."""
        swap(self.head, self.tail)

    def extend(mut self, var other: Self):
        """Append `other`'s nodes in O(1)."""
        if other.size == 0:
            return
        if self.size == 0:
            swap(self, other)
            return
        Self._at(self.tail)[].link ^= other.head
        Self._at(other.head)[].link ^= self.tail
        self.tail = other.tail
        self.size += other.size
        other.head = 0  # the nodes are ours now; other frees nothing
        other.tail = 0
        other.size = 0

    def copy(self) -> Self:
        return Self(self.to_list())

    def to_list(self, reverse: Bool = False) -> List[Self.T]:
        """The values from head to tail, or tail to head."""
        var out = List[Self.T]()
        var prev = 0
        var cur = self.tail if reverse else self.head
        while cur != 0 and len(out) <= self.size:
            out.append(Self._at(cur)[].value.copy())
            var next = Self._at(cur)[].link ^ prev
            prev = cur
            cur = next
        return out^

    def check_links(self) raises:
        """Raise unless walking from either end visits `size` nodes and
        stops at the other end."""
        if (self.head == 0) != (self.size == 0) or (self.tail == 0) != (
            self.size == 0
        ):
            raise Error("head, tail, and size disagree about emptiness")
        for from_head in [True, False]:
            var w = self._walk(from_head, self.size)
            if w[1] != 0:
                raise Error("a walk goes past ", self.size, " nodes")
            if w[0] != (self.tail if from_head else self.head):
                raise Error("a walk doesn't end at the other end")


# ---- commands, checked against a List


def check(sut: XorList[Int], model: List[Int]) raises:
    sut.check_links()
    assert_equal(len(sut), len(model), "len")
    assert_true(sut.to_list() == model, "forward")
    var backward = model.copy()
    backward.reverse()
    assert_true(sut.to_list(reverse=True) == backward, "backward")


comptime IntList = XorList[Int]


@fieldwise_init
struct PushFront(Command):
    comptime Model = List[Int]
    comptime Sut = IntList
    var value: Int

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 99)))

    def next_state(self, mut model: List[Int]) raises:
        model.insert(0, self.value)

    def run(self, model: List[Int], mut sut: IntList) raises:
        sut.push_front(self.value)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("push_front(", self.value, ")")


@fieldwise_init
struct PushBack(Command):
    comptime Model = List[Int]
    comptime Sut = IntList
    var value: Int

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 99)))

    def next_state(self, mut model: List[Int]) raises:
        model.append(self.value)

    def run(self, model: List[Int], mut sut: IntList) raises:
        sut.push_back(self.value)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("push_back(", self.value, ")")


@fieldwise_init
struct Pop(Command):
    comptime Model = List[Int]
    comptime Sut = IntList
    var front: Bool

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self(data.draw(booleans()))

    def next_state(self, mut model: List[Int]) raises:
        if len(model) > 0:
            _ = model.pop(0 if self.front else len(model) - 1)

    def run(self, model: List[Int], mut sut: IntList) raises:
        var got = sut.pop_front() if self.front else sut.pop_back()
        var expected: Optional[Int] = None
        if len(model) > 0:
            expected = model[0] if self.front else model[len(model) - 1]
        assert_equal(got, expected, "popped")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("pop_front()" if self.front else "pop_back()")


@fieldwise_init
struct Insert(Command):
    comptime Model = List[Int]
    comptime Sut = IntList
    var index: Int
    var value: Int

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self(
            data.draw(integers(0, len(model))), data.draw(integers(0, 99))
        )

    def precondition(self, model: List[Int]) raises -> Bool:
        return self.index <= len(model)

    def next_state(self, mut model: List[Int]) raises:
        model.insert(self.index, self.value)

    def run(self, model: List[Int], mut sut: IntList) raises:
        sut.insert(self.index, self.value)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("insert(", self.index, ", ", self.value, ")")


@fieldwise_init
struct Remove(Command):
    comptime Model = List[Int]
    comptime Sut = IntList
    var index: Int

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        if len(model) == 0:
            return Self(0)  # rejected by precondition
        return Self(data.draw(integers(0, len(model) - 1)))

    def precondition(self, model: List[Int]) raises -> Bool:
        return self.index < len(model)

    def next_state(self, mut model: List[Int]) raises:
        _ = model.pop(self.index)

    def run(self, model: List[Int], mut sut: IntList) raises:
        assert_equal(sut[self.index], model[self.index], "getitem")
        assert_equal(sut.remove(self.index), model[self.index], "removed")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("remove(", self.index, ")")


@fieldwise_init
struct Reverse(Command):
    comptime Model = List[Int]
    comptime Sut = IntList

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: List[Int]) raises:
        model.reverse()

    def run(self, model: List[Int], mut sut: IntList) raises:
        sut.reverse()
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("reverse()")


@fieldwise_init
struct Extend(Command):
    """Append a new list, built in either direction (so its nodes' links
    were made by push_back or by push_front then reverse)."""

    comptime Model = List[Int]
    comptime Sut = IntList
    var values: List[Int]
    var reversed: Bool

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self(
            data.draw(lists(integers(0, 99), max_size=4)),
            data.draw(booleans()),
        )

    def next_state(self, mut model: List[Int]) raises:
        model.extend(self.values.copy())

    def run(self, model: List[Int], mut sut: IntList) raises:
        var other = IntList()
        if self.reversed:
            for v in self.values:
                other.push_front(v)
            other.reverse()
        else:
            other = IntList(self.values)
        sut.extend(other^)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("extend(", self.values)
        if self.reversed:
            writer.write(", reversed")
        writer.write(")")


@fieldwise_init
struct CopyThenChange(Command):
    """A copy has its own nodes: changing it leaves the original alone."""

    comptime Model = List[Int]
    comptime Sut = IntList

    @staticmethod
    def generate(model: List[Int], mut data: ConjectureData) raises -> Self:
        return Self()

    def run(self, model: List[Int], mut sut: IntList) raises:
        var c = sut.copy()
        c.push_back(-1)
        c.reverse()
        check(sut, model)
        var expected = model.copy()
        expected.append(-1)
        expected.reverse()
        check(c, expected)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("copy_then_change()")


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_list(mut data: ConjectureData) raises:
        var start = data.draw(lists(integers(0, 99), max_size=5))
        var sut = IntList(start)
        run_commands[
            PushFront,
            PushBack,
            Pop,
            Insert,
            Remove,
            Reverse,
            Extend,
            CopyThenChange,
        ](start, sut, data)

    given_data(matches_list, settings)
    print("matches a List: passed")

    # Moving the list doesn't move its nodes.
    def survives_a_move(xs: List[Int]) raises:
        var a = IntList(xs)
        var b = a^
        check(b, xs)

    given(lists(integers()), survives_a_move, settings)
    print("survives a move: passed")

    # Heap-allocated values are freed on pop, remove, and destruction (the
    # AddressSanitizer build checks for leaks).
    def owns_its_values(xs: List[String], i: Int) raises:
        var a = XorList[String](xs)
        a.reverse()
        if len(xs) > 0:
            var k = i % len(xs)
            assert_equal(a.remove(k), xs[len(xs) - 1 - k])
        a.extend(XorList[String](xs))
        _ = a.pop_back()
        _ = a.pop_front()

    given(lists(text(max_size=20)), integers(0, 100), owns_its_values, settings)
    print("owns its values: passed")
