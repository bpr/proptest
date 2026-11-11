# A skip list (Pugh, 1990) with spans, as in Redis's sorted sets. Every
# node is on the bottom list, which is sorted by key; a node of level L is
# also on lists 1 .. L-1 above it, each a sparser express lane over the one
# below. A search starts on the top lane and drops down a lane whenever the
# next key is too big, which takes O(log n) expected steps when levels are
# random with P(level > L) = 4^-L.
#
# Each forward link also records its span: how many bottom-list steps it
# skips. Adding up spans along a search gives an element's rank, and
# following them finds the element at an index, both in O(log n). The
# bottom list is doubly linked, so it can be walked backward too.
#
# Nodes have different numbers of links, so each is one raw allocation of
# its own size (C's "flexible array member"): the key, the value (a
# String, written into the raw bytes), the level, the backward link, and
# then `level` pairs of (next, span). Links are addresses, 0 for none.
#
# In the tests, the test case chooses each node's level, so shrinking
# works on levels too, and the model (a sorted list of key, value, and
# level) determines the whole structure. After every command they check
# that every lane is the subsequence of the lane below holding the nodes
# tall enough for it, that every span is exact, that each node has the
# model's level, and that the backward links mirror the forward ones.
#
#   pixi run mojo run -I . examples/skip_list.mojo
#   pixi run mojo build -I . --sanitize address -o skip examples/skip_list.mojo && ./skip
#
# Run with PROPTEST_TIMEOUT=1000 so that crashes and hangs shrink too.

from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.sys import size_of
from std.testing import assert_equal, assert_false, assert_true

from proptest import *


# ---- the skip list

comptime BytePtr = Pointer[UInt8, MutUntrackedOrigin]
comptime MAX_LEVEL = 8

# A node's layout, in bytes.
comptime KEY = 0
comptime VALUE = 8
comptime LEVEL = VALUE + size_of[String]()
comptime BACKWARD = LEVEL + 8
comptime LINKS = BACKWARD + 8
comptime LINK_SIZE = 16
"""Each level's link: the next node's address, then the span."""


def node_size(level: Int) -> Int:
    return LINKS + LINK_SIZE * level


struct SkipList(Movable, Sized):
    """An ordered map from Int to String."""

    var head: Int
    """A node of MAX_LEVEL links and no key or value."""
    var tail: Int
    """The last node, or 0."""
    var level: Int
    """The number of lanes in use (at least 1)."""
    var length: Int
    var rng: UInt64
    """For insert's random levels."""

    def __init__(out self, seed: UInt64 = 0x9E3779B97F4A7C15):
        # UNSAFE: the head has links and a level, but no key or value
        var h = unsafe_alloc[UInt8](node_size(MAX_LEVEL), alignment=8)
        self.head = Int(h)
        Self._word(self.head, LEVEL)[] = MAX_LEVEL
        Self._word(self.head, BACKWARD)[] = 0
        for i in range(MAX_LEVEL):
            Self._set_next(self.head, i, 0)
            Self._set_span(self.head, i, 0)
        self.tail = 0
        self.level = 1
        self.length = 0
        self.rng = seed | 1

    def __deinit__(deinit self):
        # UNSAFE: frees every node and its value, then the head
        var x = Self._next(self.head, 0)
        while x != 0:
            var next = Self._next(x, 0)
            _ = Self._free(x)
            x = next
        BytePtr(unsafe_from_address=self.head).unsafe_free()

    def __len__(self) -> Int:
        return self.length

    # -- raw node fields

    @staticmethod
    def _word(n: Int, offset: Int) -> Pointer[Int, MutUntrackedOrigin]:
        return BytePtr(unsafe_from_address=n + offset).unsafe_bitcast[Int]()

    @staticmethod
    def key(n: Int) -> Int:
        return Self._word(n, KEY)[]

    @staticmethod
    def _value(n: Int) -> Pointer[String, MutUntrackedOrigin]:
        return BytePtr(unsafe_from_address=n + VALUE).unsafe_bitcast[String]()

    @staticmethod
    def node_level(n: Int) -> Int:
        return Self._word(n, LEVEL)[]

    @staticmethod
    def _backward(n: Int) -> Int:
        return Self._word(n, BACKWARD)[]

    @staticmethod
    def _next(n: Int, i: Int) -> Int:
        return Self._word(n, LINKS + LINK_SIZE * i)[]

    @staticmethod
    def _set_next(n: Int, i: Int, to: Int):
        Self._word(n, LINKS + LINK_SIZE * i)[] = to

    @staticmethod
    def _span(n: Int, i: Int) -> Int:
        return Self._word(n, LINKS + LINK_SIZE * i + 8)[]

    @staticmethod
    def _set_span(n: Int, i: Int, span: Int):
        Self._word(n, LINKS + LINK_SIZE * i + 8)[] = span

    @staticmethod
    def _new(key: Int, var value: String, level: Int) -> Int:
        # UNSAFE: a node of `level` links, all null; the caller links it
        var p = unsafe_alloc[UInt8](node_size(level), alignment=8)
        var n = Int(p)
        Self._word(n, KEY)[] = key
        Self._value(n).unsafe_write(value^)
        Self._word(n, LEVEL)[] = level
        Self._word(n, BACKWARD)[] = 0
        for i in range(level):
            Self._set_next(n, i, 0)
            Self._set_span(n, i, 0)
        return n

    @staticmethod
    def _free(n: Int) -> String:
        # UNSAFE: n must already be unlinked
        var value = Self._value(n).unsafe_take_pointee()
        BytePtr(unsafe_from_address=n).unsafe_free()
        return value^

    # -- searching

    def _search(
        self,
        key: Int,
        mut update: Array[Int, MAX_LEVEL],
        mut rank: Array[Int, MAX_LEVEL],
    ):
        """For each lane i, update[i] is the last node with a key < key, and
        rank[i] is its index (the head's is 0)."""
        var x = self.head
        var i = self.level - 1
        while i >= 0:
            rank[i] = 0 if i == self.level - 1 else rank[i + 1]
            while Self._next(x, i) != 0 and Self.key(Self._next(x, i)) < key:
                rank[i] += Self._span(x, i)
                x = Self._next(x, i)
            update[i] = x
            i -= 1

    def _find(self, key: Int) -> Int:
        var update = Array[Int, MAX_LEVEL](fill=0)
        var rank = Array[Int, MAX_LEVEL](fill=0)
        self._search(key, update, rank)
        var x = Self._next(update[0], 0)
        return x if x != 0 and Self.key(x) == key else 0

    def get(self, key: Int) -> Optional[String]:
        var x = self._find(key)
        if x == 0:
            return None
        return Self._value(x)[].copy()

    def lower_bound(self, key: Int) -> Optional[Int]:
        """The smallest key >= key."""
        var update = Array[Int, MAX_LEVEL](fill=0)
        var rank = Array[Int, MAX_LEVEL](fill=0)
        self._search(key, update, rank)
        var x = Self._next(update[0], 0)
        return Optional(Self.key(x)) if x != 0 else None

    def rank(self, key: Int) -> Int:
        """The number of keys < key."""
        var update = Array[Int, MAX_LEVEL](fill=0)
        var rank = Array[Int, MAX_LEVEL](fill=0)
        self._search(key, update, rank)
        return rank[0]

    def select(self, index: Int) -> Int:
        """The key at index (0 <= index < len), following spans."""
        debug_assert(0 <= index < self.length, "SkipList.select: bad index")
        var x = self.head
        var traversed = 0
        var i = self.level - 1
        while i >= 0:
            while (
                Self._next(x, i) != 0
                and traversed + Self._span(x, i) <= index + 1
            ):
                traversed += Self._span(x, i)
                x = Self._next(x, i)
            if traversed == index + 1:
                return Self.key(x)
            i -= 1
        return Self.key(x)

    # -- changing

    def random_level(mut self) -> Int:
        """1 + the number of 1-in-4 events in a row (xorshift64)."""
        var level = 1
        while level < MAX_LEVEL:
            self.rng ^= self.rng << 13
            self.rng ^= self.rng >> 7
            self.rng ^= self.rng << 17
            if self.rng & 3 != 0:
                break
            level += 1
        return level

    def insert(mut self, key: Int, var value: String) -> Optional[String]:
        return self.insert(key, value^, self.random_level())

    def insert(
        mut self, key: Int, var value: String, level: Int
    ) -> Optional[String]:
        """Map key to value, returning the old value if there was one. A new
        node gets `level` lanes (1 <= level <= MAX_LEVEL); an existing one
        keeps its own."""
        var update = Array[Int, MAX_LEVEL](fill=0)
        var rank = Array[Int, MAX_LEVEL](fill=0)
        self._search(key, update, rank)
        var found = Self._next(update[0], 0)
        if found != 0 and Self.key(found) == key:
            var old = Self._value(found)[].copy()
            Self._value(found)[] = value^
            return old^
        if level > self.level:
            for i in range(self.level, level):
                rank[i] = 0
                update[i] = self.head
                Self._set_span(self.head, i, self.length)
            self.level = level
        # UNSAFE: links x into lanes 0 .. level-1 after update[i], and
        # splits the spans it lands in
        var x = Self._new(key, value^, level)
        for i in range(level):
            Self._set_next(x, i, Self._next(update[i], i))
            Self._set_next(update[i], i, x)
            Self._set_span(x, i, Self._span(update[i], i) - (rank[0] - rank[i]))
            Self._set_span(update[i], i, rank[0] - rank[i] + 1)
        # the links over x, in the lanes above it, skip one more node
        for i in range(level, self.level):
            Self._set_span(update[i], i, Self._span(update[i], i) + 1)
        Self._word(x, BACKWARD)[] = 0 if update[0] == self.head else update[0]
        var after = Self._next(x, 0)
        if after != 0:
            Self._word(after, BACKWARD)[] = x
        else:
            self.tail = x
        self.length += 1
        return None

    def remove(mut self, key: Int) -> Optional[String]:
        """Remove key, returning its value if it was there."""
        var update = Array[Int, MAX_LEVEL](fill=0)
        var rank = Array[Int, MAX_LEVEL](fill=0)
        self._search(key, update, rank)
        var x = Self._next(update[0], 0)
        if x == 0 or Self.key(x) != key:
            return None
        # UNSAFE: unlinks x from every lane, then frees it
        for i in range(self.level):
            if Self._next(update[i], i) == x:
                Self._set_span(
                    update[i],
                    i,
                    Self._span(update[i], i) + Self._span(x, i) - 1,
                )
                Self._set_next(update[i], i, Self._next(x, i))
            else:
                Self._set_span(update[i], i, Self._span(update[i], i) - 1)
        var after = Self._next(x, 0)
        if after != 0:
            Self._word(after, BACKWARD)[] = Self._backward(x)
        else:
            self.tail = Self._backward(x)
        while self.level > 1 and Self._next(self.head, self.level - 1) == 0:
            self.level -= 1
        self.length -= 1
        return Self._free(x)

    # -- whole-list operations

    def copy(self) -> Self:
        """A list of new nodes with the same keys, values, and levels."""
        var out = Self(self.rng)
        var x = Self._next(self.head, 0)
        while x != 0:
            _ = out.insert(
                Self.key(x), Self._value(x)[].copy(), Self.node_level(x)
            )
            x = Self._next(x, 0)
        return out^

    def items(self, reverse: Bool = False) -> List[Tuple[Int, String, Int]]:
        """(key, value, level) for each node, in key order (or reversed,
        walking the backward links)."""
        var out = List[Tuple[Int, String, Int]]()
        var x = self.tail if reverse else Self._next(self.head, 0)
        while x != 0 and len(out) <= self.length:
            out.append(
                (Self.key(x), Self._value(x)[].copy(), Self.node_level(x))
            )
            x = Self._backward(x) if reverse else Self._next(x, 0)
        return out^

    def check(self) raises:
        """Raise unless the bottom lane is sorted with `length` nodes and
        mirrored by the backward links, each lane i holds exactly the nodes
        of level > i in order, every span is exact (a null link's span
        counts the nodes after it), and `level` is the tallest node's."""
        var index = Dict[Int, Int]()  # address -> position (head 0)
        index[self.head] = 0
        var x = Self._next(self.head, 0)
        var prev = 0
        var tallest = 1
        while x != 0:
            if len(index) > self.length:
                raise Error(
                    "the bottom lane has more than ", self.length, " nodes"
                )
            if prev != 0 and not (Self.key(prev) < Self.key(x)):
                raise Error("keys out of order")
            if Self._backward(x) != prev:
                raise Error("a backward link is wrong")
            var level = Self.node_level(x)
            if level < 1 or level > MAX_LEVEL:
                raise Error("a node of level ", level)
            tallest = max(tallest, level)
            index[x] = len(index)
            prev = x
            x = Self._next(x, 0)
        if len(index) - 1 != self.length:
            raise Error(len(index) - 1, " nodes, not ", self.length)
        if self.tail != prev:
            raise Error("the tail isn't the last node")
        if self.level != tallest:
            raise Error(
                "level ", self.level, ", but the tallest node is ", tallest
            )
        for i in range(MAX_LEVEL):
            if i >= self.level:
                if Self._next(self.head, i) != 0:
                    raise Error("the head links lane ", i, " above the level")
                continue
            # lane i must visit exactly the nodes of level > i, in order
            var a = self.head
            var b = Self._next(self.head, 0)
            while True:
                while b != 0 and Self.node_level(b) <= i:
                    b = Self._next(b, 0)
                var n = Self._next(a, i)
                if n != b:
                    raise Error("lane ", i, " skips or adds a node")
                var to = index[n] if n != 0 else self.length + 1
                var span = Self._span(a, i)
                var expected = (
                    to - index[a] if n != 0 else self.length - index[a]
                )
                if span != expected:
                    raise Error(
                        "a span in lane ", i, " is ", span, ", not ", expected
                    )
                if n == 0:
                    break
                a = n
                b = Self._next(b, 0)


# ---- commands, checked against a sorted list


@fieldwise_init
struct Entries(Copyable):
    """The model: keys in order, with their values and levels."""

    var keys: List[Int]
    var values: List[String]
    var levels: List[Int]

    def find(self, key: Int) -> Optional[Int]:
        for i in range(len(self.keys)):
            if self.keys[i] == key:
                return i
        return None

    def rank(self, key: Int) -> Int:
        var i = 0
        while i < len(self.keys) and self.keys[i] < key:
            i += 1
        return i


comptime MAX_KEY = 30


def check(sut: SkipList, model: Entries) raises:
    sut.check()
    assert_equal(len(sut), len(model.keys), "len")
    var forward = sut.items()
    var backward = sut.items(reverse=True)
    var n = len(model.keys)
    assert_equal(len(forward), n, "items")
    assert_equal(len(backward), n, "items reversed")
    for i in range(n):
        assert_equal(forward[i][0], model.keys[i], "key")
        assert_equal(forward[i][1], model.values[i], "value")
        assert_equal(forward[i][2], model.levels[i], "level")
        assert_equal(backward[n - 1 - i][0], model.keys[i], "key, reversed")


@fieldwise_init
struct Insert(Command):
    comptime Model = Entries
    comptime Sut = SkipList
    var key: Int
    var value: Int
    var level: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(
            data.draw(integers(0, MAX_KEY)),
            data.draw(integers(0, 99)),
            data.draw(integers(1, MAX_LEVEL)),
        )

    def next_state(self, mut model: Entries) raises:
        var i = model.find(self.key)
        if i:
            model.values[i.value()] = String("v", self.value)
        else:
            var r = model.rank(self.key)
            model.keys.insert(r, self.key)
            model.values.insert(r, String("v", self.value))
            model.levels.insert(r, self.level)

    def run(self, model: Entries, mut sut: SkipList) raises:
        var expected: Optional[String] = None
        var i = model.find(self.key)
        if i:
            expected = model.values[i.value()]
        assert_equal(
            sut.insert(self.key, String("v", self.value), self.level),
            expected,
            "old value",
        )
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "insert(", self.key, ", v", self.value, ", level=", self.level, ")"
        )


@fieldwise_init
struct Remove(Command):
    comptime Model = Entries
    comptime Sut = SkipList
    var key: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        # usually a key that's there
        if len(model.keys) > 0 and data.draw(integers(0, 3)) > 0:
            return Self(model.keys[data.draw(integers(0, len(model.keys) - 1))])
        return Self(data.draw(integers(0, MAX_KEY)))

    def next_state(self, mut model: Entries) raises:
        var i = model.find(self.key)
        if i:
            _ = model.keys.pop(i.value())
            _ = model.values.pop(i.value())
            _ = model.levels.pop(i.value())

    def run(self, model: Entries, mut sut: SkipList) raises:
        var expected: Optional[String] = None
        var i = model.find(self.key)
        if i:
            expected = model.values[i.value()]
        assert_equal(sut.remove(self.key), expected, "removed value")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("remove(", self.key, ")")


@fieldwise_init
struct Lookup(Command):
    """Look up one key: get, lower_bound, and rank."""

    comptime Model = Entries
    comptime Sut = SkipList
    var key: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_KEY + 1)))

    def run(self, model: Entries, mut sut: SkipList) raises:
        var expected: Optional[String] = None
        var i = model.find(self.key)
        if i:
            expected = model.values[i.value()]
        assert_equal(sut.get(self.key), expected, "get")
        var r = model.rank(self.key)
        assert_equal(sut.rank(self.key), r, "rank")
        var bound: Optional[Int] = None
        if r < len(model.keys):
            bound = model.keys[r]
        assert_equal(sut.lower_bound(self.key), bound, "lower bound")

    def write_to(self, mut writer: Some[Writer]):
        writer.write("lookup(", self.key, ")")


@fieldwise_init
struct Select(Command):
    comptime Model = Entries
    comptime Sut = SkipList
    var index: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        if len(model.keys) == 0:
            return Self(0)  # rejected by precondition
        return Self(data.draw(integers(0, len(model.keys) - 1)))

    def precondition(self, model: Entries) raises -> Bool:
        return self.index < len(model.keys)

    def run(self, model: Entries, mut sut: SkipList) raises:
        assert_equal(sut.select(self.index), model.keys[self.index], "select")

    def write_to(self, mut writer: Some[Writer]):
        writer.write("select(", self.index, ")")


@fieldwise_init
struct CopyThenChange(Command):
    """A copy has its own nodes: changing it leaves the original alone."""

    comptime Model = Entries
    comptime Sut = SkipList

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self()

    def run(self, model: Entries, mut sut: SkipList) raises:
        var c = sut.copy()
        check(c, model)
        _ = c.insert(MAX_KEY + 1, "extra", MAX_LEVEL)
        if len(model.keys) > 0:
            _ = c.remove(model.keys[0])
        c.check()
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("copy_then_change()")


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_a_sorted_list(mut data: ConjectureData) raises:
        var sut = SkipList()
        run_commands[Insert, Remove, Lookup, Select, CopyThenChange](
            Entries([], [], []), sut, data
        )

    given_data(matches_a_sorted_list, settings)
    print("matches a sorted list: passed")

    # With random levels (insert's own), the structure stays sound and
    # every key is found by index.
    def random_levels(keys: List[Int], seed: Int) raises:
        var s = SkipList(UInt64(seed))
        for k in keys:
            _ = s.insert(k, String(k))
        s.check()
        for i in range(len(s)):
            assert_equal(s.rank(s.select(i)), i, "rank(select(i))")
        for k in keys:
            assert_equal(s.get(k), Optional(String(k)))

    given(
        lists(integers(-1000, 1000), max_size=200),
        integers(0, 1 << 30),
        random_levels,
        settings,
    )
    print("random levels: passed")

    # Moving the list doesn't move its nodes.
    def survives_a_move(keys: List[Int]) raises:
        var a = SkipList()
        for k in keys:
            _ = a.insert(k, String(k))
        var b = a^
        b.check()
        assert_equal(len(b.items()), len(b))

    given(lists(integers()), survives_a_move, settings)
    print("survives a move: passed")
