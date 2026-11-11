# The LRU cache of lru_cache.mojo (LeetCode 146), written the direct C++
# way: each entry is a heap-allocated node, linked to its neighbors by
# pointers.
#
# A doubly linked list has two pointers to every node, so it can't be built
# from owning pointers alone. Rust's options are Rc<RefCell<Node>> with
# Weak back links, or raw pointers in `unsafe`. Mojo has no weak pointer,
# so this uses raw pointers (Pointer[Node, MutUntrackedOrigin], which the
# borrow checker doesn't track) and keeps the unsafety in one place:
#
# - Only LRUCache allocates, links, and frees nodes, in the methods marked
#   UNSAFE below. Pointers never leave the struct: get returns a copy of
#   the value.
# - LRUCache is Movable but not Copyable. Moving it doesn't move the nodes,
#   and a copy would share them (and free them twice).
# - Evicting reuses the evicted node, and __deinit__ frees every node.
#   (The C++ version allocates a node per put and never frees one.)
# - check_links() verifies every link, so the tests check the structure as
#   well as the behavior. Building the tests with AddressSanitizer checks
#   for use after free, double frees, and leaks:
#
#   pixi run mojo run -I . examples/lru_cache_pointers.mojo
#   pixi run mojo build -I . --sanitize address -o lru examples/lru_cache_pointers.mojo && ./lru

from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_true

from proptest import *


# ---- the cache


struct Node[K: KeyElement & Copyable & Deinitable, V: Copyable & Deinitable](
    Movable
):
    var key: Self.K
    var value: Self.V
    var prev: Optional[Pointer[Self, MutUntrackedOrigin]]
    """The more recently used neighbor; None for the head."""
    var next: Optional[Pointer[Self, MutUntrackedOrigin]]
    """The less recently used neighbor; None for the tail."""

    def __init__(out self, var key: Self.K, var value: Self.V):
        self.key = key^
        self.value = value^
        self.prev = None
        self.next = None


struct LRUCache[
    K: KeyElement & Copyable & Deinitable, V: Copyable & Deinitable
](Movable, Sized):
    """A map holding at most `capacity` entries, evicting the least
    recently used one when full."""

    comptime NodePtr = Pointer[Node[Self.K, Self.V], MutUntrackedOrigin]

    var capacity: Int
    var nodes: Dict[Self.K, Self.NodePtr]
    var head: Optional[Self.NodePtr]
    """The most recently used node."""
    var tail: Optional[Self.NodePtr]
    """The least recently used node, evicted next."""

    def __init__(out self, capacity: Int):
        debug_assert(capacity > 0, "LRUCache: capacity must be positive")
        self.capacity = capacity
        self.nodes = {}
        self.head = None
        self.tail = None

    def __deinit__(deinit self):
        # UNSAFE: frees every node; nothing may use them afterwards
        var p = self.head
        while p:
            var n = p.value()
            p = n[].next
            _ = n.unsafe_take_pointee()
            n.unsafe_free()

    def __len__(self) -> Int:
        return len(self.nodes)

    def _unlink(mut self, n: Self.NodePtr):
        # UNSAFE: n must be a live node in this list
        var p = n[].prev
        var q = n[].next
        if p:
            p.value()[].next = q
        else:
            self.head = q
        if q:
            q.value()[].prev = p
        else:
            self.tail = p
        n[].prev = None
        n[].next = None

    def _push_front(mut self, n: Self.NodePtr):
        # UNSAFE: n must be a live node not in the list
        n[].next = self.head
        if self.head:
            self.head.value()[].prev = n
        else:
            self.tail = n
        self.head = n

    def get(mut self, key: Self.K) -> Optional[Self.V]:
        """The key's value, marking the key as most recently used, or None
        if the cache doesn't hold it."""
        var found = self.nodes.get(key)
        if not found:
            return None
        var n = found.value()
        self._unlink(n)
        self._push_front(n)
        return n[].value.copy()

    def put(mut self, key: Self.K, var value: Self.V):
        """Set the key's value and mark it most recently used, evicting the
        least recently used key if the cache is full."""
        var found = self.nodes.get(key)
        if found:
            var n = found.value()
            n[].value = value^
            self._unlink(n)
            self._push_front(n)
            return
        var n: Self.NodePtr
        if len(self.nodes) == self.capacity:
            n = (
                self.tail.value()
            )  # evict the least recently used, reusing its node
            self._unlink(n)
            _ = self.nodes.pop(n[].key, n)
            n[].key = key.copy()
            n[].value = value^
        else:
            # UNSAFE: a new node, owned by the list until __deinit__
            n = unsafe_alloc[Node[Self.K, Self.V]](1)
            n.unsafe_write(Node(key.copy(), value^))
        self.nodes[key.copy()] = n
        self._push_front(n)

    def keys_by_recency(self) -> List[Self.K]:
        """The keys, most recently used first."""
        var out = List[Self.K]()
        var p = self.head
        while p:
            out.append(p.value()[].key.copy())
            p = p.value()[].next
        return out^

    def check_links(self) raises:
        """Raise if the list or the map is inconsistent: every node's
        neighbors must point back at it, the ends must be the head and the
        tail, and the map must hold exactly the nodes in the list."""
        var count = 0
        var prev: Optional[Self.NodePtr] = None
        var p = self.head
        while p:
            var n = p.value()
            count += 1
            if count > len(self.nodes):
                raise Error("the list is longer than the map (or has a cycle)")
            if n[].prev != prev:
                raise Error("a prev link doesn't point back")
            var mapped = self.nodes.get(n[].key)
            if not mapped or mapped.value() != n:
                raise Error("the map doesn't point at a node in the list")
            prev = n
            p = n[].next
        if count != len(self.nodes):
            raise Error("the map holds nodes that aren't in the list")
        if self.tail != prev:
            raise Error("the tail isn't the last node")
        if len(self.nodes) > self.capacity:
            raise Error("over capacity")


comptime IntCache = LRUCache[Int, Int]


# ---- a model: the entries in a plain list, most recently used first


@fieldwise_init
struct LruModel(Copyable, Writable):
    var capacity: Int
    var keys: List[Int]
    var values: List[Int]

    def __init__(out self, capacity: Int):
        self = Self(capacity, [], [])

    def find(self, key: Int) -> Int:
        for i in range(len(self.keys)):
            if self.keys[i] == key:
                return i
        return -1

    def touch(mut self, i: Int):
        self.keys.insert(0, self.keys.pop(i))
        self.values.insert(0, self.values.pop(i))

    def get(mut self, key: Int) -> Optional[Int]:
        var i = self.find(key)
        if i < 0:
            return None
        self.touch(i)
        return self.values[0]

    def put(mut self, key: Int, value: Int):
        var i = self.find(key)
        if i >= 0:
            self.values[i] = value
            self.touch(i)
            return
        if len(self.keys) == self.capacity:
            _ = self.keys.pop()
            _ = self.values.pop()
        self.keys.insert(0, key)
        self.values.insert(0, value)


# ---- commands, which also check the links after every step


@fieldwise_init
struct Put(Command):
    comptime Model = LruModel
    comptime Sut = IntCache
    var key: Int
    var value: Int

    @staticmethod
    def generate(model: LruModel, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 9)), data.draw(integers(0, 99)))

    def next_state(self, mut model: LruModel) raises:
        model.put(self.key, self.value)

    def run(self, model: LruModel, mut sut: IntCache) raises:
        sut.put(self.key, self.value)
        sut.check_links()
        var after = model.copy()
        self.next_state(after)
        assert_true(sut.keys_by_recency() == after.keys, "recency order")

    def write_to(self, mut writer: Some[Writer]):
        writer.write("put(", self.key, ", ", self.value, ")")


@fieldwise_init
struct Get(Command):
    comptime Model = LruModel
    comptime Sut = IntCache
    var key: Int

    @staticmethod
    def generate(model: LruModel, mut data: ConjectureData) raises -> Self:
        if len(model.keys) > 0 and data.draw(booleans()):
            return Self(data.draw(sampled_from(model.keys.copy())))
        return Self(data.draw(integers(0, 9)))

    def next_state(self, mut model: LruModel) raises:
        _ = model.get(self.key)

    def run(self, model: LruModel, mut sut: IntCache) raises:
        var after = model.copy()
        var expected = after.get(self.key)
        assert_equal(sut.get(self.key), expected, String("get(", self.key, ")"))
        sut.check_links()
        assert_true(sut.keys_by_recency() == after.keys, "recency order")

    def write_to(self, mut writer: Some[Writer]):
        writer.write("get(", self.key, ")")


# ---- properties


def leetcode_example() raises:
    var c = IntCache(2)
    c.put(1, 1)
    c.put(2, 2)
    assert_equal(c.get(1).or_else(-1), 1)
    c.put(3, 3)  # evicts 2
    assert_equal(c.get(2).or_else(-1), -1)
    c.put(4, 4)  # evicts 1
    assert_equal(c.get(1).or_else(-1), -1)
    assert_equal(c.get(3).or_else(-1), 3)
    assert_equal(c.get(4).or_else(-1), 4)
    c.check_links()


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    leetcode_example()
    print("LeetCode example: passed")

    # Model-based: each step checks the result, the links, and the
    # recency order against the model.
    def matches_model(mut data: ConjectureData) raises:
        var capacity = data.draw(integers(1, 5))
        var cache = IntCache(capacity)
        run_commands[Put, Get](LruModel(capacity), cache, data)

    given_data(matches_model, settings)
    print("matches the model: passed")

    # Moving the cache keeps its nodes where they are.
    def survives_a_move(capacity: Int, keys: List[Int]) raises:
        var a = IntCache(capacity)
        for i in range(len(keys)):
            a.put(keys[i], i)
        var order = a.keys_by_recency()
        var b = a^
        b.check_links()
        assert_true(b.keys_by_recency() == order)

    given(integers(1, 5), lists(integers(0, 9)), survives_a_move, settings)
    print("survives a move: passed")

    # Heap-allocated keys and values are freed on eviction, overwrite, and
    # destruction (the AddressSanitizer build checks for leaks).
    def owns_its_entries(keys: List[String]) raises:
        var cache = LRUCache[String, List[String]](2)
        for k in keys:
            cache.put(k, [k, k])
            cache.check_links()
            assert_true(cache.get(k).value() == [k, k])

    given(lists(text(max_size=20)), owns_its_entries, settings)
    print("owns its entries: passed")
