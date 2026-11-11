# An LRU (least recently used) cache, after LeetCode 146, and properties
# that check it against a simple model.
#
# The cache follows the usual C++ design: a hash map from each key to a
# node in a doubly linked list kept in recency order, so that get and put
# are O(1). Here the "pointers" are indices into lists, and the list is
# circular with one sentinel (slot 0) standing for both C++'s head and
# tail. An evicted node's slot is reused for the new key, so the cache
# never holds more than `capacity` nodes.
#
#   pixi run mojo run -I . examples/lru_cache.mojo

from std.testing import assert_equal, assert_true

from proptest import *


# ---- the cache


struct LRUCache[
    K: KeyElement & Copyable & Deinitable, V: Copyable & Deinitable
](Movable, Sized):
    """A map holding at most `capacity` entries, evicting the least
    recently used one when full."""

    var capacity: Int
    var slots: Dict[Self.K, Int]
    """Each key's slot. Slot i (from 1) holds keys[i - 1], values[i - 1]."""
    var keys: List[Self.K]
    var values: List[Self.V]
    var prev: List[Int]
    """The list links. Slot 0 is the sentinel: next[0] is the most
    recently used slot and prev[0] the least."""
    var next: List[Int]

    def __init__(out self, capacity: Int):
        debug_assert(capacity > 0, "LRUCache: capacity must be positive")
        self.capacity = capacity
        self.slots = {}
        self.keys = []
        self.values = []
        self.prev = [0]
        self.next = [0]

    def __len__(self) -> Int:
        return len(self.slots)

    def _unlink(mut self, i: Int):
        var p = self.prev[i]
        var n = self.next[i]
        self.next[p] = n
        self.prev[n] = p

    def _push_front(mut self, i: Int):
        var first = self.next[0]
        self.next[i] = first
        self.prev[i] = 0
        self.next[0] = i
        self.prev[first] = i

    def get(mut self, key: Self.K) -> Optional[Self.V]:
        """The key's value, marking the key as most recently used, or None
        if the cache doesn't hold it."""
        var found = self.slots.get(key)
        if not found:
            return None
        var i = found.value()
        self._unlink(i)
        self._push_front(i)
        return self.values[i - 1].copy()

    def put(mut self, key: Self.K, var value: Self.V):
        """Set the key's value and mark it most recently used, evicting the
        least recently used key if the cache is full."""
        var found = self.slots.get(key)
        if found:
            var i = found.value()
            self.values[i - 1] = value^
            self._unlink(i)
            self._push_front(i)
            return
        var i: Int
        if len(self.slots) == self.capacity:
            i = self.prev[0]  # evict the least recently used, reusing its slot
            _ = self.slots.pop(self.keys[i - 1], 0)
            self._unlink(i)
            self.keys[i - 1] = key.copy()
            self.values[i - 1] = value^
        else:
            self.keys.append(key.copy())
            self.values.append(value^)
            self.prev.append(0)
            self.next.append(0)
            i = len(self.keys)
        self.slots[key.copy()] = i
        self._push_front(i)

    def keys_by_recency(self) -> List[Self.K]:
        """The keys, most recently used first."""
        var out = List[Self.K]()
        var i = self.next[0]
        while i != 0:
            out.append(self.keys[i - 1].copy())
            i = self.next[i]
        return out^


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


# ---- commands: one struct per operation


@fieldwise_init
struct Put(Command):
    comptime Model = LruModel
    comptime Sut = IntCache
    var key: Int
    var value: Int

    @staticmethod
    def generate(model: LruModel, mut data: ConjectureData) raises -> Self:
        # few keys, so that programs revisit keys and fill the cache
        return Self(data.draw(integers(0, 9)), data.draw(integers(0, 99)))

    def next_state(self, mut model: LruModel) raises:
        model.put(self.key, self.value)

    def run(self, model: LruModel, mut sut: IntCache) raises:
        sut.put(self.key, self.value)
        var after = model.copy()
        self.next_state(after)
        assert_equal(len(sut), len(after.keys), "wrong size")

    def write_to(self, mut writer: Some[Writer]):
        writer.write("put(", self.key, ", ", self.value, ")")


@fieldwise_init
struct Get(Command):
    comptime Model = LruModel
    comptime Sut = IntCache
    var key: Int

    @staticmethod
    def generate(model: LruModel, mut data: ConjectureData) raises -> Self:
        # usually a key the cache should hold, sometimes any key
        if len(model.keys) > 0 and data.draw(booleans()):
            return Self(data.draw(sampled_from(model.keys.copy())))
        return Self(data.draw(integers(0, 9)))

    def next_state(self, mut model: LruModel) raises:
        _ = model.get(self.key)

    def run(self, model: LruModel, mut sut: IntCache) raises:
        var before = model.copy()
        var expected = before.get(self.key)
        assert_equal(sut.get(self.key), expected, String("get(", self.key, ")"))

    def write_to(self, mut writer: Some[Writer]):
        writer.write("get(", self.key, ")")


# ---- properties


def leetcode_example() raises:
    # LeetCode's example 1; get returns -1 for a missing key there
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


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    leetcode_example()
    print("LeetCode example: passed")

    # Model-based: random programs of puts and gets, on caches of random
    # capacity, checked against LruModel after every step. At the end the
    # recency order must match the model's too.
    def matches_model(mut data: ConjectureData) raises:
        var capacity = data.draw(integers(1, 5))
        var model = LruModel(capacity)
        var cache = IntCache(capacity)
        var program = data.draw(commands[Put, Get](model))
        program.run(model.copy(), cache)
        program.apply_all(model)
        assert_true(cache.keys_by_recency() == model.keys, "recency order")
        assert_true(len(cache.keys) <= capacity, "too many nodes")

    given_data(matches_model, settings)
    print("matches the model: passed")

    # Without a model: after a run of puts, the cache holds exactly the
    # last `capacity` distinct keys put, each with its last value.
    def keeps_the_most_recent(capacity: Int, keys: List[Int]) raises:
        var cache = IntCache(capacity)
        for i in range(len(keys)):
            cache.put(keys[i], i)
        var kept = 0
        var seen = List[Int]()
        var j = len(keys) - 1
        while j >= 0:
            var k = keys[j]
            if k not in seen:
                seen.append(k)
                if len(seen) <= capacity:
                    kept += 1
                    assert_equal(cache.get(k).or_else(-1), j)
                else:
                    assert_true(not cache.get(k), "evicted key still held")
            j -= 1
        assert_equal(len(cache), kept)

    given(
        integers(1, 5), lists(integers(0, 9)), keeps_the_most_recent, settings
    )
    print("keeps the most recent keys: passed")

    # The cache is generic: string keys and list values.
    def put_then_get(key: String, value: List[Int]) raises:
        var cache = LRUCache[String, List[Int]](1)
        cache.put("other", [])
        cache.put(key, value.copy())
        assert_true(cache.get(key).value() == value)
        assert_equal(len(cache), 1)

    given(text(), lists(integers()), put_then_get, settings)
    print("generic keys and values: passed")
