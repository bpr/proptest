# A splay tree (Sleator and Tarjan, 1985): a binary search tree that moves
# every node it touches to the root with a sequence of rotations (a
# "splay"). There's no balance information, yet every operation takes
# O(log n) amortized time.
#
# Every node links to its parent as well as its children, the way a C
# implementation would, so each node has three pointers that must agree:
# x.left.parent == x, and so on. Links are Optional[Pointer], which the
# borrow checker doesn't track. Only SplayTree allocates, links, and frees
# nodes, in the methods marked UNSAFE. It's Movable, not Copyable (a copy
# would share nodes); copy() builds a tree of new nodes with the same shape.
# Nodes also hold the size of their subtree, for select(i) and rank(key).
#
# The tests are model-based, against a sorted list. After every command
# they check every link, the search-tree order, and the subtree sizes, and
# walk the tree in order both ways using only the parent pointers.
#
# A splay that rotates the node up one level at a time ("move to root")
# instead of zig-zig rotations gives a working search tree that is
# O(n) per access in the worst case, which a comparison with a list can't
# see. So the tree can also check the access lemma at the heart of the
# analysis after every splay. With potential
# Phi = sum over nodes of log2(subtree size), splaying x in a tree with
# root t takes
#
#   rotations + Phi(after) - Phi(before) <= 3 (log2 |t| - log2 |x|) + 1
#
# A move-to-root splay breaks it, e.g. at the deepest node of a long path.
# The second property checks the sequential access theorem (Tarjan, 1985):
# accessing every key in order takes O(n) rotations from any starting tree.
#
#   pixi run mojo run -I . examples/splay_tree.mojo
#   pixi run mojo build -I . --sanitize address -o splay examples/splay_tree.mojo && ./splay
#
# A bad link usually makes a walk dereference a freed or garbage address;
# run with PROPTEST_FORK=1 (Settings(fork=True)) so that crashes shrink too.

from std.math import log2
from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_true

from proptest import *


# ---- the tree


struct SplayNode[
    K: Comparable & Copyable & Deinitable, V: Copyable & Deinitable
](Movable):
    var key: Self.K
    var value: Self.V
    var left: Optional[Pointer[Self, MutUntrackedOrigin]]
    var right: Optional[Pointer[Self, MutUntrackedOrigin]]
    var parent: Optional[Pointer[Self, MutUntrackedOrigin]]
    var size: Int
    """The number of nodes in this subtree."""

    def __init__(
        out self,
        var key: Self.K,
        var value: Self.V,
        parent: Optional[Pointer[Self, MutUntrackedOrigin]],
    ):
        self.key = key^
        self.value = value^
        self.left = None
        self.right = None
        self.parent = parent
        self.size = 1

    def take_value(deinit self) -> Self.V:
        return self.value^


struct SplayTree[
    K: Comparable & Copyable & Deinitable, V: Copyable & Deinitable
](Movable, Sized):
    """An ordered map in which every access splays the node it reaches."""

    comptime Node = SplayNode[Self.K, Self.V]
    comptime NodePtr = Pointer[Self.Node, MutUntrackedOrigin]
    comptime Link = Optional[Self.NodePtr]

    var root: Self.Link
    var size: Int
    var rotations: Int
    """Rotations so far."""
    var audit: Bool
    """Check the access lemma on every splay (O(n) each)."""
    var worst_excess: Float64
    """The largest amount by which a splay's amortized cost exceeded the
    access lemma's bound (only with `audit`)."""

    def __init__(out self, audit: Bool = False):
        self.root = None
        self.size = 0
        self.rotations = 0
        self.audit = audit
        self.worst_excess = -1.0

    def __deinit__(deinit self):
        # UNSAFE: frees every node, children first; nothing may use them
        # afterwards
        var cur = self.root
        while cur:
            var n = cur.value()
            if n[].left:
                cur = n[].left
            elif n[].right:
                cur = n[].right
            else:
                var p = n[].parent
                if p:
                    if p.value()[].left == cur:
                        p.value()[].left = None
                    else:
                        p.value()[].right = None
                _ = Self._free(n)
                cur = p

    def __len__(self) -> Int:
        return self.size

    # -- nodes and links

    @staticmethod
    def _new(
        var key: Self.K, var value: Self.V, parent: Self.Link
    ) -> Self.NodePtr:
        # UNSAFE: a new node; the caller must link it into the tree
        var n = unsafe_alloc[Self.Node](1)
        n.unsafe_write(Self.Node(key^, value^, parent))
        return Self.NodePtr(to=n[])

    @staticmethod
    def _free(n: Self.NodePtr) -> Self.V:
        # UNSAFE: n must already be unlinked from the tree
        var value = n.unsafe_take_pointee().take_value()
        n.unsafe_free()
        return value^

    @staticmethod
    def _child(n: Self.NodePtr, right: Bool) -> Self.Link:
        return n[].right if right else n[].left

    @staticmethod
    def _set_child(n: Self.NodePtr, right: Bool, c: Self.Link):
        if right:
            n[].right = c
        else:
            n[].left = c

    @staticmethod
    def _is_right(n: Self.NodePtr, p: Self.NodePtr) -> Bool:
        """Whether n is p's right child."""
        return p[].right == Self.Link(n)

    @staticmethod
    def _size(n: Self.Link) -> Int:
        return n.value()[].size if n else 0

    @staticmethod
    def _extreme(var n: Self.NodePtr, right: Bool) -> Self.NodePtr:
        """The last node going right (or left) from n."""
        while Self._child(n, right):
            n = Self._child(n, right).value()
        return n

    @staticmethod
    def _next(n: Self.NodePtr, right: Bool) -> Self.Link:
        """The in-order successor (or predecessor) of n, found with parent
        links."""
        var c = Self._child(n, right)
        if c:
            return Self._extreme(c.value(), not right)
        var cur = n
        var p = n[].parent
        while p and Self._is_right(cur, p.value()) == right:
            cur = p.value()
            p = cur[].parent
        return p

    # -- splaying

    def _rotate(mut self, x: Self.NodePtr):
        """Rotate x above its parent."""
        # UNSAFE: relinks x, its parent, its grandparent, and one subtree
        var p = x[].parent.value()
        var g = p[].parent
        var right = Self._is_right(x, p)
        var inner = Self._child(x, not right)
        Self._set_child(p, right, inner)
        if inner:
            inner.value()[].parent = p
        if g:
            Self._set_child(g.value(), Self._is_right(p, g.value()), x)
        else:
            self.root = x
        x[].parent = g
        Self._set_child(x, not right, p)
        p[].parent = x
        p[].size = 1 + Self._size(p[].left) + Self._size(p[].right)
        x[].size = 1 + Self._size(x[].left) + Self._size(x[].right)
        self.rotations += 1

    def _splay(mut self, x: Self.NodePtr):
        """Move x to the root."""
        var before = Tuple(0, 0.0)
        var start = self.rotations
        if self.audit:
            before = Self._potential(self.root)
        var x_size = x[].size
        while x[].parent:
            var p = x[].parent.value()
            if not p[].parent:
                self._rotate(x)  # zig
            elif Self._is_right(x, p) == Self._is_right(p, p[].parent.value()):
                self._rotate(p)  # zig-zig
                self._rotate(x)
            else:
                self._rotate(x)  # zig-zag
                self._rotate(x)
        if self.audit:
            var cost = Float64(self.rotations - start)
            var amortized = cost + Self._potential(self.root)[1] - before[1]
            var bound = (
                3.0 * (log2(Float64(before[0])) - log2(Float64(x_size))) + 1.0
            )
            self.worst_excess = max(self.worst_excess, amortized - bound)

    @staticmethod
    def _potential(n: Self.Link) -> Tuple[Int, Float64]:
        """The number of nodes under n, and the sum of log2 of their subtree
        sizes, counted (not read from the size fields)."""
        if not n:
            return (0, 0.0)
        var l = Self._potential(n.value()[].left)
        var r = Self._potential(n.value()[].right)
        var size = l[0] + r[0] + 1
        return (size, l[1] + r[1] + log2(Float64(size)))

    def _find(mut self, key: Self.K) -> Self.Link:
        """The node holding key, splayed to the root; if there's none,
        splays the last node visited."""
        var cur = self.root
        var last = cur
        while cur:
            var n = cur.value()
            if n[].key == key:
                self._splay(n)
                return cur
            last = cur
            cur = Self._child(n, n[].key < key)
        if last:
            self._splay(last.value())
        return None

    # -- the map

    def insert(
        mut self, var key: Self.K, var value: Self.V
    ) -> Optional[Self.V]:
        """Map key to value, returning the old value if there was one."""
        if not self.root:
            self.root = Self._new(key^, value^, None)
            self.size = 1
            return None
        var n = self.root.value()
        while True:
            if n[].key == key:
                var old = n[].value.copy()
                n[].value = value^
                self._splay(n)
                return old^
            var right = n[].key < key
            var c = Self._child(n, right)
            if not c:
                break
            n = c.value()
        # UNSAFE: links a new leaf under n. Its ancestors' sizes are now one
        # too small, but the splay rotates every one of them and recomputes
        # their sizes.
        var leaf = Self._new(key^, value^, n)
        Self._set_child(n, n[].key < leaf[].key, leaf)
        self.size += 1
        self._splay(leaf)
        return None

    def get(mut self, key: Self.K) -> Optional[Self.V]:
        var n = self._find(key)
        if not n:
            return None
        return n.value()[].value.copy()

    def remove(mut self, key: Self.K) -> Optional[Self.V]:
        """Remove key, returning its value if it was there."""
        var found = self._find(key)
        if not found:
            return None
        # UNSAFE: found is the root: join its subtrees, then free it
        var x = found.value()
        var l = x[].left
        var r = x[].right
        if r:
            r.value()[].parent = None
        if not l:
            self.root = r
        else:
            l.value()[].parent = None
            self.root = l
            var m = Self._extreme(l.value(), right=True)
            self._splay(m)  # the largest key on the left has no right child
            m[].right = r
            if r:
                r.value()[].parent = m
            m[].size += Self._size(r)
        self.size -= 1
        return Self._free(x)

    def lower_bound(mut self, key: Self.K) -> Optional[Self.K]:
        """The smallest key >= key."""
        var cur = self.root
        var last = cur
        var best = Self.Link(None)
        while cur:
            var n = cur.value()
            last = cur
            if n[].key < key:
                cur = n[].right
            else:
                best = cur
                cur = n[].left
        if best:
            self._splay(best.value())
            return best.value()[].key.copy()
        if last:
            self._splay(last.value())
        return None

    def select(mut self, var i: Int) -> Self.K:
        """The key at index i in sorted order (0 <= i < len)."""
        debug_assert(0 <= i < self.size, "SplayTree.select: bad index")
        var n = self.root.value()
        while True:
            var left = Self._size(n[].left)
            if i < left:
                n = n[].left.value()
            elif i == left:
                break
            else:
                i -= left + 1
                n = n[].right.value()
        self._splay(n)
        return n[].key.copy()

    def rank(mut self, key: Self.K) -> Int:
        """The number of keys < key."""
        var count = 0
        var cur = self.root
        var last = cur
        while cur:
            var n = cur.value()
            last = cur
            if n[].key < key:
                count += Self._size(n[].left) + 1
                cur = n[].right
            else:
                cur = n[].left
        if last:
            self._splay(last.value())
        return count

    def extreme(mut self, largest: Bool) -> Optional[Self.K]:
        """The smallest (or largest) key."""
        if not self.root:
            return None
        var n = Self._extreme(self.root.value(), largest)
        self._splay(n)
        return n[].key.copy()

    def root_key(self) -> Optional[Self.K]:
        if not self.root:
            return None
        return self.root.value()[].key.copy()

    # -- whole-tree operations

    def copy(self) -> Self:
        """A tree of new nodes with the same shape."""
        var out = Self(self.audit)
        if self.root:
            out.root = Self._clone(self.root.value(), None)
        out.size = self.size
        return out^

    @staticmethod
    def _clone(n: Self.NodePtr, parent: Self.Link) -> Self.NodePtr:
        # UNSAFE: allocates the copy of n's subtree
        var c = Self._new(n[].key.copy(), n[].value.copy(), parent)
        c[].size = n[].size
        if n[].left:
            c[].left = Self._clone(n[].left.value(), c)
        if n[].right:
            c[].right = Self._clone(n[].right.value(), c)
        return c

    def items(self, reverse: Bool = False) -> List[Tuple[Self.K, Self.V]]:
        """The entries in key order (or reversed), walked with parent
        links."""
        var out = List[Tuple[Self.K, Self.V]]()
        if not self.root:
            return out^
        var cur = Self.Link(Self._extreme(self.root.value(), reverse))
        while cur and len(out) <= self.size:
            var n = cur.value()
            out.append((n[].key.copy(), n[].value.copy()))
            cur = Self._next(n, not reverse)
        return out^

    def shape(self) -> List[Self.K]:
        """The keys in preorder, which determine the shape of a search
        tree."""
        var out = List[Self.K]()
        var stack = List[Self.NodePtr]()
        if self.root:
            stack.append(self.root.value())
        while len(stack) > 0 and len(out) <= self.size:
            var n = stack.pop()
            out.append(n[].key.copy())
            if n[].right:
                stack.append(n[].right.value())
            if n[].left:
                stack.append(n[].left.value())
        return out^

    def check_links(self) raises:
        """Raise unless every child's parent link points back, keys are in
        search-tree order, subtree sizes are right, and there are `size`
        nodes."""
        if self.root and self.root.value()[].parent:
            raise Error("the root has a parent")
        var count = Self._check(self.root, None, None, None, self.size)
        if count != self.size:
            raise Error("the tree has ", count, " nodes, not ", self.size)

    @staticmethod
    def _check(
        n: Self.Link,
        parent: Self.Link,
        low: Optional[Self.K],
        high: Optional[Self.K],
        limit: Int,
    ) raises -> Int:
        if not n:
            return 0
        if limit <= 0:
            raise Error("more nodes than the size (a cycle?)")
        var x = n.value()
        if x[].parent != parent:
            raise Error("a child's parent link doesn't point back")
        if (low and not (low.value() < x[].key)) or (
            high and not (x[].key < high.value())
        ):
            raise Error("keys out of order")
        var l = Self._check(x[].left, n, low, x[].key.copy(), limit - 1)
        var r = Self._check(x[].right, n, x[].key.copy(), high, limit - 1 - l)
        if x[].size != l + r + 1:
            raise Error("a subtree's size is ", x[].size, ", not ", l + r + 1)
        return l + r + 1


# ---- commands, checked against a sorted list of entries


@fieldwise_init
struct Entries(Copyable, Writable):
    """The model: keys in increasing order, and their values."""

    var keys: List[Int]
    var values: List[Int]

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


comptime IntTree = SplayTree[Int, Int]

# Bounds of the generated keys, so that keys collide often.
comptime MAX_KEY = 30


def check(sut: IntTree, model: Entries) raises:
    sut.check_links()
    assert_equal(len(sut), len(model.keys), "len")
    var forward = sut.items()
    var backward = sut.items(reverse=True)
    assert_equal(len(forward), len(model.keys), "items")
    assert_equal(len(backward), len(model.keys), "items reversed")
    var n = len(model.keys)
    for i in range(n):
        assert_equal(forward[i][0], model.keys[i], "key")
        assert_equal(forward[i][1], model.values[i], "value")
        assert_equal(backward[n - 1 - i][0], model.keys[i], "key, reversed")
    assert_true(
        sut.worst_excess <= 1e-9,
        String("a splay broke the access lemma by ", sut.worst_excess),
    )


@fieldwise_init
struct Insert(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var key: Int
    var value: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_KEY)), data.draw(integers(0, 99)))

    def next_state(self, mut model: Entries) raises:
        var i = model.find(self.key)
        if i:
            model.values[i.value()] = self.value
        else:
            var r = model.rank(self.key)
            model.keys.insert(r, self.key)
            model.values.insert(r, self.value)

    def run(self, model: Entries, mut sut: IntTree) raises:
        var expected: Optional[Int] = None
        var i = model.find(self.key)
        if i:
            expected = model.values[i.value()]
        assert_equal(sut.insert(self.key, self.value), expected, "old value")
        assert_equal(sut.root_key(), Optional(self.key), "splayed to the root")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("insert(", self.key, ", ", self.value, ")")


@fieldwise_init
struct Remove(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var key: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_KEY)))

    def next_state(self, mut model: Entries) raises:
        var i = model.find(self.key)
        if i:
            _ = model.keys.pop(i.value())
            _ = model.values.pop(i.value())

    def run(self, model: Entries, mut sut: IntTree) raises:
        var expected: Optional[Int] = None
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
struct Get(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var key: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_KEY)))

    def run(self, model: Entries, mut sut: IntTree) raises:
        var i = model.find(self.key)
        if i:
            assert_equal(sut.get(self.key), Optional(model.values[i.value()]))
            assert_equal(sut.root_key(), Optional(self.key), "splayed")
        else:
            assert_equal(sut.get(self.key), Optional[Int](None))
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("get(", self.key, ")")


@fieldwise_init
struct LowerBound(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var key: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_KEY + 1)))

    def run(self, model: Entries, mut sut: IntTree) raises:
        var r = model.rank(self.key)
        var expected: Optional[Int] = None
        if r < len(model.keys):
            expected = model.keys[r]
        assert_equal(sut.lower_bound(self.key), expected, "lower bound")
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("lower_bound(", self.key, ")")


@fieldwise_init
struct Select(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var index: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        if len(model.keys) == 0:
            return Self(0)  # rejected by precondition
        return Self(data.draw(integers(0, len(model.keys) - 1)))

    def precondition(self, model: Entries) raises -> Bool:
        return self.index < len(model.keys)

    def run(self, model: Entries, mut sut: IntTree) raises:
        assert_equal(sut.select(self.index), model.keys[self.index], "select")
        assert_equal(sut.root_key(), Optional(model.keys[self.index]))
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("select(", self.index, ")")


@fieldwise_init
struct Rank(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var key: Int

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_KEY + 1)))

    def run(self, model: Entries, mut sut: IntTree) raises:
        assert_equal(sut.rank(self.key), model.rank(self.key), "rank")
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("rank(", self.key, ")")


@fieldwise_init
struct Extreme(Command):
    comptime Model = Entries
    comptime Sut = IntTree
    var largest: Bool

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(booleans()))

    def run(self, model: Entries, mut sut: IntTree) raises:
        var expected: Optional[Int] = None
        var n = len(model.keys)
        if n > 0:
            expected = model.keys[n - 1] if self.largest else model.keys[0]
        assert_equal(sut.extreme(self.largest), expected, "extreme")
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("max()" if self.largest else "min()")


@fieldwise_init
struct CopyThenChange(Command):
    """A copy has the same shape and its own nodes: changing it leaves the
    original alone."""

    comptime Model = Entries
    comptime Sut = IntTree

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self()

    def run(self, model: Entries, mut sut: IntTree) raises:
        var shape = sut.shape()
        var c = sut.copy()
        assert_true(c.shape() == shape, "the copy's shape")
        check(c, model)
        _ = c.insert(MAX_KEY + 1, -1)
        if len(model.keys) > 0:
            _ = c.remove(model.keys[0])
        assert_true(sut.shape() == shape, "the original's shape")
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("copy_then_change()")


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_a_sorted_list(mut data: ConjectureData) raises:
        var sut = IntTree(audit=True)
        run_commands[
            Insert,
            Remove,
            Get,
            LowerBound,
            Select,
            Rank,
            Extreme,
            CopyThenChange,
        ](Entries([], []), sut, data)

    given_data(matches_a_sorted_list, settings)
    print("matches a sorted list: passed")

    # Sequential access theorem: from any tree, accessing every key in
    # increasing order takes at most 4.5 n rotations (Elmasry, 2004).
    # Inserting keys in increasing order builds the worst starting tree, a
    # path, which random commands seldom build.
    def sequential_access_is_linear(keys: List[Int], as_path: Bool) raises:
        var order = keys.copy()
        if as_path:
            sort(order)
        var t = IntTree(audit=True)
        for k in order:
            _ = t.insert(k, 0)
        var start = t.rotations
        for i in range(len(t)):
            _ = t.select(i)
        var n = len(t)
        assert_true(
            Float64(t.rotations - start) <= 4.5 * Float64(n),
            String(t.rotations - start, " rotations for ", n, " keys"),
        )
        t.check_links()

    given(
        lists(integers(0, 200), max_size=100),
        booleans(),
        sequential_access_is_linear,
        settings,
    )
    print("sequential access is linear: passed")

    # Moving the tree doesn't move its nodes.
    def survives_a_move(keys: List[Int]) raises:
        var a = IntTree()
        for k in keys:
            _ = a.insert(k, k)
        var b = a^
        b.check_links()
        assert_equal(len(b.items()), len(b))

    given(lists(integers()), survives_a_move, settings)
    print("survives a move: passed")

    # Heap-allocated keys and values are freed on remove and destruction
    # (the AddressSanitizer build checks for leaks).
    def owns_its_entries(keys: List[String]) raises:
        var t = SplayTree[String, String]()
        for k in keys:
            _ = t.insert(k, k + "!")
        if len(keys) > 0:
            assert_equal(t.remove(keys[0]), Optional(keys[0] + "!"))
        var c = t.copy()
        _ = c.insert("extra", "")
        t.check_links()

    given(lists(text(max_size=10)), owns_its_entries, settings)
    print("owns its entries: passed")
