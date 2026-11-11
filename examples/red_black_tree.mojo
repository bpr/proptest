# A red-black tree that stores each node's color in the low bit of its
# parent pointer, as the Linux kernel's rbtree does (__rb_parent_color).
# A node is at least 8-byte aligned, so the low bits of its address are
# always 0, and bit 0 is free to hold the color (0 for red, 1 for black).
#
# Reading a parent means masking off the color and turning the integer
# back into a pointer (Pointer(unsafe_from_address=...)); setting one
# means OR-ing an address with the old color. A wrong mask or a forgotten
# color bit gives a pointer off by one byte, which the compiler can't
# know is wrong: a test of how the optimizer handles pointer bit tricks.
#
# Only RBTree allocates, links, and frees nodes, in the methods marked
# UNSAFE. It's Movable, not Copyable; copy() builds a tree of new nodes
# with the same shape and colors.
#
# The tests are model-based, against a sorted list. After every command
# they check the red-black rules (the root is black, a red node has no red
# child, every path down has the same number of black nodes), that every
# parent link points back and holds no stray bits, the search-tree order,
# and that the height is at most 2 log2(n + 1). They also walk the tree in
# order both ways using only the parent links.
#
#   pixi run mojo run -I . examples/red_black_tree.mojo
#   pixi run mojo build -I . --sanitize address -o rb examples/red_black_tree.mojo && ./rb
#
# A bad link usually makes a walk dereference a garbage address, or loop
# forever around a cycle. Run with PROPTEST_TIMEOUT=1000 (each test case in
# a child process, killed after a second) so that crashes and hangs shrink
# too.

from std.math import log2
from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.sys import align_of
from std.testing import assert_equal, assert_true

from proptest import *


# ---- the tree

comptime RED = 0
comptime BLACK = 1
comptime COLOR_MASK = 1


struct RBNode[K: Comparable & Copyable & Deinitable, V: Copyable & Deinitable](
    Movable
):
    var key: Self.K
    var value: Self.V
    var left: Optional[Pointer[Self, MutUntrackedOrigin]]
    var right: Optional[Pointer[Self, MutUntrackedOrigin]]
    var parent_color: Int
    """The parent's address (0 for the root) OR the color."""

    def __init__(
        out self, var key: Self.K, var value: Self.V, parent_color: Int
    ):
        self.key = key^
        self.value = value^
        self.left = None
        self.right = None
        self.parent_color = parent_color

    def take_value(deinit self) -> Self.V:
        return self.value^


struct RBTree[K: Comparable & Copyable & Deinitable, V: Copyable & Deinitable](
    Movable, Sized
):
    """An ordered map kept balanced by red-black rules."""

    comptime Node = RBNode[Self.K, Self.V]
    comptime NodePtr = Pointer[Self.Node, MutUntrackedOrigin]
    comptime Link = Optional[Self.NodePtr]

    var root: Self.Link
    var size: Int

    def __init__(out self):
        self.root = None
        self.size = 0

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
                var p = Self._parent(n)
                if p:
                    if p.value()[].left == cur:
                        p.value()[].left = None
                    else:
                        p.value()[].right = None
                _ = Self._free(n)
                cur = p

    def __len__(self) -> Int:
        return self.size

    # -- tagged parent pointers

    @staticmethod
    def _addr(n: Self.Link) -> Int:
        return Int(n.value()) if n else 0

    @staticmethod
    def _parent(n: Self.NodePtr) -> Self.Link:
        var a = n[].parent_color & ~COLOR_MASK
        if a == 0:
            return None
        return Self.NodePtr(unsafe_from_address=a)

    @staticmethod
    def _set_parent(n: Self.NodePtr, p: Self.Link):
        n[].parent_color = Self._addr(p) | (n[].parent_color & COLOR_MASK)

    @staticmethod
    def _color(n: Self.NodePtr) -> Int:
        return n[].parent_color & COLOR_MASK

    @staticmethod
    def _set_color(n: Self.NodePtr, color: Int):
        n[].parent_color = (n[].parent_color & ~COLOR_MASK) | color

    @staticmethod
    def _is_red(n: Self.Link) -> Bool:
        """Missing nodes (leaves) are black."""
        return n and Self._color(n.value()) == RED

    # -- nodes and links

    @staticmethod
    def _new(
        var key: Self.K, var value: Self.V, parent: Self.Link
    ) -> Self.NodePtr:
        # UNSAFE: a new red node; the caller must link it into the tree
        var n = unsafe_alloc[Self.Node](1)
        debug_assert(Int(n) & COLOR_MASK == 0, "RBTree: unaligned node")
        n.unsafe_write(Self.Node(key^, value^, Self._addr(parent) | RED))
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
        var p = Self._parent(n)
        while p and Self._is_right(cur, p.value()) == right:
            cur = p.value()
            p = Self._parent(cur)
        return p

    def _replace_child(mut self, old: Self.NodePtr, new: Self.Link):
        """Put `new` where `old` hangs from its parent (or at the root), and
        set new's parent."""
        # UNSAFE: relinks old's parent; old's own links are unchanged
        var p = Self._parent(old)
        if not p:
            self.root = new
        else:
            Self._set_child(p.value(), Self._is_right(old, p.value()), new)
        if new:
            Self._set_parent(new.value(), p)

    def _rotate(mut self, x: Self.NodePtr):
        """Rotate x above its parent. Colors are unchanged."""
        # UNSAFE: relinks x, its parent, its grandparent, and one subtree
        var p = Self._parent(x).value()
        var right = Self._is_right(x, p)
        var inner = Self._child(x, not right)
        self._replace_child(p, x)
        Self._set_child(p, right, inner)
        if inner:
            Self._set_parent(inner.value(), p)
        Self._set_child(x, not right, p)
        Self._set_parent(p, x)

    # -- the map

    def _find(self, key: Self.K) -> Self.Link:
        var cur = self.root
        while cur:
            var n = cur.value()
            if n[].key == key:
                return cur
            cur = Self._child(n, n[].key < key)
        return None

    def get(self, key: Self.K) -> Optional[Self.V]:
        var n = self._find(key)
        if not n:
            return None
        return n.value()[].value.copy()

    def insert(
        mut self, var key: Self.K, var value: Self.V
    ) -> Optional[Self.V]:
        """Map key to value, returning the old value if there was one."""
        var parent = Self.Link(None)
        var right = False
        var cur = self.root
        while cur:
            var n = cur.value()
            if n[].key == key:
                var old = n[].value.copy()
                n[].value = value^
                return old^
            parent = cur
            right = n[].key < key
            cur = Self._child(n, right)
        # UNSAFE: links a new red leaf, then restores the red-black rules
        var z = Self._new(key^, value^, parent)
        if parent:
            Self._set_child(parent.value(), right, z)
        else:
            self.root = z
        self.size += 1
        self._fix_after_insert(z)
        return None

    def _fix_after_insert(mut self, var z: Self.NodePtr):
        """z is red; its parent may be red too."""
        while Self._is_red(Self._parent(z)):
            var p = Self._parent(z).value()
            var g = Self._parent(p).value()  # p is red, so not the root
            var p_right = Self._is_right(p, g)
            var uncle = Self._child(g, not p_right)
            if Self._is_red(uncle):
                # recolor and move the problem up two levels
                Self._set_color(p, BLACK)
                Self._set_color(uncle.value(), BLACK)
                Self._set_color(g, RED)
                z = g
                continue
            if Self._is_right(z, p) != p_right:
                # z is an inner grandchild: rotate it to the outside
                self._rotate(z)
                swap(z, p)
            self._rotate(p)
            Self._set_color(p, BLACK)
            Self._set_color(g, RED)
        Self._set_color(self.root.value(), BLACK)

    def remove(mut self, key: Self.K) -> Optional[Self.V]:
        """Remove key, returning its value if it was there."""
        var found = self._find(key)
        if not found:
            return None
        # UNSAFE: unlinks z, then restores the red-black rules
        var z = found.value()
        var removed_color = Self._color(z)
        var x: Self.Link  # the node that takes the removed node's place
        var x_parent: Self.Link
        if not z[].left:
            x = z[].right
            x_parent = Self._parent(z)
            self._replace_child(z, x)
        elif not z[].right:
            x = z[].left
            x_parent = Self._parent(z)
            self._replace_child(z, x)
        else:
            # move z's successor y into z's place
            var y = Self._extreme(z[].right.value(), right=False)
            removed_color = Self._color(y)
            x = y[].right
            if Self._parent(y) == found:
                x_parent = y
            else:
                x_parent = Self._parent(y)
                self._replace_child(y, x)
                y[].right = z[].right
                Self._set_parent(y[].right.value(), y)
            self._replace_child(z, y)
            y[].left = z[].left
            Self._set_parent(y[].left.value(), y)
            Self._set_color(y, Self._color(z))
        if removed_color == BLACK:
            self._fix_after_remove(x, x_parent)
        self.size -= 1
        return Self._free(z)

    def _fix_after_remove(mut self, var x: Self.Link, var x_parent: Self.Link):
        """The paths through x have one black node too few."""
        while x != self.root and not Self._is_red(x):
            var p = x_parent.value()
            var x_left = p[].left == x
            var w = Self._child(p, x_left).value()  # x's sibling
            if Self._is_red(w):
                Self._set_color(w, BLACK)
                Self._set_color(p, RED)
                self._rotate(w)
                w = Self._child(p, x_left).value()
            if not Self._is_red(w[].left) and not Self._is_red(w[].right):
                Self._set_color(w, RED)
                x = p
                x_parent = Self._parent(p)
                continue
            if not Self._is_red(Self._child(w, x_left)):
                # the far nephew is black, so the near one is red
                var near = Self._child(w, not x_left).value()
                Self._set_color(near, BLACK)
                Self._set_color(w, RED)
                self._rotate(near)
                w = near
            Self._set_color(w, Self._color(p))
            Self._set_color(p, BLACK)
            Self._set_color(Self._child(w, x_left).value(), BLACK)
            self._rotate(w)
            x = self.root
            break
        if x:
            Self._set_color(x.value(), BLACK)

    def lower_bound(self, key: Self.K) -> Optional[Self.K]:
        """The smallest key >= key."""
        var cur = self.root
        var best = Self.Link(None)
        while cur:
            var n = cur.value()
            if n[].key < key:
                cur = n[].right
            else:
                best = cur
                cur = n[].left
        if best:
            return best.value()[].key.copy()
        return None

    def extreme(self, largest: Bool) -> Optional[Self.K]:
        """The smallest (or largest) key."""
        if not self.root:
            return None
        return Self._extreme(self.root.value(), largest)[].key.copy()

    # -- whole-tree operations

    def copy(self) -> Self:
        """A tree of new nodes with the same shape and colors."""
        var out = Self()
        if self.root:
            out.root = Self._clone(self.root.value(), None)
        out.size = self.size
        return out^

    @staticmethod
    def _clone(n: Self.NodePtr, parent: Self.Link) -> Self.NodePtr:
        # UNSAFE: allocates the copy of n's subtree
        var c = Self._new(n[].key.copy(), n[].value.copy(), parent)
        Self._set_color(c, Self._color(n))
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

    def colors(self) -> List[Int]:
        """The colors in preorder."""
        var out = List[Int]()
        var stack = List[Self.NodePtr]()
        if self.root:
            stack.append(self.root.value())
        while len(stack) > 0 and len(out) <= self.size:
            var n = stack.pop()
            out.append(Self._color(n))
            if n[].right:
                stack.append(n[].right.value())
            if n[].left:
                stack.append(n[].left.value())
        return out^

    def check(self) raises:
        """Raise unless the red-black rules hold, every parent link points
        back and holds only the color bit, the keys are in order, there are
        `size` nodes, and the height is at most 2 log2(n + 1)."""
        if self.root:
            if Self._parent(self.root.value()):
                raise Error("the root has a parent")
            if Self._is_red(self.root):
                raise Error("the root is red")
        var r = Self._check(self.root, None, None, None, self.size)
        if r[0] != self.size:
            raise Error("the tree has ", r[0], " nodes, not ", self.size)
        if Float64(r[2]) > 2.0 * log2(Float64(self.size + 1)) + 1e-9:
            raise Error("height ", r[2], " with ", self.size, " nodes")

    @staticmethod
    def _check(
        n: Self.Link,
        parent: Self.Link,
        low: Optional[Self.K],
        high: Optional[Self.K],
        limit: Int,
    ) raises -> Tuple[Int, Int, Int]:
        """The number of nodes, black height, and height of n's subtree."""
        if not n:
            return (0, 1, 0)
        if limit <= 0:
            raise Error("more nodes than the size (a cycle?)")
        var x = n.value()
        var tag = x[].parent_color & (align_of[Self.Node]() - 1)
        if tag & ~COLOR_MASK != 0:
            raise Error("stray bits in a parent pointer: ", tag)
        if Self._parent(x) != parent:
            raise Error("a child's parent link doesn't point back")
        if (low and not (low.value() < x[].key)) or (
            high and not (x[].key < high.value())
        ):
            raise Error("keys out of order")
        if Self._is_red(n) and (
            Self._is_red(x[].left) or Self._is_red(x[].right)
        ):
            raise Error("a red node has a red child")
        var l = Self._check(x[].left, n, low, x[].key.copy(), limit - 1)
        var r = Self._check(
            x[].right, n, x[].key.copy(), high, limit - 1 - l[0]
        )
        if l[1] != r[1]:
            raise Error("black heights differ: ", l[1], " and ", r[1])
        var black = 1 if Self._color(x) == BLACK else 0
        return (l[0] + r[0] + 1, l[1] + black, max(l[2], r[2]) + 1)


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


comptime IntTree = RBTree[Int, Int]

# Bounds of the generated keys, so that keys collide often.
comptime MAX_KEY = 40


def check(sut: IntTree, model: Entries) raises:
    sut.check()
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
        # usually a key that's there
        if len(model.keys) > 0 and data.draw(integers(0, 3)) > 0:
            return Self(model.keys[data.draw(integers(0, len(model.keys) - 1))])
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
        var expected: Optional[Int] = None
        if i:
            expected = model.values[i.value()]
        assert_equal(sut.get(self.key), expected, "get")

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

    def write_to(self, mut writer: Some[Writer]):
        writer.write("lower_bound(", self.key, ")")


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

    def write_to(self, mut writer: Some[Writer]):
        writer.write("max()" if self.largest else "min()")


@fieldwise_init
struct CopyThenChange(Command):
    """A copy has the same shape and colors and its own nodes: changing it
    leaves the original alone."""

    comptime Model = Entries
    comptime Sut = IntTree

    @staticmethod
    def generate(model: Entries, mut data: ConjectureData) raises -> Self:
        return Self()

    def run(self, model: Entries, mut sut: IntTree) raises:
        var shape = sut.shape()
        var colors = sut.colors()
        var c = sut.copy()
        assert_true(c.shape() == shape, "the copy's shape")
        assert_true(c.colors() == colors, "the copy's colors")
        check(c, model)
        _ = c.insert(MAX_KEY + 1, -1)
        if len(model.keys) > 0:
            _ = c.remove(model.keys[0])
        c.check()
        assert_true(sut.shape() == shape, "the original's shape")
        assert_true(sut.colors() == colors, "the original's colors")
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("copy_then_change()")


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_a_sorted_list(mut data: ConjectureData) raises:
        var sut = IntTree()
        run_commands[Insert, Remove, Get, LowerBound, Extreme, CopyThenChange](
            Entries([], []), sut, data
        )

    given_data(matches_a_sorted_list, settings)
    print("matches a sorted list: passed")

    # Building a tree of up to 200 keys, then removing them all in a drawn
    # order, exercises the fixups on larger trees than the commands reach.
    def builds_and_empties(keys: List[Int], order: List[Int]) raises:
        var t = IntTree()
        var model = Entries([], [])
        for k in keys:
            _ = t.insert(k, k)
            Insert(k, k).next_state(model)
        check(t, model)
        for i in order:
            if len(model.keys) == 0:
                break
            var k = model.keys[i % len(model.keys)]
            assert_equal(t.remove(k), Optional(k))
            Remove(k).next_state(model)
            check(t, model)

    given(
        lists(integers(0, 1000), max_size=200),
        lists(integers(0, 1000), max_size=200),
        builds_and_empties,
        settings,
    )
    print("builds and empties: passed")

    # Moving the tree doesn't move its nodes.
    def survives_a_move(keys: List[Int]) raises:
        var a = IntTree()
        for k in keys:
            _ = a.insert(k, k)
        var b = a^
        b.check()
        assert_equal(len(b.items()), len(b))

    given(lists(integers()), survives_a_move, settings)
    print("survives a move: passed")

    # Heap-allocated keys and values are freed on remove and destruction
    # (the AddressSanitizer build checks for leaks).
    def owns_its_entries(keys: List[String]) raises:
        var t = RBTree[String, String]()
        for k in keys:
            _ = t.insert(k, k + "!")
        if len(keys) > 0:
            assert_equal(t.remove(keys[0]), Optional(keys[0] + "!"))
        var c = t.copy()
        _ = c.insert("extra", "")
        t.check()
        c.check()

    given(lists(text(max_size=10)), owns_its_entries, settings)
    print("owns its entries: passed")
