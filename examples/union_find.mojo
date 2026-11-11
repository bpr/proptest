# Union-find (a disjoint-set forest; Galler and Fischer, 1964): each set is
# a tree of nodes linked by parent pointers, and the root names the set. A
# root's parent pointer points to the root itself.
#
# - find(x) walks up to the root, then points every node on the way
#   directly at it (path compression), so later finds are short.
# - union(a, b) links the root of lower rank under the other (union by
#   rank). A rank bounds the tree's height and only grows when two trees of
#   equal rank are linked, so a tree of rank r has at least 2^r nodes.
#
# Together these make a sequence of m operations take O(m α(n)) time,
# where α, the inverse Ackermann function, is at most 4 for any n that
# fits in memory (Tarjan, 1975).
#
# Each node is its own heap allocation, linked by Pointers, and find
# rewrites the links it walks. Only UnionFind allocates and frees nodes,
# in the methods marked UNSAFE; callers name elements by handle. (Keeping
# the nodes in a List instead would be a classic bug: growing the list
# moves the nodes and leaves every parent pointer dangling.)
#
# The tests are model-based, against a naive partition (a set label per
# element). After every command they check that the trees partition the
# elements as the model does, that ranks strictly increase toward each
# root, that each root's size is right, and that every tree's height is
# at most its root's rank, which is at most log2 of its size. A find must
# leave every node on its path pointing at the root.
#
#   pixi run mojo run -I . examples/union_find.mojo
#   pixi run mojo build -I . --sanitize address -o uf examples/union_find.mojo && ./uf
#
# Run with PROPTEST_TIMEOUT=1000 so that crashes and hangs (a parent cycle
# makes find loop forever) shrink too.

from std.collections import Set
from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_false, assert_true

from proptest import *


# ---- the forest


struct UFNode(Movable):
    var parent: Pointer[Self, MutUntrackedOrigin]
    """Points to itself at a root."""
    var rank: Int
    var size: Int
    """The number of elements in the set (kept at the root only)."""

    def __init__(out self):
        # unusable until the forest points it at itself
        self.parent = Pointer[Self, MutUntrackedOrigin](
            unsafe_from_address=Int(0)
        )
        self.rank = 0
        self.size = 1


comptime NodePtr = Pointer[UFNode, MutUntrackedOrigin]


struct UnionFind(Movable, Sized):
    """Disjoint sets of elements 0, 1, 2, ..., made by make_set."""

    var nodes: List[NodePtr]
    """Each element's node, by handle. Moving this List moves only the
    pointers, never the nodes."""
    var sets: Int
    """The number of sets (roots)."""

    def __init__(out self):
        self.nodes = []
        self.sets = 0

    def __deinit__(deinit self):
        # UNSAFE: frees every node
        for n in self.nodes:
            _ = n.unsafe_take_pointee()
            n.unsafe_free()

    def __len__(self) -> Int:
        return len(self.nodes)

    def make_set(mut self) -> Int:
        """A new element, in a set of its own; returns its handle."""
        # UNSAFE: allocates a node and makes it a root
        var p = unsafe_alloc[UFNode](1)
        p.unsafe_write(UFNode())
        var n = NodePtr(to=p[])
        n[].parent = n
        self.nodes.append(n)
        self.sets += 1
        return len(self.nodes) - 1

    @staticmethod
    def _find(x: NodePtr) -> NodePtr:
        """x's root, pointing every node on the way at it."""
        var root = x
        while root[].parent != root:
            root = root[].parent
        # UNSAFE: rewrites the parent links on x's path
        var cur = x
        while cur != root:
            var next = cur[].parent
            cur[].parent = root
            cur = next
        return root

    def find(self, x: Int) -> Int:
        """The handle of the root of x's set (which is its name)."""
        var root = Self._find(self.nodes[x])
        for i in range(len(self.nodes)):
            if self.nodes[i] == root:
                return i
        return -1

    def same(self, a: Int, b: Int) -> Bool:
        return Self._find(self.nodes[a]) == Self._find(self.nodes[b])

    def union(mut self, a: Int, b: Int) -> Bool:
        """Merge a's and b's sets; False if they were already one."""
        var ra = Self._find(self.nodes[a])
        var rb = Self._find(self.nodes[b])
        if ra == rb:
            return False
        if ra[].rank < rb[].rank:
            swap(ra, rb)
        # UNSAFE: links the lower-ranked root under the other
        rb[].parent = ra
        ra[].size += rb[].size
        if ra[].rank == rb[].rank:
            ra[].rank += 1
        self.sets -= 1
        return True

    def set_size(self, x: Int) -> Int:
        return Self._find(self.nodes[x])[].size

    # -- inspection (without compressing paths)

    def path(self, x: Int) -> List[NodePtr]:
        """The nodes from x up to its root, inclusive."""
        var out = List[NodePtr]()
        var n = self.nodes[x]
        out.append(n)
        while n[].parent != n and len(out) <= len(self.nodes):
            n = n[].parent
            out.append(n)
        return out^

    def check(self) raises:
        """Raise unless every path ends at a root, ranks strictly increase
        up each path, and each root's size, rank, and height agree."""
        var roots = 0
        var count = Dict[Int, Int]()  # root address -> elements
        var height = Dict[Int, Int]()
        for i in range(len(self.nodes)):
            var p = self.path(i)
            var root = p[len(p) - 1]
            if root[].parent != root:
                raise Error("element ", i, "'s path doesn't end at a root")
            for k in range(len(p) - 1):
                if p[k][].rank >= p[k + 1][].rank:
                    raise Error("a rank doesn't increase toward the root")
            var r = Int(root)
            count[r] = count.get(r, 0) + 1
            height[r] = max(height.get(r, 0), len(p) - 1)
            if p[0] == root:
                roots += 1
        if roots != self.sets:
            raise Error(roots, " roots, but ", self.sets, " sets")
        for item in count.items():
            var root = NodePtr(unsafe_from_address=item.key)
            if root[].size != item.value:
                raise Error(
                    "a root's size is ", root[].size, ", not ", item.value
                )
            if height[item.key] > root[].rank:
                raise Error("a tree is taller than its rank")
            if (1 << root[].rank) > item.value:
                raise Error(
                    "a root of rank ",
                    root[].rank,
                    " has ",
                    item.value,
                    " elements",
                )


# ---- commands, checked against a naive partition


@fieldwise_init
struct Partition(Copyable):
    """The model: a set label per element."""

    var label: List[Int]

    def union(mut self, a: Int, b: Int) -> Bool:
        var la = self.label[a]
        var lb = self.label[b]
        if la == lb:
            return False
        for i in range(len(self.label)):
            if self.label[i] == lb:
                self.label[i] = la
        return True

    def size(self, x: Int) -> Int:
        var n = 0
        for l in self.label:
            if l == self.label[x]:
                n += 1
        return n

    def sets(self) -> Int:
        var seen = Set[Int]()
        for l in self.label:
            seen.add(l)
        return len(seen)


def check(sut: UnionFind, model: Partition) raises:
    sut.check()
    assert_equal(len(sut), len(model.label), "elements")
    assert_equal(sut.sets, model.sets(), "sets")
    # the trees and the model's labels name the same sets: a bijection
    # between roots and labels
    var root_of_label = Dict[Int, Int]()
    var label_of_root = Dict[Int, Int]()
    for i in range(len(model.label)):
        var p = sut.path(i)
        var root = Int(p[len(p) - 1])
        var label = model.label[i]
        if (
            root_of_label.get(label, root) != root
            or label_of_root.get(root, label) != label
        ):
            raise Error("element ", i, " is in the wrong set")
        root_of_label[label] = root
        label_of_root[root] = label


def draw_element(model: Partition, mut data: ConjectureData) raises -> Int:
    if len(model.label) == 0:
        return -1
    return data.draw(integers(0, len(model.label) - 1))


def has(model: Partition, x: Int) -> Bool:
    return 0 <= x < len(model.label)


@fieldwise_init
struct MakeSet(Command):
    comptime Model = Partition
    comptime Sut = UnionFind

    @staticmethod
    def generate(model: Partition, mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: Partition) raises:
        model.label.append(len(model.label))

    def run(self, model: Partition, mut sut: UnionFind) raises:
        assert_equal(sut.make_set(), len(model.label), "handle")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("make_set()")


@fieldwise_init
struct Union(Command):
    comptime Model = Partition
    comptime Sut = UnionFind
    var a: Int
    var b: Int

    @staticmethod
    def generate(model: Partition, mut data: ConjectureData) raises -> Self:
        return Self(draw_element(model, data), draw_element(model, data))

    def precondition(self, model: Partition) raises -> Bool:
        return has(model, self.a) and has(model, self.b)

    def next_state(self, mut model: Partition) raises:
        _ = model.union(self.a, self.b)

    def run(self, model: Partition, mut sut: UnionFind) raises:
        var after = model.copy()
        assert_equal(
            sut.union(self.a, self.b), after.union(self.a, self.b), "merged"
        )
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("union(", self.a, ", ", self.b, ")")


@fieldwise_init
struct Same(Command):
    comptime Model = Partition
    comptime Sut = UnionFind
    var a: Int
    var b: Int

    @staticmethod
    def generate(model: Partition, mut data: ConjectureData) raises -> Self:
        return Self(draw_element(model, data), draw_element(model, data))

    def precondition(self, model: Partition) raises -> Bool:
        return has(model, self.a) and has(model, self.b)

    def run(self, model: Partition, mut sut: UnionFind) raises:
        assert_equal(
            sut.same(self.a, self.b),
            model.label[self.a] == model.label[self.b],
            "same set",
        )
        assert_equal(sut.set_size(self.a), model.size(self.a), "set size")
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("same(", self.a, ", ", self.b, ")")


@fieldwise_init
struct Find(Command):
    """A find returns the root, and compresses the whole path to it."""

    comptime Model = Partition
    comptime Sut = UnionFind
    var x: Int

    @staticmethod
    def generate(model: Partition, mut data: ConjectureData) raises -> Self:
        return Self(draw_element(model, data))

    def precondition(self, model: Partition) raises -> Bool:
        return has(model, self.x)

    def run(self, model: Partition, mut sut: UnionFind) raises:
        var before = sut.path(self.x)
        var root = before[len(before) - 1]
        var r = sut.find(self.x)
        assert_true(sut.nodes[r] == root, "find returned the root")
        for n in before:
            assert_true(
                n[].parent == root, "a node on the path isn't compressed"
            )
        check(sut, model)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("find(", self.x, ")")


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_a_partition(mut data: ConjectureData) raises:
        var sut = UnionFind()
        var model = Partition([])
        # start with some elements, so that unions come early
        for _ in range(data.draw(integers(0, 12))):
            _ = sut.make_set()
            model.label.append(len(model.label))
        run_commands[MakeSet, Union, Same, Find](model, sut, data)

    given_data(matches_a_partition, settings)
    print("matches a partition: passed")

    # Union by rank keeps trees short even when every union is between a
    # big set and a singleton, in the worst order (no finds to compress).
    def unions_keep_trees_short(n: Int, pairs: List[Tuple[Int, Int]]) raises:
        var uf = UnionFind()
        for _ in range(n):
            _ = uf.make_set()
        for p in pairs:
            _ = uf.union(p[0] % n, p[1] % n)
        uf.check()

    given(
        integers(1, 64),
        lists(tuples(integers(0, 63), integers(0, 63)), max_size=100),
        unions_keep_trees_short,
        settings,
    )
    print("unions keep trees short: passed")

    # Union by rank's worst case: merging equal-sized sets in rounds, as in
    # a tournament, builds a binomial tree of height exactly log2 n. Then a
    # find from any node must point its whole path at the root (random
    # programs seldom build paths of three or more nodes).
    def compresses_a_binomial_tree(k: Int, x: Int) raises:
        var uf = UnionFind()
        var n = 1 << k
        for _ in range(n):
            _ = uf.make_set()
        var step = 1
        while step < n:
            for i in range(0, n, 2 * step):
                _ = uf.union(i, i + step)  # both are roots: nothing to compress
            step *= 2
        uf.check()
        var height = 0
        for i in range(n):
            height = max(height, len(uf.path(i)) - 1)
        assert_equal(height, k, "height")
        var before = uf.path(x % n)
        var root = before[len(before) - 1]
        _ = uf.find(x % n)
        for node in before:
            assert_true(
                node[].parent == root, "a node on the path isn't compressed"
            )
        uf.check()

    given(integers(0, 6), integers(0, 63), compresses_a_binomial_tree, settings)
    print("compresses a binomial tree: passed")

    # Moving the forest doesn't move its nodes.
    def survives_a_move(n: Int, pairs: List[Tuple[Int, Int]]) raises:
        var a = UnionFind()
        for _ in range(n):
            _ = a.make_set()
        for p in pairs:
            _ = a.union(p[0] % n, p[1] % n)
        var sets = a.sets
        var b = a^
        b.check()
        assert_equal(b.sets, sets)

    given(
        integers(1, 20),
        lists(tuples(integers(0, 19), integers(0, 19))),
        survives_a_move,
        settings,
    )
    print("survives a move: passed")
