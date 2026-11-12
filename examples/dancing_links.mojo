# Knuth's Dancing Links (Algorithm X with DLX, "Dancing Links",
# arXiv cs/0011047), extended to Algorithm C, exact covering with colors
# (TAOCP 7.2.2.1), with heap-allocated nodes linked by raw pointers in four
# directions.
#
# An exact cover problem has items and options (sets of items); a solution
# is a set of options containing every primary item exactly once and every
# secondary item at most once. Each option must contain a primary item.
#
# With colors, an option may give a secondary item a color, and then the
# item may be in several options of a solution, as long as all of them
# give it the same color. (An option that gives it no color still wants it
# to itself.) With no colors, Algorithm C is Algorithm X.
#
# Each item has a header node; each option has a node per item, linked into
# a circular row (left/right) and into its item's circular column
# (up/down). The primary headers are linked into a ring through the root.
# Covering an item unlinks its header and every option that uses it;
# uncovering relinks them in reverse order. A removed node keeps its own
# links, so `x.left.right = x; x.right.left = x` puts it back: the links
# "dance", and the search allocates nothing.
#
# Colors add "purifying": choosing an option that gives item i the color
# c marks every other option with i:c as compatible (color -1) and hides
# every option that gives i another color or none. Hiding skips nodes
# marked compatible, so they stay in their purified columns.
#
# Covers must be undone in reverse order. Within one uncover, though, the
# loops could run in either direction: nodes removed from a doubly linked
# list come back correctly if relinked in reverse order *or* in the same
# order (only a mixed order breaks it), so a top-down uncover is an
# equivalent mutant, which no test can catch.
#
# The links are Pointer[Node, MutUntrackedOrigin], which the borrow
# checker doesn't track. Only ExactCover allocates, links, and frees nodes,
# in the methods marked UNSAFE; it frees them all in __deinit__, from a
# list of every node rather than by following links that may be dancing.
#
# The tests check:
# - the solutions against brute force, with and without Knuth's
#   minimum-remaining-values heuristic;
# - that a planted solution is found in larger problems;
# - that a search leaves every link exactly as it found it;
# - cover, purify, and their undoing, model-based: after each step every
#   column must hold exactly the options the model says, with the colors
#   it says;
# - Knuth's example of covering with colors;
# - the n-queens counts, using secondary items for the diagonals.
#
# Build with AddressSanitizer to check for use after free and leaks:
#
#   pixi run mojo run -I . examples/dancing_links.mojo
#   pixi run mojo build -I . --sanitize address -o dlx examples/dancing_links.mojo && ./dlx

from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_true

from proptest import *


# ---- the structure


struct Node(Movable):
    var left: Pointer[Self, MutUntrackedOrigin]
    var right: Pointer[Self, MutUntrackedOrigin]
    var up: Pointer[Self, MutUntrackedOrigin]
    var down: Pointer[Self, MutUntrackedOrigin]
    var column: Pointer[Self, MutUntrackedOrigin]
    """The item's header (for a header, itself)."""
    var size: Int
    """For a header: the number of options in its column."""
    var item: Int
    var option: Int
    """The option's index; -1 for headers and the root."""
    var id: Int
    """The node's index in ExactCover.nodes, for snapshots."""
    var color: Int
    """For an option's node: the color it gives its item (0 for none, -1
    once a purify has found it compatible). For a header: the color it's
    purified with, while it is."""

    def __init__(
        out self,
        me: Pointer[Self, MutUntrackedOrigin],
        item: Int,
        option: Int,
        id: Int,
    ):
        """A node linked only to itself."""
        self.left = me
        self.right = me
        self.up = me
        self.down = me
        self.column = me
        self.size = 0
        self.item = item
        self.option = option
        self.id = id
        self.color = 0


comptime NodePtr = Pointer[Node, MutUntrackedOrigin]


def _alloc(mut nodes: List[NodePtr], item: Int, option: Int) -> NodePtr:
    # UNSAFE: a new node, owned by `nodes` until ExactCover.__deinit__
    var n = unsafe_alloc[Node](1)
    n.unsafe_write(Node(n, item, option, len(nodes)))
    nodes.append(n)
    return n


struct ExactCover(Movable):
    """An exact cover problem with items 0..n_items-1, of which the first
    n_primary are primary."""

    var n_items: Int
    var n_primary: Int
    var nodes: List[NodePtr]
    """Every node, for __deinit__ and snapshots."""
    var root: NodePtr
    var headers: List[NodePtr]
    var options: List[List[Int]]

    def __init__(out self, n_items: Int, n_primary: Int):
        debug_assert(0 <= n_primary <= n_items, "ExactCover: bad n_primary")
        self.n_items = n_items
        self.n_primary = n_primary
        var nodes = List[NodePtr]()
        var root = _alloc(nodes, -1, -1)
        var headers = List[NodePtr]()
        for i in range(n_items):
            var h = _alloc(nodes, i, -1)
            if i < n_primary:  # secondary headers stay linked to themselves
                h[].left = root[].left
                h[].right = root
                root[].left[].right = h
                root[].left = h
            headers.append(h)
        self.nodes = nodes^
        self.root = root
        self.headers = headers^
        self.options = []

    def __deinit__(deinit self):
        # UNSAFE: frees every node; nothing may use them afterwards
        for n in self.nodes:
            _ = n.unsafe_take_pointee()
            n.unsafe_free()

    def add_option(
        mut self,
        items: List[Int],
        colors: List[Int] = [],
        at_top: Bool = False,
    ) raises:
        """Add an option: distinct items, at least one primary, with the
        colors it gives them (0 for none; only secondary items may have
        one). It goes at the bottom of each item's column, or at the top if
        `at_top`."""
        var has_primary = False
        if len(colors) != 0 and len(colors) != len(items):
            raise Error("add_option: one color per item")
        for i in range(len(items)):
            if items[i] < 0 or items[i] >= self.n_items:
                raise Error("add_option: no item ", items[i])
            var color = colors[i] if len(colors) > 0 else 0
            if color < 0 or (color > 0 and items[i] < self.n_primary):
                raise Error("add_option: bad color for item ", items[i])
            for j in range(i):
                if items[j] == items[i]:
                    raise Error("add_option: item ", items[i], " repeated")
            has_primary = has_primary or items[i] < self.n_primary
        if not has_primary:
            raise Error("add_option: needs a primary item")
        var option = len(self.options)
        self.options.append(items.copy())
        var first: Optional[NodePtr] = None
        for k in range(len(items)):
            # UNSAFE: links a new node into its column and at the end of
            # its row
            var item = items[k]
            var h = self.headers[item]
            var n = _alloc(self.nodes, item, option)
            n[].column = h
            n[].color = colors[k] if len(colors) > 0 else 0
            if at_top:
                n[].up = h
                n[].down = h[].down
                h[].down[].up = n
                h[].down = n
            else:
                n[].up = h[].up
                n[].down = h
                h[].up[].down = n
                h[].up = n
            h[].size += 1
            if first:
                var f = first.value()
                n[].left = f[].left
                n[].right = f
                f[].left[].right = n
                f[].left = n
            else:
                first = n

    def hide(mut self, i: NodePtr):
        """Remove the rest of i's option from their columns, except nodes
        a purify found compatible (Knuth's hide')."""
        # UNSAFE: unlinks the other nodes of i's row from their columns
        var j = i[].right
        while j != i:
            if j[].color >= 0:
                j[].down[].up = j[].up
                j[].up[].down = j[].down
                j[].column[].size -= 1
            j = j[].right

    def unhide(mut self, i: NodePtr):
        """Undo hide(i)."""
        # UNSAFE: relinks what hide(i) unlinked, in reverse order
        var j = i[].left
        while j != i:
            if j[].color >= 0:
                j[].column[].size += 1
                j[].down[].up = j
                j[].up[].down = j
            j = j[].left

    def cover(mut self, c: NodePtr):
        """Remove item c's header from the ring, and every option in c's
        column from the other columns."""
        # UNSAFE: c must be a header that isn't covered
        c[].right[].left = c[].left
        c[].left[].right = c[].right
        var i = c[].down
        while i != c:
            self.hide(i)
            i = i[].down

    def uncover(mut self, c: NodePtr):
        """Undo cover(c); covers must be undone in reverse order."""
        # UNSAFE: c must be the most recently covered header
        var i = c[].up
        while i != c:
            self.unhide(i)
            i = i[].up
        c[].right[].left = c
        c[].left[].right = c

    def purify(mut self, c: NodePtr, color: Int):
        """Commit secondary item c to `color`: mark the options giving it
        that color compatible (-1), and hide the others."""
        # UNSAFE: c must be a header that isn't covered or purified
        c[].color = color
        var i = c[].down
        while i != c:
            if i[].color == color:
                i[].color = -1
            else:
                self.hide(i)
            i = i[].down

    def unpurify(mut self, c: NodePtr):
        """Undo purify(c, ...), in reverse order."""
        # UNSAFE: c must be the most recently purified or covered header
        var color = c[].color
        var i = c[].up
        while i != c:
            if i[].color < 0:
                i[].color = color
            else:
                self.unhide(i)
            i = i[].up
        c[].color = 0

    def commit(mut self, j: NodePtr):
        """Choosing j's option: cover j's item, or purify it with j's
        color (nothing if j is already marked compatible)."""
        if j[].color == 0:
            self.cover(j[].column)
        elif j[].color > 0:
            self.purify(j[].column, j[].color)

    def uncommit(mut self, j: NodePtr):
        """Undo commit(j)."""
        if j[].color == 0:
            self.uncover(j[].column)
        elif j[].color > 0:
            self.unpurify(j[].column)

    def cover_item(mut self, item: Int):
        self.cover(self.headers[item])

    def uncover_item(mut self, item: Int):
        self.uncover(self.headers[item])

    def purify_item(mut self, item: Int, color: Int):
        self.purify(self.headers[item], color)

    def unpurify_item(mut self, item: Int):
        self.unpurify(self.headers[item])

    def _search(
        mut self,
        mut partial: List[Int],
        mut solutions: List[List[Int]],
        limit: Int,
        mrv: Bool,
    ) -> Bool:
        """Algorithm X; returns True once `limit` solutions are found."""
        if self.root[].right == self.root:
            solutions.append(partial.copy())
            return len(solutions) >= limit
        var c = self.root[].right
        if mrv:  # the item with the fewest options left
            var p = c[].right
            while p != self.root:
                if p[].size < c[].size:
                    c = p
                p = p[].right
        self.cover(c)
        var stop = False
        var r = c[].down
        while r != c and not stop:
            partial.append(r[].option)
            var j = r[].right
            while j != r:
                self.commit(j)
                j = j[].right
            stop = self._search(partial, solutions, limit, mrv)
            j = r[].left
            while j != r:
                self.uncommit(j)
                j = j[].left
            _ = partial.pop()
            r = r[].down
        self.uncover(c)
        return stop

    def solve(
        mut self, limit: Int = Int.MAX, mrv: Bool = True
    ) -> List[List[Int]]:
        """Up to `limit` solutions, each a list of option indices.
        `mrv` branches on the item with the fewest options (Knuth's
        heuristic); otherwise on the first item."""
        var partial = List[Int]()
        var solutions = List[List[Int]]()
        if limit > 0:
            _ = self._search(partial, solutions, limit, mrv)
        return solutions^

    # ---- inspection, for the tests

    def ring(self) -> List[Int]:
        """The uncovered primary items, in the root's ring order."""
        var out = List[Int]()
        var p = self.root[].right
        while p != self.root and len(out) <= self.n_items:
            out.append(p[].item)
            p = p[].right
        return out^

    def column(self, item: Int) -> List[Int]:
        """The options in the item's column, top to bottom."""
        var out = List[Int]()
        var h = self.headers[item]
        var p = h[].down
        while p != h and len(out) <= len(self.options):
            out.append(p[].option)
            p = p[].down
        return out^

    def colors(self, item: Int) -> List[Int]:
        """The colors of the nodes in the item's column, top to bottom."""
        var out = List[Int]()
        var h = self.headers[item]
        var p = h[].down
        while p != h and len(out) <= len(self.options):
            out.append(p[].color)
            p = p[].down
        return out^

    def snapshot(self) -> List[Int]:
        """Every link, size, and color, as node ids."""
        var out = List[Int]()
        for n in self.nodes:
            out.append(n[].left[].id)
            out.append(n[].right[].id)
            out.append(n[].up[].id)
            out.append(n[].down[].id)
            out.append(n[].column[].id)
            out.append(n[].size)
            out.append(n[].color)
        return out^

    def check_links(self) raises:
        """Raise unless the ring and every column and row is a consistent
        circular list: neighbors point back, columns point at their header
        and hold `size` nodes, and rows have one node per item."""
        var p = self.root
        for _ in range(self.n_primary + 1):
            if p[].right[].left != p:
                raise Error("ring: a left link doesn't point back")
            p = p[].right
            if p == self.root:
                break
        if p != self.root:
            raise Error("ring: longer than the primary items (or a cycle)")
        for h in self.headers:
            var count = 0
            var q = h[].down
            while q != h:
                count += 1
                if count > len(self.options):
                    raise Error("column ", h[].item, ": too long or a cycle")
                if q[].up[].down != q or q[].down[].up != q:
                    raise Error(
                        "column ", h[].item, ": a link doesn't point back"
                    )
                if q[].column != h or q[].item != h[].item:
                    raise Error("column ", h[].item, ": a node from elsewhere")
                var width = 1
                var r = q[].right
                while r != q:
                    if r[].left[].right != r or r[].option != q[].option:
                        raise Error("row ", q[].option, ": a bad link")
                    width += 1
                    if width > len(self.options[q[].option]):
                        raise Error("row ", q[].option, ": too long")
                    r = r[].right
                if width != len(self.options[q[].option]):
                    raise Error("row ", q[].option, ": too short")
                q = q[].down
            if h[].up[].down != h or h[].down[].up != h:
                raise Error("column ", h[].item, ": the header's links")
            if count != h[].size:
                raise Error(
                    "column ", h[].item, ": size ", h[].size, " but ", count
                )


# ---- problems as bitmasks, and brute force


@fieldwise_init
struct Problem(Copyable, Writable):
    var n_items: Int
    var n_primary: Int
    var options: List[Int]
    """Each option as a bitmask of its items."""
    var at_top: Int
    """A bitmask of the options added at the top of their columns, so the
    columns don't all list the options in the same order."""
    var colors: List[List[Int]]
    """The color option k gives item i, at [k][i] (0 for none)."""

    @staticmethod
    def uncolored(
        n_items: Int, n_primary: Int, var options: List[Int], at_top: Int
    ) -> Self:
        var colors = List[List[Int]]()
        for _ in range(len(options)):
            colors.append(List[Int](length=n_items, fill=0))
        return Self(n_items, n_primary, options^, at_top, colors^)

    def column_order(self, item: Int) -> List[Int]:
        """The options in the item's column, top to bottom."""
        var out = List[Int]()
        for k in range(len(self.options)):
            if self.options[k] & (1 << item):
                if self.at_top & (1 << k):
                    out.insert(0, k)
                else:
                    out.append(k)
        return out^

    def items(self, option: Int) -> List[Int]:
        var out = List[Int]()
        for i in range(self.n_items):
            if self.options[option] & (1 << i):
                out.append(i)
        return out^

    def option_colors(self, option: Int) -> List[Int]:
        var out = List[Int]()
        for i in self.items(option):
            out.append(self.colors[option][i])
        return out^

    def build(self) raises -> ExactCover:
        var x = ExactCover(self.n_items, self.n_primary)
        for k in range(len(self.options)):
            x.add_option(
                self.items(k),
                self.option_colors(k),
                at_top=Bool(self.at_top & (1 << k)),
            )
        return x^

    def brute_force(self) -> List[Int]:
        """Every solution, as a bitmask of options, in increasing order:
        each primary item in exactly one chosen option, and each secondary
        item in at most one, or in several that all give it one color."""
        var primary = (1 << self.n_primary) - 1
        var out = List[Int]()
        for chosen in range(1 << len(self.options)):
            var used = 0
            var color = List[Int](length=self.n_items, fill=0)
            var ok = True
            for k in range(len(self.options)):
                if not chosen & (1 << k):
                    continue
                for i in self.items(k):
                    var c = self.colors[k][i]
                    if used & (1 << i):
                        # shared: fine only if both give it the same color
                        if c == 0 or c != color[i]:
                            ok = False
                    color[i] = c
                    used |= 1 << i
            if ok and used & primary == primary:
                out.append(chosen)
        return out^


def as_masks(solutions: List[List[Int]]) -> List[Int]:
    var out = List[Int]()
    for s in solutions:
        var m = 0
        for k in s:
            m |= 1 << k
        out.append(m)
    sort(out)
    return out^


def draw_problem(
    mut data: ConjectureData,
    max_items: Int,
    max_options: Int,
    max_colors: Int = 2,
) raises -> Problem:
    var n = data.draw(integers(1, max_items))
    var n_primary = data.draw(integers(1, n))
    var masks = data.draw(
        lists(
            tuples(
                integers(0, (1 << n) - 1),
                integers(0, n_primary - 1),
                booleans(),
            ),
            max_size=max_options,
        )
    )
    var options = List[Int]()
    var at_top = 0
    var colors = List[List[Int]]()
    for k in range(len(masks)):  # every option gets a primary item
        options.append(masks[k][0] | (1 << masks[k][1]))
        if masks[k][2]:
            at_top |= 1 << k
        # a color (or none) for each secondary item; few colors, so that
        # they often agree
        var c = List[Int](length=n, fill=0)
        for i in range(n_primary, n):
            if options[k] & (1 << i):
                c[i] = data.draw(integers(0, max_colors))
        colors.append(c^)
    return Problem(n, n_primary, options^, at_top, colors^)


# ---- a model of cover, purify, and undoing them


@fieldwise_init
struct CoverModel(Copyable, Writable):
    """The structure as sets: which nodes are linked into their columns,
    and each node's color."""

    var problem: Problem
    var stack: List[Int]
    """The covered or purified items, in order."""
    var purified_with: List[Int]
    """The color each item on the stack was purified with (0: covered)."""
    var linked: List[List[Bool]]
    """Whether option k's node for item i is in item i's column, at [k][i]."""
    var color: List[List[Int]]
    """That node's color, at [k][i]."""
    var saved_linked: List[List[List[Bool]]]
    var saved_color: List[List[List[Int]]]
    """The state before each operation on the stack, to undo it."""
    var initial: List[Int]
    """The structure's snapshot before any operation."""

    @staticmethod
    def start(problem: Problem, initial: List[Int]) -> Self:
        var linked = List[List[Bool]]()
        for _ in range(len(problem.options)):
            linked.append(List[Bool](length=problem.n_items, fill=True))
        return Self(
            problem.copy(),
            [],
            [],
            linked^,
            problem.colors.copy(),
            [],
            [],
            initial.copy(),
        )

    def is_used(self, item: Int) -> Bool:
        return item in self.stack

    def ring(self) -> List[Int]:
        var out = List[Int]()
        for i in range(self.problem.n_primary):
            if not self.is_used(i):
                out.append(i)
        return out^

    def column(self, item: Int) -> List[Int]:
        """The options whose node for `item` is still in its column."""
        var out = List[Int]()
        for k in self.problem.column_order(item):
            if self.linked[k][item]:
                out.append(k)
        return out^

    def colors(self, item: Int) -> List[Int]:
        var out = List[Int]()
        for k in self.column(item):
            out.append(self.color[k][item])
        return out^

    def _hide(mut self, option: Int, item: Int):
        for i in self.problem.items(option):
            if i != item and self.color[option][i] >= 0:
                self.linked[option][i] = False

    def _save(mut self, item: Int, color: Int):
        self.saved_linked.append(self.linked.copy())
        self.saved_color.append(self.color.copy())
        self.stack.append(item)
        self.purified_with.append(color)

    def cover(mut self, item: Int):
        self._save(item, 0)
        for k in self.column(item):
            self._hide(k, item)

    def purify(mut self, item: Int, color: Int):
        self._save(item, color)
        for k in self.column(item):
            if self.color[k][item] == color:
                self.color[k][item] = -1
            else:
                self._hide(k, item)

    def undo(mut self):
        self.linked = self.saved_linked.pop()
        self.color = self.saved_color.pop()
        _ = self.stack.pop()
        _ = self.purified_with.pop()


def check_against(model: CoverModel, sut: ExactCover) raises:
    sut.check_links()
    assert_true(sut.ring() == model.ring(), "ring")
    for i in range(model.problem.n_items):
        assert_true(sut.column(i) == model.column(i), String("column ", i))
        assert_true(sut.colors(i) == model.colors(i), String("colors ", i))


@fieldwise_init
struct Cover(Command):
    comptime Model = CoverModel
    comptime Sut = ExactCover
    var item: Int

    @staticmethod
    def generate(model: CoverModel, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, model.problem.n_items - 1)))

    def precondition(self, model: CoverModel) raises -> Bool:
        return not model.is_used(self.item)

    def next_state(self, mut model: CoverModel) raises:
        model.cover(self.item)

    def run(self, model: CoverModel, mut sut: ExactCover) raises:
        sut.cover_item(self.item)
        var after = model.copy()
        self.next_state(after)
        check_against(after, sut)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("cover(", self.item, ")")


@fieldwise_init
struct Purify(Command):
    comptime Model = CoverModel
    comptime Sut = ExactCover
    var item: Int
    var color: Int

    @staticmethod
    def generate(model: CoverModel, mut data: ConjectureData) raises -> Self:
        var p = model.problem.copy()
        if p.n_primary == p.n_items:
            return Self(0, 1)  # rejected by precondition
        return Self(
            data.draw(integers(p.n_primary, p.n_items - 1)),
            data.draw(integers(1, 2)),
        )

    def precondition(self, model: CoverModel) raises -> Bool:
        return self.item >= model.problem.n_primary and not model.is_used(
            self.item
        )

    def next_state(self, mut model: CoverModel) raises:
        model.purify(self.item, self.color)

    def run(self, model: CoverModel, mut sut: ExactCover) raises:
        sut.purify_item(self.item, self.color)
        var after = model.copy()
        self.next_state(after)
        check_against(after, sut)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("purify(", self.item, ", color ", self.color, ")")


@fieldwise_init
struct Undo(Command):
    """Uncover or unpurify the last item covered or purified."""

    comptime Model = CoverModel
    comptime Sut = ExactCover

    @staticmethod
    def generate(model: CoverModel, mut data: ConjectureData) raises -> Self:
        return Self()

    def precondition(self, model: CoverModel) raises -> Bool:
        return len(model.stack) > 0

    def next_state(self, mut model: CoverModel) raises:
        model.undo()

    def run(self, model: CoverModel, mut sut: ExactCover) raises:
        var last = len(model.stack) - 1
        if model.purified_with[last] > 0:
            sut.unpurify_item(model.stack[last])
        else:
            sut.uncover_item(model.stack[last])
        var after = model.copy()
        self.next_state(after)
        check_against(after, sut)
        if len(after.stack) == 0:
            assert_true(sut.snapshot() == after.initial, "links restored")

    def write_to(self, mut writer: Some[Writer]):
        writer.write("undo()")


# ---- Knuth's example of exact covering with colors (TAOCP 7.2.2.1)


def knuths_color_example() raises:
    # primary items p, q, r (0..2); secondary items x, y (3, 4); colors
    # A = 1, B = 2. The options:
    #   0: p q x y:A    1: p r x:A y    2: p x:B    3: q x:A    4: r y:B
    var x = ExactCover(5, 3)
    x.add_option([0, 1, 3, 4], [0, 0, 0, 1])
    x.add_option([0, 2, 3, 4], [0, 0, 1, 0])
    x.add_option([0, 3], [0, 2])
    x.add_option([1, 3], [0, 1])
    x.add_option([2, 4], [0, 2])
    var before = x.snapshot()
    var solutions = x.solve()
    assert_equal(len(solutions), 1, "one solution")
    var s = solutions[0].copy()
    sort(s)
    assert_true(s == [1, 3], "options 1 and 3 (p r x:A y, q x:A)")
    assert_true(x.snapshot() == before, "links and colors restored")


# ---- n queens: rows and columns primary, diagonals secondary


def queens(n: Int) raises -> ExactCover:
    # items: rows 0..n-1, columns n..2n-1, then 2n-1 diagonals of each kind
    var x = ExactCover(6 * n - 2, 2 * n)
    for r in range(n):
        for c in range(n):
            x.add_option([r, n + c, 2 * n + r + c, 4 * n - 1 + r - c + n - 1])
    return x^


def queens_counts() raises:
    var expected: List[Int] = [1, 0, 0, 2, 10, 4, 40, 92]
    for n in range(1, len(expected) + 1):
        var x = queens(n)
        var before = x.snapshot()
        assert_equal(len(x.solve()), expected[n - 1], String(n, " queens"))
        assert_equal(len(x.solve(mrv=False)), expected[n - 1])
        assert_true(x.snapshot() == before, "the search restored the links")
    # a limit stops the search early, and still restores the links
    var x = queens(8)
    var before = x.snapshot()
    assert_equal(len(x.solve(limit=3)), 3)
    assert_true(x.snapshot() == before)


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    queens_counts()
    print("n queens, 1..8: passed")
    knuths_color_example()
    print("Knuth's color example: passed")

    def matches_brute_force(mut data: ConjectureData) raises:
        var p = draw_problem(data, 6, 10)
        var x = p.build()
        x.check_links()
        var before = x.snapshot()
        var expected = p.brute_force()
        assert_true(as_masks(x.solve()) == expected, "with mrv")
        assert_true(x.snapshot() == before, "the links after a search")
        assert_true(as_masks(x.solve(mrv=False)) == expected, "without mrv")
        assert_true(x.snapshot() == before, "the links after a search")
        x.check_links()

    given_data(matches_brute_force, settings)
    print("matches brute force: passed")

    # Partition the items into blocks (a planted solution), add other
    # options, and shuffle: the search must find the partition.
    def finds_a_planted_solution(mut data: ConjectureData) raises:
        var n = data.draw(integers(1, 24))
        var blocks = data.draw(integers(1, n))
        var masks = List[Int]()
        for _ in range(blocks):
            masks.append(0)
        for i in range(n):
            masks[data.draw(integers(0, blocks - 1))] |= 1 << i
        var planted = List[Int]()
        for m in masks:
            if m != 0:
                planted.append(m)
        var options = data.draw(lists(integers(1, (1 << n) - 1), max_size=12))
        for m in planted:
            options.append(m)
        var shuffled = data.draw(permutations(options^))
        var at_top = data.draw(integers(0, (1 << len(shuffled)) - 1))
        var x = Problem.uncolored(n, n, shuffled.copy(), at_top).build()
        var found = x.solve()
        x.check_links()
        var cover = 0
        for o in planted:
            cover |= o
        # every solution is an exact cover, and the planted one is there
        var seen_planted = False
        for s in found:
            var used = 0
            var masks_in = List[Int]()
            for k in s:
                assert_true(used & shuffled[k] == 0, "options overlap")
                used |= shuffled[k]
                masks_in.append(shuffled[k])
            assert_equal(used, cover, "covers every item")
            sort(masks_in)
            var p = planted.copy()
            sort(p)
            seen_planted = seen_planted or masks_in == p
        assert_true(seen_planted, "found the planted solution")

    given_data(finds_a_planted_solution, settings)
    print("finds a planted solution: passed")

    def cover_matches_model(mut data: ConjectureData) raises:
        var p = draw_problem(data, 6, 10)
        var x = p.build()
        var model = CoverModel.start(p, x.snapshot())
        run_commands[Cover, Purify, Undo](model, x, data)

    given_data(cover_matches_model, settings)
    print("cover, purify, and undo match the model: passed")

    # Moving the structure doesn't move its nodes.
    def survives_a_move(mut data: ConjectureData) raises:
        var p = draw_problem(data, 6, 10)
        var a = p.build()
        var expected = as_masks(a.solve())
        var b = a^
        b.check_links()
        assert_true(as_masks(b.solve()) == expected)

    given_data(survives_a_move, settings)
    print("survives a move: passed")
