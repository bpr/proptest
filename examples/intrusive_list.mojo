# Intrusive linked lists, as in the Linux kernel (struct list_head): the
# links live inside the elements, and a list of tasks is a ring of the
# tasks' own link fields. From a link, container_of recovers the task
# around it by subtracting the link field's offset in the struct, here
# reflect[Task].field_offset[name=...](). A task holds two links, so it can
# be on two lists at once (every task, and the ready queue) with no
# allocation for either.
#
# Every step from a link to its task (and back) goes through an integer:
# address minus offset, then Pointer(unsafe_from_address=...). The
# compiler sees pointers to one field turned into pointers to another, a
# test of how it handles pointer arithmetic across fields.
#
# The rules, Linux's:
# - A list is a ring through a sentinel head, so linking and unlinking
#   never check for the ends. Heads are heap-allocated: the ring points at
#   them, so moving a list must not move its head.
# - A link not on any list points to itself (list_del_init), so "is this
#   task ready?" is one comparison.
# - Only Scheduler allocates and frees tasks, in the methods marked UNSAFE.
#   Lists own nothing but their heads.
#
# Unlike Linux's, the link field is part of the list's type
# (IntrusiveList[Task, "ready_link"]), so splicing a list linked through
# one field into a list linked through another doesn't compile.
#
# The tests are model-based: a scheduler's tasks and ready queue against two
# plain lists of ids, checking both rings both ways after every command.
#
#   pixi run mojo run -I . examples/intrusive_list.mojo
#   pixi run mojo build -I . --sanitize address -o intrusive examples/intrusive_list.mojo && ./intrusive
#
# Run with PROPTEST_TIMEOUT=1000 so that crashes and hangs (a broken ring
# can loop forever) shrink too.

from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.reflection import reflect
from std.testing import assert_equal, assert_false, assert_true

from proptest import *


# ---- links


struct ListHead(Movable):
    """Two links of a ring; points to itself when not on a list."""

    var next: Pointer[Self, MutUntrackedOrigin]
    var prev: Pointer[Self, MutUntrackedOrigin]

    def __init__(out self):
        # unusable until _init_link points it at itself
        self.next = Pointer[Self, MutUntrackedOrigin](
            unsafe_from_address=Int(0)
        )
        self.prev = self.next


comptime LinkPtr = Pointer[ListHead, MutUntrackedOrigin]


def _init_link(n: LinkPtr):
    n[].next = n
    n[].prev = n


def _is_linked(n: LinkPtr) -> Bool:
    return n[].next != n


def _link_between(n: LinkPtr, prev: LinkPtr, next: LinkPtr):
    # UNSAFE: prev and next must be adjacent in a ring, and n on none
    next[].prev = n
    n[].next = next
    n[].prev = prev
    prev[].next = n


def _unlink(n: LinkPtr):
    # UNSAFE: n must be on a ring; afterwards it points to itself
    n[].prev[].next = n[].next
    n[].next[].prev = n[].prev
    _init_link(n)


struct IntrusiveList[T: AnyType, field: StringLiteral](Movable, Sized):
    """A list of T values linked through their ListHead field `field`. It
    doesn't own its elements."""

    comptime offset = reflect[Self.T].field_offset[name=Self.field]()
    comptime Elem = Pointer[Self.T, MutUntrackedOrigin]

    var head: LinkPtr
    """The sentinel, on the heap so that moving the list doesn't move it."""
    var size: Int

    def __init__(out self):
        var h = unsafe_alloc[ListHead](1)
        h.unsafe_write(ListHead())
        self.head = LinkPtr(to=h[])
        _init_link(self.head)
        self.size = 0

    def __deinit__(deinit self):
        # UNSAFE: elements still on the list are left pointing at a freed
        # head; the owner of the elements must not use those links again
        _ = self.head.unsafe_take_pointee()
        self.head.unsafe_free()

    def __len__(self) -> Int:
        return self.size

    @staticmethod
    def link_of(e: Self.Elem) -> LinkPtr:
        return LinkPtr(unsafe_from_address=Int(e) + Self.offset)

    @staticmethod
    def container_of(n: LinkPtr) -> Self.Elem:
        return Self.Elem(unsafe_from_address=Int(n) - Self.offset)

    def contains(self, e: Self.Elem) -> Bool:
        """Whether e is on this list (or another list through the same
        field)."""
        return _is_linked(Self.link_of(e))

    def push_back(mut self, e: Self.Elem):
        debug_assert(not self.contains(e), "IntrusiveList: already linked")
        _link_between(Self.link_of(e), self.head[].prev, self.head)
        self.size += 1

    def push_front(mut self, e: Self.Elem):
        debug_assert(not self.contains(e), "IntrusiveList: already linked")
        _link_between(Self.link_of(e), self.head, self.head[].next)
        self.size += 1

    def remove(mut self, e: Self.Elem):
        debug_assert(self.contains(e), "IntrusiveList: not linked")
        _unlink(Self.link_of(e))
        self.size -= 1

    def front(self) -> Optional[Self.Elem]:
        if self.size == 0:
            return None
        return Self.container_of(self.head[].next)

    def move_to_front(mut self, e: Self.Elem):
        """Linux's list_move: e must be on this list."""
        var n = Self.link_of(e)
        _unlink(n)
        _link_between(n, self.head, self.head[].next)

    def move_to_back(mut self, e: Self.Elem):
        """Linux's list_move_tail: e must be on this list."""
        var n = Self.link_of(e)
        _unlink(n)
        _link_between(n, self.head[].prev, self.head)

    def splice_back(mut self, mut other: Self):
        """Move all of other's elements to the end of this list, in O(1)."""
        if other.size == 0:
            return
        # UNSAFE: relinks the two rings into one, and empties other's
        var first = other.head[].next
        var last = other.head[].prev
        var at = self.head[].prev
        at[].next = first
        first[].prev = at
        last[].next = self.head
        self.head[].prev = last
        self.size += other.size
        _init_link(other.head)
        other.size = 0

    def elements(self, reverse: Bool = False) -> List[Self.Elem]:
        var out = List[Self.Elem]()
        var n = self.head[].prev if reverse else self.head[].next
        while n != self.head and len(out) <= self.size:
            out.append(Self.container_of(n))
            n = n[].prev if reverse else n[].next
        return out^

    def check_links(self) raises:
        """Raise unless the ring through the head has `size` links and each
        link's neighbors point back at it."""
        var n = self.head
        for i in range(self.size + 1):
            if n[].next[].prev != n:
                raise Error("a link's next doesn't point back")
            if n[].prev[].next != n:
                raise Error("a link's prev doesn't point back")
            n = n[].next
            if n == self.head:
                if i != self.size:
                    raise Error("the ring has ", i, " links, not ", self.size)
                return
        raise Error("the ring doesn't come back to its head")


# ---- a scheduler: every task is on `all`, and some are on `ready`


struct Task(Movable):
    var id: Int
    var all_link: ListHead
    var name: String
    """Heap-allocated, so AddressSanitizer sees leaked tasks."""
    var ready_link: ListHead

    def __init__(out self, id: Int, var name: String):
        self.id = id
        self.all_link = ListHead()
        self.name = name^
        self.ready_link = ListHead()


comptime TaskPtr = Pointer[Task, MutUntrackedOrigin]


struct Scheduler(Movable):
    var all: IntrusiveList[Task, "all_link"]
    """Every task, oldest first."""
    var ready: IntrusiveList[Task, "ready_link"]
    """The run queue."""
    var next_id: Int

    def __init__(out self):
        self.all = IntrusiveList[Task, "all_link"]()
        self.ready = IntrusiveList[Task, "ready_link"]()
        self.next_id = 0

    def __deinit__(deinit self):
        # UNSAFE: frees every task; the lists then free their heads
        for t in self.all.elements():
            _ = t.unsafe_take_pointee()
            t.unsafe_free()

    def spawn(mut self) -> Int:
        """A new task, not ready."""
        # UNSAFE: allocates a task and links it into `all`
        var p = unsafe_alloc[Task](1)
        p.unsafe_write(Task(self.next_id, String("task ", self.next_id)))
        var t = TaskPtr(to=p[])
        _init_link(LinkPtr(to=t[].all_link))
        _init_link(LinkPtr(to=t[].ready_link))
        self.all.push_back(t)
        self.next_id += 1
        return t[].id

    def find(self, id: Int) -> Optional[TaskPtr]:
        for t in self.all.elements():
            if t[].id == id:
                return t
        return None

    def wake(mut self, id: Int, urgent: Bool = False) -> Bool:
        """Put the task at the back of the run queue (the front if urgent),
        unless it's there."""
        var t = self.find(id)
        if not t or self.ready.contains(t.value()):
            return False
        if urgent:
            self.ready.push_front(t.value())
        else:
            self.ready.push_back(t.value())
        return True

    def block(mut self, id: Int) -> Bool:
        """Take the task off the run queue."""
        var t = self.find(id)
        if not t or not self.ready.contains(t.value()):
            return False
        self.ready.remove(t.value())
        return True

    def run_next(mut self) -> Optional[Int]:
        """Round robin: the front task runs and goes to the back."""
        var t = self.ready.front()
        if not t:
            return None
        self.ready.move_to_back(t.value())
        return t.value()[].id

    def bump(mut self, id: Int) -> Bool:
        """Move a ready task to the front of the run queue."""
        var t = self.find(id)
        if not t or not self.ready.contains(t.value()):
            return False
        self.ready.move_to_front(t.value())
        return True

    def wake_all(mut self):
        """Wake every task that isn't ready, oldest first."""
        var woken = IntrusiveList[Task, "ready_link"]()
        for t in self.all.elements():
            if not self.ready.contains(t):
                woken.push_back(t)
        self.ready.splice_back(woken)

    def kill(mut self, id: Int) -> Bool:
        """Unlink the task from both lists and free it."""
        var found = self.find(id)
        if not found:
            return False
        var t = found.value()
        # UNSAFE: unlinks t from both lists, then frees it
        if self.ready.contains(t):
            self.ready.remove(t)
        self.all.remove(t)
        _ = t.unsafe_take_pointee()
        t.unsafe_free()
        return True

    def ids(self, ready: Bool, reverse: Bool = False) -> List[Int]:
        var out = List[Int]()
        var ts = self.ready.elements(reverse) if ready else self.all.elements(
            reverse
        )
        for t in ts:
            out.append(t[].id)
        return out^

    def check(self) raises:
        """Raise unless both rings are sound, and every task off the run
        queue has a ready link pointing to itself."""
        self.all.check_links()
        self.ready.check_links()
        var on_ready = 0
        for t in self.all.elements():
            if t[].name != String("task ", t[].id):
                raise Error("task ", t[].id, " has the wrong name")
            if self.ready.contains(t):
                on_ready += 1
            else:
                var n = LinkPtr(to=t[].ready_link)
                if n[].prev != n:
                    raise Error("an unlinked task's prev isn't itself")
        if on_ready != len(self.ready):
            raise Error(on_ready, " tasks are ready, not ", len(self.ready))


# ---- commands, checked against two lists of ids


@fieldwise_init
struct Model(Copyable):
    var all: List[Int]
    var ready: List[Int]
    var next_id: Int

    def is_ready(self, id: Int) -> Bool:
        return id in self.ready

    def remove_ready(mut self, id: Int):
        for i in range(len(self.ready)):
            if self.ready[i] == id:
                _ = self.ready.pop(i)
                return


def check(sut: Scheduler, model: Model) raises:
    sut.check()
    assert_true(sut.ids(ready=False) == model.all, "all tasks")
    assert_true(sut.ids(ready=True) == model.ready, "run queue")
    var all_rev = model.all.copy()
    all_rev.reverse()
    var ready_rev = model.ready.copy()
    ready_rev.reverse()
    assert_true(sut.ids(ready=False, reverse=True) == all_rev, "all, reversed")
    assert_true(
        sut.ids(ready=True, reverse=True) == ready_rev, "run queue, reversed"
    )


def draw_task(model: Model, mut data: ConjectureData) raises -> Int:
    """The id of a task that exists, or -1 if there are none."""
    if len(model.all) == 0:
        return -1
    return model.all[data.draw(integers(0, len(model.all) - 1))]


@fieldwise_init
struct Spawn(Command):
    comptime Model = Model
    comptime Sut = Scheduler

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: Model) raises:
        model.all.append(model.next_id)
        model.next_id += 1

    def run(self, model: Model, mut sut: Scheduler) raises:
        assert_equal(sut.spawn(), model.next_id, "id")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("spawn()")


@fieldwise_init
struct Wake(Command):
    comptime Model = Model
    comptime Sut = Scheduler
    var id: Int
    var urgent: Bool

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(draw_task(model, data), data.draw(booleans()))

    def precondition(self, model: Model) raises -> Bool:
        return self.id in model.all

    def next_state(self, mut model: Model) raises:
        if not model.is_ready(self.id):
            if self.urgent:
                model.ready.insert(0, self.id)
            else:
                model.ready.append(self.id)

    def run(self, model: Model, mut sut: Scheduler) raises:
        assert_equal(
            sut.wake(self.id, self.urgent), not model.is_ready(self.id), "woke"
        )
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("wake(", self.id)
        if self.urgent:
            writer.write(", urgent")
        writer.write(")")


@fieldwise_init
struct Block(Command):
    comptime Model = Model
    comptime Sut = Scheduler
    var id: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(draw_task(model, data))

    def precondition(self, model: Model) raises -> Bool:
        return self.id in model.all

    def next_state(self, mut model: Model) raises:
        model.remove_ready(self.id)

    def run(self, model: Model, mut sut: Scheduler) raises:
        assert_equal(sut.block(self.id), model.is_ready(self.id), "blocked")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("block(", self.id, ")")


@fieldwise_init
struct RunNext(Command):
    comptime Model = Model
    comptime Sut = Scheduler

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: Model) raises:
        if len(model.ready) > 0:
            model.ready.append(model.ready.pop(0))

    def run(self, model: Model, mut sut: Scheduler) raises:
        var expected: Optional[Int] = None
        if len(model.ready) > 0:
            expected = model.ready[0]
        assert_equal(sut.run_next(), expected, "ran")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("run_next()")


@fieldwise_init
struct Bump(Command):
    comptime Model = Model
    comptime Sut = Scheduler
    var id: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(draw_task(model, data))

    def precondition(self, model: Model) raises -> Bool:
        return self.id in model.all

    def next_state(self, mut model: Model) raises:
        if model.is_ready(self.id):
            model.remove_ready(self.id)
            model.ready.insert(0, self.id)

    def run(self, model: Model, mut sut: Scheduler) raises:
        assert_equal(sut.bump(self.id), model.is_ready(self.id), "bumped")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("bump(", self.id, ")")


@fieldwise_init
struct WakeAll(Command):
    comptime Model = Model
    comptime Sut = Scheduler

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: Model) raises:
        var woken = List[Int]()
        for id in model.all:
            if not model.is_ready(id):
                woken.append(id)
        model.ready.extend(woken^)

    def run(self, model: Model, mut sut: Scheduler) raises:
        sut.wake_all()
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("wake_all()")


@fieldwise_init
struct Kill(Command):
    comptime Model = Model
    comptime Sut = Scheduler
    var id: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(draw_task(model, data))

    def precondition(self, model: Model) raises -> Bool:
        return self.id in model.all

    def next_state(self, mut model: Model) raises:
        model.remove_ready(self.id)
        for i in range(len(model.all)):
            if model.all[i] == self.id:
                _ = model.all.pop(i)
                return

    def run(self, model: Model, mut sut: Scheduler) raises:
        assert_true(sut.kill(self.id), "killed")
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("kill(", self.id, ")")


# ---- a list on its own


struct Item(Movable):
    var link: ListHead
    var value: Int

    def __init__(out self, value: Int):
        self.link = ListHead()
        self.value = value


comptime Items = IntrusiveList[Item, "link"]


def new_item(value: Int) -> Items.Elem:
    var p = unsafe_alloc[Item](1)
    p.unsafe_write(Item(value))
    var e = Items.Elem(to=p[])
    _init_link(Items.link_of(e))
    return e


def values(l: Items) -> List[Int]:
    var out = List[Int]()
    for e in l.elements():
        out.append(e[].value)
    return out^


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    # The link fields are at different, nonzero offsets, so container_of
    # really subtracts something.
    comptime all_offset = reflect[Task].field_offset[name="all_link"]()
    comptime ready_offset = reflect[Task].field_offset[name="ready_link"]()
    assert_true(0 < all_offset < ready_offset, "field offsets")

    def matches_two_lists(mut data: ConjectureData) raises:
        var sut = Scheduler()
        run_commands[Spawn, Wake, Block, RunNext, Bump, WakeAll, Kill](
            Model([], [], 0), sut, data
        )

    given_data(matches_two_lists, settings)
    print("matches two lists: passed")

    # Moving the scheduler moves neither its tasks nor its lists' heads.
    def survives_a_move(n: Int, ready: List[Bool]) raises:
        var a = Scheduler()
        var model = Model([], [], 0)
        for i in range(n):
            _ = a.spawn()
            model.all.append(i)
            if i < len(ready) and ready[i]:
                _ = a.wake(i)
                model.ready.append(i)
        var b = a^
        check(b, model)
        b.wake_all()
        b.check()

    given(integers(0, 20), lists(booleans()), survives_a_move, settings)
    print("survives a move: passed")

    # Splicing moves every element and leaves the other list empty and
    # usable. (Here the link is the first field, at offset 0.)
    def splicing_empties_the_other_list(
        a_front: List[Bool], b_front: List[Bool]
    ) raises:
        var items = List[Items.Elem]()
        var a = Items()
        var b = Items()
        var model_a = List[Int]()
        var model_b = List[Int]()
        for i in range(len(a_front) + len(b_front)):
            var e = new_item(i)
            items.append(e)
            var to_a = i < len(a_front)
            var front = a_front[i] if to_a else b_front[i - len(a_front)]
            ref l = a if to_a else b
            ref m = model_a if to_a else model_b
            if front:
                l.push_front(e)
                m.insert(0, i)
            else:
                l.push_back(e)
                m.append(i)
        a.splice_back(b)
        model_a.extend(model_b^)
        a.check_links()
        b.check_links()
        assert_true(values(a) == model_a, "spliced")
        assert_equal(len(b), 0)
        assert_equal(len(b.elements()), 0, "the other list is empty")
        var extra = new_item(-1)
        items.append(extra)
        b.push_back(extra)
        b.check_links()
        assert_true(values(b) == [-1], "the other list is reusable")
        for e in items:
            _ = e.unsafe_take_pointee()
            e.unsafe_free()

    given(
        lists(booleans()),
        lists(booleans()),
        splicing_empties_the_other_list,
        settings,
    )
    print("splicing empties the other list: passed")
