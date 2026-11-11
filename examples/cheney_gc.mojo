# A copying garbage collector (Cheney, 1970) for a heap of small objects.
# The heap is two "semispaces" of raw words. Objects are allocated one
# after another in the current space; when it fills up, the collector
# copies every object reachable from the roots into the other space and
# switches spaces. What isn't copied is garbage, and is never looked at.
#
# An object is a header word (its number of fields, shifted left 2) and
# then its fields. A field word is tagged by its low bit: odd words are
# integers (v << 1 | 1), 0 is nil, and any other word is the address of
# an object. Copying an object overwrites its old header with a
# forwarding address (the new address | 1), so an object reached twice is
# copied once, and shared objects and cycles survive.
#
# Cheney's trick is that the to-space is its own queue: the roots are
# copied first, then a scan pointer walks the copied objects, copying
# what their fields point to onto the end, until the scan pointer catches
# up with the allocation pointer. No stack, no recursion: a breadth-first
# traversal in place.
#
# Every pointer is an integer turned back into a pointer, and a copy moves
# objects while the mutator holds handles to them: the mutator holds
# handles (indices into the root table), never addresses, because any
# allocation may move every object. After a collection, the old space is
# filled with a poison pattern, so anything still pointing into it reads
# garbage that the checks catch. (AddressSanitizer sees each space as one
# allocation, so it can't.)
#
# The tests are model-based. The model is the object graph, with objects
# as plain lists of fields; it also replays Cheney's copy order to predict
# every object's address, and which allocations trigger a collection or
# run out of memory. After every command, the graph reachable from the
# roots must be isomorphic to the model's (with shared objects and cycles
# mapped one to one), every object must be where the model says, and the
# heap must parse from start to end with every pointer at an object.
#
#   pixi run mojo run -I . examples/cheney_gc.mojo
#   pixi run mojo build -I . --sanitize address -o gc examples/cheney_gc.mojo && ./gc
#
# Run with PROPTEST_TIMEOUT=1000 so that crashes and hangs shrink too.

from std.collections import Set
from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_false, assert_true

from proptest import *


# ---- the heap

comptime WordPtr = Pointer[Int, MutUntrackedOrigin]
comptime NIL = 0
comptime FORWARDED = 1
comptime POISON = 0x5A5A5A5A5A5A5A5A
"""Written over a space after it's evacuated: not a header (the low bits
are 10), and as a field, a pointer to nowhere."""


def int_word(v: Int) -> Int:
    return (v << 1) | 1


def is_int(w: Int) -> Bool:
    return w & 1 == 1


def is_ref(w: Int) -> Bool:
    return w != NIL and not is_int(w)


struct Heap(Movable):
    """A garbage-collected heap of `capacity` words (per semispace)."""

    var space: WordPtr
    """The current space, where objects are allocated."""
    var other: WordPtr
    """The space the next collection copies into."""
    var capacity: Int
    var used: Int
    """Words allocated in the current space."""
    var roots: List[Int]
    """The root table: a word per handle (NIL once dropped)."""
    var collections: Int

    def __init__(out self, capacity: Int):
        self.capacity = capacity
        self.space = unsafe_alloc[Int](capacity)
        self.other = unsafe_alloc[Int](capacity)
        for i in range(capacity):
            self.space[unsafe_offset=i] = POISON
            self.other[unsafe_offset=i] = POISON
        self.used = 0
        self.roots = []
        self.collections = 0

    def __deinit__(deinit self):
        self.space.unsafe_free()
        self.other.unsafe_free()

    @staticmethod
    def _at(addr: Int) -> WordPtr:
        return WordPtr(unsafe_from_address=addr)

    @staticmethod
    def fields(addr: Int) -> Int:
        """The number of fields of the object at addr."""
        return Self._at(addr)[] >> 2

    @staticmethod
    def field(addr: Int, i: Int) -> WordPtr:
        return Self._at(addr).unsafe_offset(1 + i)

    def offset(self, addr: Int) -> Int:
        """The distance in words from the start of the current space to
        addr."""
        return (addr - Int(self.space)) // 8

    # -- the mutator's interface: handles, never addresses

    def new(mut self, n: Int) -> Optional[Int]:
        """A new object of n nil fields, and a handle to it; None if even a
        collection doesn't free enough room."""
        if self.used + n + 1 > self.capacity:
            self.collect()
            if self.used + n + 1 > self.capacity:
                return None
        var p = self.space.unsafe_offset(self.used)
        p[] = n << 2
        for i in range(n):
            p[unsafe_offset=1 + i] = NIL
        self.used += n + 1
        self.roots.append(Int(p))
        return len(self.roots) - 1

    def get(self, h: Int, i: Int) -> Int:
        """Field i of handle h's object, as a raw word."""
        return Self.field(self.roots[h], i)[]

    def set_int(mut self, h: Int, i: Int, v: Int):
        Self.field(self.roots[h], i)[] = int_word(v)

    def set_ref(mut self, h: Int, i: Int, target: Int):
        Self.field(self.roots[h], i)[] = self.roots[target]

    def set_nil(mut self, h: Int, i: Int):
        Self.field(self.roots[h], i)[] = NIL

    def follow(mut self, h: Int, i: Int) -> Int:
        """A new handle to the object field i of h's object refers to."""
        self.roots.append(self.get(h, i))
        return len(self.roots) - 1

    def drop(mut self, h: Int):
        self.roots[h] = NIL

    # -- the collector

    def collect(mut self):
        """Copy everything reachable from the roots to the other space,
        and switch spaces."""
        var free = 0  # words copied so far
        for k in range(len(self.roots)):
            self.roots[k] = self._forward(self.roots[k], free)
        var scan = 0
        while scan < free:
            var addr = Int(self.other.unsafe_offset(scan))
            var n = Self.fields(addr)
            for i in range(n):
                var f = Self.field(addr, i)
                f[] = self._forward(f[], free)
            scan += n + 1
        # the old space holds only garbage and forwarding addresses now
        for i in range(self.used):
            self.space[unsafe_offset=i] = POISON
        swap(self.space, self.other)
        self.used = free
        self.collections += 1

    def _forward(mut self, w: Int, mut free: Int) -> Int:
        """w's new value: an object is copied (once) to the other space."""
        if not is_ref(w):
            return w
        var header = Self._at(w)[]
        if header & FORWARDED != 0:
            return header & ~FORWARDED
        var size = (header >> 2) + 1
        var to = self.other.unsafe_offset(free)
        for i in range(size):
            to[unsafe_offset=i] = Self._at(w)[unsafe_offset=i]
        free += size
        Self._at(w)[] = Int(to) | FORWARDED
        return Int(to)

    # -- inspection

    def objects(self) raises -> List[Int]:
        """The addresses of the objects in the current space, in order.
        Raises unless the space parses as objects from start to `used`."""
        var out = List[Int]()
        var i = 0
        while i < self.used:
            var addr = Int(self.space.unsafe_offset(i))
            var header = Self._at(addr)[]
            if header & 3 != 0 or header < 0:
                raise Error("a bad header at word ", i, ": ", header)
            out.append(addr)
            i += Self.fields(addr) + 1
        if i != self.used:
            raise Error("the last object runs past the allocated words")
        return out^

    def check(self) raises:
        """Raise unless the space parses, and every pointer (in an object or
        a root) is the address of an object in it."""
        var objects = self.objects()
        var starts = Set[Int]()
        for a in objects:
            starts.add(a)
        for a in objects:
            for i in range(Self.fields(a)):
                var w = Self.field(a, i)[]
                if is_ref(w) and w not in starts:
                    raise Error("a field points outside the heap's objects")
        for w in self.roots:
            if is_ref(w) and w not in starts:
                raise Error("a root points outside the heap's objects")


# ---- the model: an object graph


@fieldwise_init
struct Field(Copyable, Equatable):
    var kind: Int
    """NIL_FIELD, INT_FIELD, or REF_FIELD."""
    var value: Int
    """The integer, or the object id."""


comptime NIL_FIELD = 0
comptime INT_FIELD = 1
comptime REF_FIELD = 2


@fieldwise_init
struct Model(Copyable):
    var objects: List[List[Field]]
    """Every object ever allocated, by id (the model never frees)."""
    var offsets: List[Int]
    """Where each object is in the current space (live objects only)."""
    var handles: List[Int]
    """Each handle's object id, or -1 once dropped."""
    var used: Int
    var capacity: Int

    @staticmethod
    def empty(capacity: Int) -> Self:
        return Self([], [], [], 0, capacity)

    def size(self, id: Int) -> Int:
        return len(self.objects[id]) + 1

    def collect(mut self):
        """Cheney's copy order: the roots in handle order, then a
        breadth-first scan of the copies' fields."""
        var copied = Set[Int]()
        var queue = List[Int]()
        var free = 0
        for h in range(len(self.handles)):
            var id = self.handles[h]
            if id >= 0 and id not in copied:
                copied.add(id)
                queue.append(id)
                self.offsets[id] = free
                free += self.size(id)
        var scan = 0
        while scan < len(queue):
            var id = queue[scan]
            for f in self.objects[id]:
                if f.kind == REF_FIELD and f.value not in copied:
                    copied.add(f.value)
                    queue.append(f.value)
                    self.offsets[f.value] = free
                    free += self.size(f.value)
            scan += 1
        self.used = free

    def new(mut self, n: Int) -> Optional[Int]:
        if self.used + n + 1 > self.capacity:
            self.collect()
            if self.used + n + 1 > self.capacity:
                return None
        var fields = List[Field]()
        for _ in range(n):
            fields.append(Field(NIL_FIELD, 0))
        self.objects.append(fields^)
        self.offsets.append(self.used)
        self.used += n + 1
        self.handles.append(len(self.objects) - 1)
        return len(self.handles) - 1

    def live_handles(self) -> List[Int]:
        var out = List[Int]()
        for h in range(len(self.handles)):
            if self.handles[h] >= 0:
                out.append(h)
        return out^

    def field_count(self, h: Int) -> Int:
        return len(self.objects[self.handles[h]])


def check(heap: Heap, model: Model) raises:
    """The heap reachable from the roots is isomorphic to the model's
    graph, with every object at the model's offset."""
    heap.check()
    assert_equal(len(heap.roots), len(model.handles), "handles")
    assert_equal(heap.used, model.used, "words in use")
    var heap_to_model = Dict[Int, Int]()
    var model_to_heap = Dict[Int, Int]()
    var stack = List[Tuple[Int, Int]]()
    for h in range(len(model.handles)):
        var id = model.handles[h]
        var w = heap.roots[h]
        if id < 0:
            assert_equal(w, NIL, "a dropped root")
        else:
            assert_true(is_ref(w), "a live root isn't a pointer")
            stack.append((w, id))
    while len(stack) > 0:
        var pair = stack.pop()
        var addr = pair[0]
        var id = pair[1]
        if addr in heap_to_model or id in model_to_heap:
            if heap_to_model.get(addr) != Optional(id) or model_to_heap.get(
                id
            ) != Optional(addr):
                raise Error("object ", id, " isn't one heap object")
            continue
        heap_to_model[addr] = id
        model_to_heap[id] = addr
        assert_equal(heap.offset(addr), model.offsets[id], "object's offset")
        ref fields = model.objects[id]
        assert_equal(Heap.fields(addr), len(fields), "number of fields")
        for i in range(len(fields)):
            var w = Heap.field(addr, i)[]
            var f = fields[i].copy()
            if f.kind == NIL_FIELD:
                assert_equal(w, NIL, "a nil field")
            elif f.kind == INT_FIELD:
                assert_equal(w, int_word(f.value), "an integer field")
            else:
                assert_true(is_ref(w), "a pointer field")
                stack.append((w, f.value))


def draw_handle(model: Model, mut data: ConjectureData) raises -> Int:
    var live = model.live_handles()
    if len(live) == 0:
        return -1
    return live[data.draw(integers(0, len(live) - 1))]


def draw_field(model: Model, h: Int, mut data: ConjectureData) raises -> Int:
    if h < 0 or model.field_count(h) == 0:
        return 0
    return data.draw(integers(0, model.field_count(h) - 1))


def has_field(model: Model, h: Int, i: Int) -> Bool:
    return (
        0 <= h < len(model.handles)
        and model.handles[h] >= 0
        and i < model.field_count(h)
    )


@fieldwise_init
struct New(Command):
    comptime Model = Model
    comptime Sut = Heap
    var fields: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 4)))

    def next_state(self, mut model: Model) raises:
        _ = model.new(self.fields)

    def run(self, model: Model, mut sut: Heap) raises:
        var after = model.copy()
        assert_equal(sut.new(self.fields), after.new(self.fields), "handle")
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("new(", self.fields, ")")


@fieldwise_init
struct SetInt(Command):
    comptime Model = Model
    comptime Sut = Heap
    var handle: Int
    var field: Int
    var value: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        var h = draw_handle(model, data)
        return Self(h, draw_field(model, h, data), data.draw(integers(-9, 9)))

    def precondition(self, model: Model) raises -> Bool:
        return has_field(model, self.handle, self.field)

    def next_state(self, mut model: Model) raises:
        model.objects[model.handles[self.handle]][self.field] = Field(
            INT_FIELD, self.value
        )

    def run(self, model: Model, mut sut: Heap) raises:
        sut.set_int(self.handle, self.field, self.value)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("#", self.handle, ".", self.field, " = ", self.value)


@fieldwise_init
struct SetRef(Command):
    comptime Model = Model
    comptime Sut = Heap
    var handle: Int
    var field: Int
    var target: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        var h = draw_handle(model, data)
        return Self(h, draw_field(model, h, data), draw_handle(model, data))

    def precondition(self, model: Model) raises -> Bool:
        return (
            has_field(model, self.handle, self.field)
            and 0 <= self.target < len(model.handles)
            and model.handles[self.target] >= 0
        )

    def next_state(self, mut model: Model) raises:
        model.objects[model.handles[self.handle]][self.field] = Field(
            REF_FIELD, model.handles[self.target]
        )

    def run(self, model: Model, mut sut: Heap) raises:
        sut.set_ref(self.handle, self.field, self.target)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("#", self.handle, ".", self.field, " = #", self.target)


@fieldwise_init
struct SetNil(Command):
    comptime Model = Model
    comptime Sut = Heap
    var handle: Int
    var field: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        var h = draw_handle(model, data)
        return Self(h, draw_field(model, h, data))

    def precondition(self, model: Model) raises -> Bool:
        return has_field(model, self.handle, self.field)

    def next_state(self, mut model: Model) raises:
        model.objects[model.handles[self.handle]][self.field] = Field(
            NIL_FIELD, 0
        )

    def run(self, model: Model, mut sut: Heap) raises:
        sut.set_nil(self.handle, self.field)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("#", self.handle, ".", self.field, " = nil")


@fieldwise_init
struct Follow(Command):
    """A new handle to the object a field refers to, so objects can stay
    reachable after the handle they were made with is dropped."""

    comptime Model = Model
    comptime Sut = Heap
    var handle: Int
    var field: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        var h = draw_handle(model, data)
        return Self(h, draw_field(model, h, data))

    def precondition(self, model: Model) raises -> Bool:
        return (
            has_field(model, self.handle, self.field)
            and model.objects[model.handles[self.handle]][self.field].kind
            == REF_FIELD
        )

    def next_state(self, mut model: Model) raises:
        model.handles.append(
            model.objects[model.handles[self.handle]][self.field].value
        )

    def run(self, model: Model, mut sut: Heap) raises:
        assert_equal(
            sut.follow(self.handle, self.field), len(model.handles), "handle"
        )
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("follow(#", self.handle, ".", self.field, ")")


@fieldwise_init
struct Drop(Command):
    comptime Model = Model
    comptime Sut = Heap
    var handle: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(draw_handle(model, data))

    def precondition(self, model: Model) raises -> Bool:
        return (
            0 <= self.handle < len(model.handles)
            and model.handles[self.handle] >= 0
        )

    def next_state(self, mut model: Model) raises:
        model.handles[self.handle] = -1

    def run(self, model: Model, mut sut: Heap) raises:
        sut.drop(self.handle)
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("drop(#", self.handle, ")")


@fieldwise_init
struct Collect(Command):
    comptime Model = Model
    comptime Sut = Heap

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: Model) raises:
        model.collect()

    def run(self, model: Model, mut sut: Heap) raises:
        sut.collect()
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("collect()")


# ---- properties

comptime CAPACITY = 24


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_the_model(mut data: ConjectureData) raises:
        var heap = Heap(CAPACITY)
        run_commands[New, SetInt, SetRef, SetNil, Follow, Drop, Collect](
            Model.empty(CAPACITY), heap, data
        )

    given_data(matches_the_model, settings)
    print("matches the model: passed")

    # A cycle of n objects, reachable from one handle, survives collections
    # with its shape (and nothing else survives).
    def a_cycle_survives(n: Int, collections: Int) raises:
        var heap = Heap(CAPACITY)
        var first = heap.new(2).value()
        heap.set_int(first, 1, 0)
        var prev = first
        for k in range(1, n):
            var h = heap.new(2).value()
            heap.set_int(h, 1, k)
            heap.set_ref(prev, 0, h)
            if prev != first:
                heap.drop(prev)
            prev = h
        heap.set_ref(prev, 0, first)
        if prev != first:
            heap.drop(prev)
        for _ in range(collections):
            heap.collect()
            heap.check()
            assert_equal(heap.used, 3 * n)
        # walk the cycle through handles: a raw address taken from the
        # heap wouldn't keep it alive, and Mojo destroys values after
        # their last use
        var h = first
        for k in range(n + 1):
            assert_equal(heap.get(h, 1), int_word(k % n))
            h = heap.follow(h, 0)

    given(
        integers(1, CAPACITY // 3), integers(0, 3), a_cycle_survives, settings
    )
    print("a cycle survives: passed")

    # Allocation succeeds exactly while the live objects fit, collecting
    # first when the space is full. Objects are dropped (made garbage) as
    # drawn, so a collection can free exactly enough room.
    def fills_to_capacity(sizes: List[Int], drops: List[Bool]) raises:
        var heap = Heap(CAPACITY)
        var model = Model.empty(CAPACITY)
        for k in range(len(sizes)):
            var h = heap.new(sizes[k])
            assert_equal(h, model.new(sizes[k]), String("new(", sizes[k], ")"))
            if h and k < len(drops) and drops[k]:
                heap.drop(h.value())
                model.handles[h.value()] = -1
            check(heap, model)

    given(
        lists(integers(0, 4), max_size=20),
        lists(booleans(), max_size=20),
        fills_to_capacity,
        settings,
    )
    print("fills to capacity: passed")

    # Moving the heap doesn't move its spaces.
    def survives_a_move(sizes: List[Int]) raises:
        var a = Heap(CAPACITY)
        for n in sizes:
            _ = a.new(n)
        var used = a.used
        var b = a^
        b.check()
        assert_equal(b.used, used)
        b.collect()
        b.check()

    given(lists(integers(0, 4)), survives_a_move, settings)
    print("survives a move: passed")
