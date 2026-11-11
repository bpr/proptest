# A malloc-style allocator inside one arena, with Knuth's boundary tags.
# Each block starts with a header word and ends with a footer word, both
# holding the block's size OR a used bit. A free block also stores the
# addresses of the next and previous free blocks in its own payload bytes:
# memory that was a user's data a moment ago is reinterpreted as pointers.
# The free blocks form a ring through a sentinel block at the start of the
# arena, so the list has no ends to check.
#
# - alloc is first fit along the free list, splitting off what's left
#   over when it's big enough to be a block.
# - free merges the block with a free neighbor on either side (found with
#   the next block's header and the previous block's footer), so no two
#   free blocks are ever adjacent.
# - realloc shrinks in place, grows in place into a free next block, or
#   moves the data.
# - Every new free block goes to the front of the free list.
#
# The tests are model-based. The model is the same allocator written over
# plain lists of integers (block offsets and sizes, and the free list's
# order), so it predicts every address the allocator returns. After each
# command they compare every block and the free list in both directions,
# check each header against its footer, and check that every live
# allocation still holds the bytes written to it.
#
#   pixi run mojo run -I . examples/free_list_allocator.mojo
#   pixi run mojo build -I . --sanitize address -o fl examples/free_list_allocator.mojo && ./fl
#
# AddressSanitizer sees the arena as one allocation, so it can't see a
# block overrun; the byte patterns and boundary tags are the checks here.
# Run with PROPTEST_TIMEOUT=1000 so that crashes and hangs (a broken free
# list can loop forever) shrink too.

from std.memory import Pointer, unsafe_memmove
from std.memory.alloc import unsafe_alloc
from std.testing import assert_equal, assert_false, assert_true

from proptest import *


# ---- the allocator

comptime BytePtr = Pointer[UInt8, MutUntrackedOrigin]
comptime WordPtr = Pointer[Int, MutUntrackedOrigin]

comptime WORD = 8
comptime ALIGN = 16
comptime USED = 1
comptime MIN_BLOCK = 32
"""A header, the two free-list pointers, and a footer."""


def block_size(n: Int) -> Int:
    """The size of the block that holds n bytes: payload, header, and
    footer, rounded up to the alignment."""
    return max(MIN_BLOCK, (n + 2 * WORD + ALIGN - 1) & ~(ALIGN - 1))


struct FreeListAllocator(Movable):
    """A first-fit allocator of an arena of `capacity` bytes."""

    var base: BytePtr
    """The arena, from the system allocator."""
    var capacity: Int
    var head: BytePtr
    """The sentinel: a used block whose free-list links begin the ring."""
    var first: BytePtr
    """The first real block; the blocks end at a header of size 0."""

    def __init__(out self, capacity: Int):
        debug_assert(
            capacity >= MIN_BLOCK and capacity % ALIGN == 0,
            "FreeListAllocator: bad capacity",
        )
        # 8 bytes of padding, the sentinel, the blocks, and an end header,
        # so that payloads (8 bytes into a block) are 16-byte aligned
        self.capacity = capacity
        self.base = unsafe_alloc[UInt8](capacity + 48, alignment=ALIGN)
        self.head = self.base.unsafe_offset(WORD)
        self.first = self.head.unsafe_offset(MIN_BLOCK)
        # UNSAFE: lays out the empty arena
        Self._set(self.head, MIN_BLOCK, USED)
        Self._set_next(self.head, self.head)
        Self._set_prev(self.head, self.head)
        Self._set(self.first, capacity, 0)
        Self._word(self.first.unsafe_offset(capacity))[] = 0 | USED
        self._push_front(self.first)

    def __deinit__(deinit self):
        self.base.unsafe_free()

    # -- boundary tags and free-list links, read from the arena's bytes

    @staticmethod
    def _word(p: BytePtr) -> WordPtr:
        return p.unsafe_bitcast[Int]()

    @staticmethod
    def _size(b: BytePtr) -> Int:
        return Self._word(b)[] & ~(ALIGN - 1)

    @staticmethod
    def _used(b: BytePtr) -> Bool:
        return Self._word(b)[] & USED != 0

    @staticmethod
    def _set(b: BytePtr, size: Int, used: Int):
        """Write b's header and footer."""
        Self._word(b)[] = size | used
        Self._word(b.unsafe_offset(size - WORD))[] = size | used

    @staticmethod
    def _next(b: BytePtr) -> BytePtr:
        return b.unsafe_offset(WORD).unsafe_bitcast[BytePtr]()[]

    @staticmethod
    def _prev(b: BytePtr) -> BytePtr:
        return b.unsafe_offset(2 * WORD).unsafe_bitcast[BytePtr]()[]

    @staticmethod
    def _set_next(b: BytePtr, n: BytePtr):
        b.unsafe_offset(WORD).unsafe_bitcast[BytePtr]()[] = n

    @staticmethod
    def _set_prev(b: BytePtr, p: BytePtr):
        b.unsafe_offset(2 * WORD).unsafe_bitcast[BytePtr]()[] = p

    def _push_front(mut self, b: BytePtr):
        var n = Self._next(self.head)
        Self._set_next(b, n)
        Self._set_prev(b, self.head)
        Self._set_prev(n, b)
        Self._set_next(self.head, b)

    @staticmethod
    def _unlink(b: BytePtr):
        var p = Self._prev(b)
        var n = Self._next(b)
        Self._set_next(p, n)
        Self._set_prev(n, p)

    def _place(mut self, b: BytePtr, need: Int, size: Int):
        """Make the unlinked block b (of `size` bytes, at least `need`)
        used, and free what's left over if it can be a block."""
        if size - need >= MIN_BLOCK:
            Self._set(b, need, USED)
            var rest = b.unsafe_offset(need)
            Self._set(rest, size - need, 0)
            self._push_front(rest)
        else:
            Self._set(b, size, USED)

    # -- the allocator

    def alloc(mut self, n: Int) -> Optional[BytePtr]:
        """At least n bytes, 16-byte aligned; None if no free block is big
        enough."""
        var need = block_size(n)
        var b = Self._next(self.head)
        while b != self.head:
            var size = Self._size(b)
            if size >= need:
                Self._unlink(b)
                self._place(b, need, size)
                return b.unsafe_offset(WORD)
            b = Self._next(b)
        return None

    def free(mut self, p: BytePtr):
        """Free memory from alloc or realloc."""
        var b = p.unsafe_offset(-WORD)
        debug_assert(Self._used(b), "FreeListAllocator.free: not in use")
        var size = Self._size(b)
        var after = b.unsafe_offset(size)
        if not Self._used(after):
            Self._unlink(after)
            size += Self._size(after)
        var before_tag = Self._word(b.unsafe_offset(-WORD))[]
        if before_tag & USED == 0:
            var before_size = before_tag & ~(ALIGN - 1)
            b = b.unsafe_offset(-before_size)
            Self._unlink(b)
            size += before_size
        Self._set(b, size, 0)
        self._push_front(b)

    def realloc(mut self, p: BytePtr, n: Int) -> Optional[BytePtr]:
        """Resize the allocation at p to n bytes, keeping its contents up to
        the smaller size. None (leaving it as it was) if there's no room."""
        var b = p.unsafe_offset(-WORD)
        var size = Self._size(b)
        var need = block_size(n)
        if need <= size:
            if size - need >= MIN_BLOCK:
                # free the tail (merging it with a free next block)
                Self._set(b, need, USED)
                Self._set(b.unsafe_offset(need), size - need, USED)
                self.free(b.unsafe_offset(need + WORD))
            return p
        var after = b.unsafe_offset(size)
        if not Self._used(after) and size + Self._size(after) >= need:
            Self._unlink(after)
            self._place(b, need, size + Self._size(after))
            return p
        var q = self.alloc(n)
        if not q:
            return None
        unsafe_memmove(dest=q.value(), src=p, count=min(size - 2 * WORD, n))
        self.free(p)
        return q

    # -- inspection

    def offset(self, p: BytePtr) -> Int:
        """A payload's offset from the first block."""
        return Int(p) - Int(self.first) - WORD

    def payload(self, offset: Int) -> BytePtr:
        return self.first.unsafe_offset(offset + WORD)

    def blocks(self) -> List[Tuple[Int, Int, Bool]]:
        """(offset, size, used) for each block, in address order."""
        var out = List[Tuple[Int, Int, Bool]]()
        var b = self.first
        while Self._size(b) != 0 and len(out) <= self.capacity // ALIGN:
            out.append((Int(b) - Int(self.first), Self._size(b), Self._used(b)))
            b = b.unsafe_offset(Self._size(b))
        return out^

    def free_list(self, reverse: Bool = False) -> List[Int]:
        """The free blocks' offsets, in free-list order."""
        var out = List[Int]()
        var b = Self._prev(self.head) if reverse else Self._next(self.head)
        while b != self.head and len(out) <= self.capacity // MIN_BLOCK:
            out.append(Int(b) - Int(self.first))
            b = Self._prev(b) if reverse else Self._next(b)
        return out^

    def check(self) raises:
        """Raise unless the blocks tile the arena with matching headers and
        footers, no two free blocks are adjacent, and the free list is a
        ring of exactly the free blocks."""
        if Self._word(self.head)[] != MIN_BLOCK | USED:
            raise Error("the sentinel's header is overwritten")
        if Self._word(self.first.unsafe_offset(-WORD))[] != MIN_BLOCK | USED:
            raise Error("the sentinel's footer is overwritten")
        var b = self.first
        var end = self.first.unsafe_offset(self.capacity)
        var free_blocks = 0
        var prev_free = False
        while b != end:
            if Int(b) > Int(end):
                raise Error("a block runs past the end of the arena")
            var size = Self._size(b)
            if size < MIN_BLOCK or size % ALIGN != 0:
                raise Error("a block of ", size, " bytes")
            if Self._word(b)[] != Self._word(b.unsafe_offset(size - WORD))[]:
                raise Error("a header and footer disagree")
            var is_free = not Self._used(b)
            if is_free and prev_free:
                raise Error("two adjacent free blocks")
            if is_free:
                free_blocks += 1
            prev_free = is_free
            b = b.unsafe_offset(size)
        if Self._word(end)[] != USED:
            raise Error("the end header is overwritten")
        var f = self.head
        for i in range(free_blocks + 1):
            if Self._prev(Self._next(f)) != f:
                raise Error("a free block's next doesn't point back")
            f = Self._next(f)
            if f == self.head:
                if i != free_blocks:
                    raise Error(
                        "the free list has ", i, " blocks, not ", free_blocks
                    )
                return
            if Self._used(f):
                raise Error("a used block is on the free list")
        raise Error("the free list doesn't come back to the sentinel")


# ---- the model: the same allocator over lists of integers


@fieldwise_init
struct Model(Copyable):
    var offsets: List[Int]
    var sizes: List[Int]
    var used: List[Bool]
    """The blocks, in address order."""
    var free: List[Int]
    """Offsets of the free blocks, in free-list order."""
    var handles: List[Int]
    var at: List[Int]
    var lengths: List[Int]
    """Each live allocation: its handle, block offset, and length."""
    var next_handle: Int

    @staticmethod
    def empty(capacity: Int) -> Self:
        return Self([0], [capacity], [False], [0], [], [], [], 0)

    def _block(self, offset: Int) -> Int:
        for i in range(len(self.offsets)):
            if self.offsets[i] == offset:
                return i
        return -1

    def _unlink(mut self, offset: Int):
        for i in range(len(self.free)):
            if self.free[i] == offset:
                _ = self.free.pop(i)
                return

    def _place(mut self, i: Int, need: Int):
        var size = self.sizes[i]
        self.used[i] = True
        if size - need >= MIN_BLOCK:
            self.sizes[i] = need
            self.offsets.insert(i + 1, self.offsets[i] + need)
            self.sizes.insert(i + 1, size - need)
            self.used.insert(i + 1, False)
            self.free.insert(0, self.offsets[i] + need)

    def alloc_block(mut self, n: Int) -> Optional[Int]:
        var need = block_size(n)
        for k in range(len(self.free)):
            var offset = self.free[k]
            var i = self._block(offset)
            if self.sizes[i] >= need:
                self._unlink(offset)
                self._place(i, need)
                return offset
        return None

    def free_block(mut self, offset: Int):
        var i = self._block(offset)
        self.used[i] = False
        if i + 1 < len(self.offsets) and not self.used[i + 1]:
            self._unlink(self.offsets[i + 1])
            self.sizes[i] += self.sizes[i + 1]
            _ = self.offsets.pop(i + 1)
            _ = self.sizes.pop(i + 1)
            _ = self.used.pop(i + 1)
        if i > 0 and not self.used[i - 1]:
            self._unlink(self.offsets[i - 1])
            self.sizes[i - 1] += self.sizes[i]
            _ = self.offsets.pop(i)
            _ = self.sizes.pop(i)
            _ = self.used.pop(i)
            i -= 1
        self.free.insert(0, self.offsets[i])

    def realloc_block(mut self, offset: Int, n: Int) -> Optional[Int]:
        var i = self._block(offset)
        var size = self.sizes[i]
        var need = block_size(n)
        if need <= size:
            if size - need >= MIN_BLOCK:
                self.sizes[i] = need
                self.offsets.insert(i + 1, offset + need)
                self.sizes.insert(i + 1, size - need)
                self.used.insert(i + 1, True)
                self.free_block(offset + need)
            return offset
        if (
            i + 1 < len(self.offsets)
            and not self.used[i + 1]
            and size + self.sizes[i + 1] >= need
        ):
            self._unlink(self.offsets[i + 1])
            self.sizes[i] += self.sizes[i + 1]
            _ = self.offsets.pop(i + 1)
            _ = self.sizes.pop(i + 1)
            _ = self.used.pop(i + 1)
            self._place(i, need)
            return offset
        var moved = self.alloc_block(n)
        if moved:
            self.free_block(offset)
        return moved

    def live(self, handle: Int) -> Int:
        """The index of a live handle, or -1."""
        for i in range(len(self.handles)):
            if self.handles[i] == handle:
                return i
        return -1


comptime CAPACITY = 1024
comptime MAX_REQUEST = 300


def pattern(handle: Int, i: Int) -> UInt8:
    return UInt8((handle * 31 + i * 7 + 1) % 256)


def fill(p: BytePtr, handle: Int, start: Int, end: Int):
    for i in range(start, end):
        p[unsafe_offset=i] = pattern(handle, i)


def check(sut: FreeListAllocator, model: Model) raises:
    sut.check()
    var blocks = sut.blocks()
    assert_equal(len(blocks), len(model.offsets), "number of blocks")
    for i in range(len(blocks)):
        assert_equal(blocks[i][0], model.offsets[i], "block offset")
        assert_equal(blocks[i][1], model.sizes[i], "block size")
        assert_equal(blocks[i][2], model.used[i], "block in use")
    assert_true(sut.free_list() == model.free, "free list")
    var backward = model.free.copy()
    backward.reverse()
    assert_true(sut.free_list(reverse=True) == backward, "free list, reversed")
    for k in range(len(model.handles)):
        var p = sut.payload(model.at[k])
        assert_equal(Int(p) % ALIGN, 0, "alignment")
        for i in range(model.lengths[k]):
            if p[unsafe_offset=i] != pattern(model.handles[k], i):
                raise Error("allocation ", model.handles[k], " lost byte ", i)


def draw_handle(model: Model, mut data: ConjectureData) raises -> Int:
    if len(model.handles) == 0:
        return -1
    return model.handles[data.draw(integers(0, len(model.handles) - 1))]


@fieldwise_init
struct Alloc(Command):
    comptime Model = Model
    comptime Sut = FreeListAllocator
    var size: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, MAX_REQUEST)))

    def next_state(self, mut model: Model) raises:
        var offset = model.alloc_block(self.size)
        if offset:
            model.handles.append(model.next_handle)
            model.at.append(offset.value())
            model.lengths.append(self.size)
            model.next_handle += 1

    def run(self, model: Model, mut sut: FreeListAllocator) raises:
        var after = model.copy()
        self.next_state(after)
        var p = sut.alloc(self.size)
        if len(after.handles) == len(model.handles):
            assert_false(Bool(p), "alloc should fail")
        else:
            assert_true(Bool(p), "alloc failed")
            assert_equal(sut.offset(p.value()), after.at[len(after.at) - 1])
            fill(p.value(), model.next_handle, 0, self.size)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("alloc(", self.size, ")")


@fieldwise_init
struct Free(Command):
    comptime Model = Model
    comptime Sut = FreeListAllocator
    var handle: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(draw_handle(model, data))

    def precondition(self, model: Model) raises -> Bool:
        return model.live(self.handle) >= 0

    def next_state(self, mut model: Model) raises:
        var k = model.live(self.handle)
        model.free_block(model.at[k])
        _ = model.handles.pop(k)
        _ = model.at.pop(k)
        _ = model.lengths.pop(k)

    def run(self, model: Model, mut sut: FreeListAllocator) raises:
        sut.free(sut.payload(model.at[model.live(self.handle)]))
        var after = model.copy()
        self.next_state(after)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("free(#", self.handle, ")")


@fieldwise_init
struct Realloc(Command):
    comptime Model = Model
    comptime Sut = FreeListAllocator
    var handle: Int
    var size: Int

    @staticmethod
    def generate(model: Model, mut data: ConjectureData) raises -> Self:
        return Self(
            draw_handle(model, data), data.draw(integers(0, MAX_REQUEST))
        )

    def precondition(self, model: Model) raises -> Bool:
        return model.live(self.handle) >= 0

    def next_state(self, mut model: Model) raises:
        var k = model.live(self.handle)
        var moved = model.realloc_block(model.at[k], self.size)
        if moved:
            model.at[k] = moved.value()
            model.lengths[k] = self.size

    def run(self, model: Model, mut sut: FreeListAllocator) raises:
        var k = model.live(self.handle)
        var after = model.copy()
        self.next_state(after)
        var p = sut.realloc(sut.payload(model.at[k]), self.size)
        if not p:
            assert_equal(after.lengths[k], model.lengths[k], "realloc failed")
            assert_equal(after.at[k], model.at[k], "realloc failed")
        else:
            assert_equal(sut.offset(p.value()), after.at[k], "realloc moved")
            # the old contents are there; write the rest
            var kept = min(model.lengths[k], self.size)
            for i in range(kept):
                if p.value()[unsafe_offset=i] != pattern(self.handle, i):
                    raise Error("realloc lost byte ", i)
            fill(p.value(), self.handle, kept, self.size)
        check(sut, after)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("realloc(#", self.handle, ", ", self.size, ")")


# ---- properties


def main() raises:
    var settings = Settings(database=None, max_examples=500)

    def matches_the_model(mut data: ConjectureData) raises:
        var sut = FreeListAllocator(CAPACITY)
        run_commands[Alloc, Free, Realloc](Model.empty(CAPACITY), sut, data)

    given_data(matches_the_model, settings)
    print("matches the model: passed")

    # Freeing everything, in any order, merges the arena back into one
    # free block.
    def freeing_everything_merges(sizes: List[Int], order: List[Int]) raises:
        var a = FreeListAllocator(CAPACITY)
        var ptrs = List[BytePtr]()
        for n in sizes:
            var p = a.alloc(n)
            if p:
                ptrs.append(p.value())
        for i in order:
            if len(ptrs) == 0:
                break
            a.free(ptrs.pop(i % len(ptrs)))
            a.check()
        for p in ptrs:
            a.free(p)
        a.check()
        var blocks = a.blocks()
        assert_equal(len(blocks), 1)
        assert_equal(blocks[0][1], CAPACITY)
        assert_false(blocks[0][2])

    given(
        lists(integers(0, MAX_REQUEST // 3)),
        lists(integers(0, 100)),
        freeing_everything_merges,
        settings,
    )
    print("freeing everything merges: passed")

    # Moving the allocator doesn't move its arena.
    def survives_a_move(sizes: List[Int]) raises:
        var a = FreeListAllocator(CAPACITY)
        for n in sizes:
            _ = a.alloc(n)
        var before = a.blocks()
        var b = a^
        b.check()
        assert_equal(len(b.blocks()), len(before))

    given(lists(integers(0, MAX_REQUEST)), survives_a_move, settings)
    print("survives a move: passed")
