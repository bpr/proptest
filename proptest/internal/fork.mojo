# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Running test cases in a child process (`Settings(fork=True)`), after
Rust proptest's `fork` option. Not in Hypothesis.

A test that crashes (a segfault, an abort, an AddressSanitizer report)
would kill the whole run before anything was shrunk. With `fork`, each
test case runs in a `fork()`ed child. The child records what it does in
a log, in memory shared with the parent: each choice and span as it is
made, the notes of the final replay, and at the end the rest of the test
case's result. If the child dies before the end, the parent rebuilds the
test case from the log, up to the crash, as a failure whose origin is
the signal. Shrinking then works on crashes as on any other failure.

The log holds records of a tag byte and a payload, after a header of the
committed length and an overflow flag. A record is committed (the length
updated) only once it is completely written, so a crash in the middle of
one can't leave a torn record.
"""

from std.collections import Dict
from std.ffi import external_call, get_errno, ErrNo
from std.memory import ArcPointer, Pointer
from std.sys.info import CompilationTarget

from proptest.internal.choice import ChoiceValue, Constraints
from proptest.internal.intervals import IntervalSet


comptime LOG_SIZE = 64 * 1024 * 1024
"""Bytes of address space reserved for one test case's log; only the
pages written are ever backed by memory."""

comptime _HEADER = 16
"""The committed length (8 bytes) and the overflow flag (8 bytes)."""

comptime TAG_NODE: UInt8 = 1
comptime TAG_SPAN_START: UInt8 = 2
comptime TAG_SPAN_STOP: UInt8 = 3
comptime TAG_ARG_SPAN: UInt8 = 4
comptime TAG_NOTE: UInt8 = 5
comptime TAG_END: UInt8 = 6

comptime _BytePtr = Pointer[UInt8, MutUntrackedOrigin]
comptime _WordPtr = Pointer[Int, MutUntrackedOrigin]


# ===----------------------------------------------------------------------=== #
# Shared memory
# ===----------------------------------------------------------------------=== #


def map_shared(size: Int) -> Int:
    """The address of `size` bytes of anonymous memory shared with child
    processes, or 0 if mmap fails."""
    comptime PROT_READ_WRITE = Int32(3)
    comptime MAP_SHARED = Int32(0x01)
    comptime MAP_ANONYMOUS = Int32(
        0x1000
    ) if CompilationTarget.is_macos() else Int32(0x20)
    comptime MAP_NORESERVE = Int32(
        0x40
    ) if CompilationTarget.is_macos() else Int32(0x4000)
    var addr = external_call["mmap", Int](
        Int(0),
        size,
        PROT_READ_WRITE,
        MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE,
        Int32(-1),
        Int(0),
    )
    if addr == -1:  # MAP_FAILED
        return 0
    _WordPtr(unsafe_from_address=addr)[] = 0
    _WordPtr(unsafe_from_address=addr + 8)[] = 0
    return addr


def unmap_shared(addr: Int, size: Int):
    _ = external_call["munmap", Int32](addr, size)


# ===----------------------------------------------------------------------=== #
# Writing (in the child)
# ===----------------------------------------------------------------------=== #


struct ForkLog(Movable):
    """The child's end of the log."""

    var base: Int
    var size: Int
    var pos: Int
    """The end of the record being written."""
    var overflowed: Bool
    var interval_ids: Dict[Int, Int]
    """Interval sets already written, by address."""
    var keep_alive: List[ArcPointer[IntervalSet]]
    """The sets in `interval_ids`, kept alive so that their addresses
    aren't reused by other sets during the test case."""
    var weight_ids: Dict[Int, Int]
    var keep_weights: List[ArcPointer[List[Float64]]]

    def __init__(out self, base: Int, size: Int):
        self.base = base
        self.size = size
        self.pos = _HEADER
        self.overflowed = False
        self.interval_ids = {}
        self.keep_alive = []
        self.weight_ids = {}
        self.keep_weights = []

    def begin(mut self, tag: UInt8):
        self.u8(tag)

    def commit(mut self):
        """Publish the record written since the last commit."""
        if self.overflowed:
            return
        _WordPtr(unsafe_from_address=self.base)[] = self.pos - _HEADER

    def u8(mut self, v: UInt8):
        if self.pos + 1 > self.size:
            self._overflow()
            return
        _BytePtr(unsafe_from_address=self.base + self.pos)[] = v
        self.pos += 1

    def u64(mut self, v: UInt64):
        if self.pos + 8 > self.size:
            self._overflow()
            return
        for k in range(8):
            _BytePtr(unsafe_from_address=self.base + self.pos + k)[] = UInt8(
                (v >> UInt64(8 * k)) & 0xFF
            )
        self.pos += 8

    def int(mut self, v: Int):
        self.u64(UInt64(v))

    def i128(mut self, v: Int128):
        self.u64(UInt64(v & 0xFFFF_FFFF_FFFF_FFFF))
        self.u64(UInt64((v >> 64) & 0xFFFF_FFFF_FFFF_FFFF))

    def f64(mut self, v: Float64):
        self.u64(UInt64(v.to_bits()))

    def bool(mut self, v: Bool):
        self.u8(UInt8(1) if v else UInt8(0))

    def string(mut self, s: String):
        var bytes = s.as_bytes()
        self.int(len(bytes))
        for b in bytes:
            self.u8(b)

    def strings(mut self, xs: List[String]):
        self.int(len(xs))
        for x in xs:
            self.string(x)

    def seq(mut self, xs: List[UInt32]):
        self.int(len(xs))
        for x in xs:
            self.u64(UInt64(x))

    def value(mut self, v: ChoiceValue):
        self.u8(v.kind)
        self.i128(v.i)
        self.f64(v.f)
        self.seq(v.seq)

    def constraints(mut self, c: Constraints):
        self.u8(c.kind)
        self.bool(c.has_min)
        self.bool(c.has_max)
        self.i128(c.min_value)
        self.i128(c.max_value)
        self.i128(c.shrink_towards)
        self.f64(c.fmin)
        self.f64(c.fmax)
        self.bool(c.allow_nan)
        self.f64(c.smallest_nonzero_magnitude)
        self.f64(c.p)
        self.int(c.min_size)
        self.int(c.max_size)
        # weights and intervals: -1 for none, else an id, followed by the
        # contents the first time the id appears
        if c.weights:
            var w = c.weights.value()
            var addr = Int(w.ptr())
            var id = self.weight_ids.get(addr)
            if id:
                self.int(id.value())
            else:
                var new = len(self.keep_weights)
                self.weight_ids[addr] = new
                self.keep_weights.append(w)
                self.int(new)
                self.int(len(w[]))
                for x in w[]:
                    self.f64(x)
        else:
            self.int(-1)
        if c.intervals:
            var s = c.intervals.value()
            var addr = Int(s.ptr())
            var id = self.interval_ids.get(addr)
            if id:
                self.int(id.value())
            else:
                var new = len(self.keep_alive)
                self.interval_ids[addr] = new
                self.keep_alive.append(s)
                self.int(new)
                self.int(len(s[].lows))
                for k in range(len(s[].lows)):
                    self.u64(UInt64(s[].lows[k]))
                    self.u64(UInt64(s[].highs[k]))
        else:
            self.int(-1)

    def _overflow(mut self):
        if not self.overflowed:
            self.overflowed = True
            _WordPtr(unsafe_from_address=self.base + 8)[] = 1


# ===----------------------------------------------------------------------=== #
# Reading (in the parent)
# ===----------------------------------------------------------------------=== #


struct LogReader(Movable):
    var base: Int
    var pos: Int
    var end: Int
    var overflowed: Bool
    var intervals: Dict[Int, ArcPointer[IntervalSet]]
    var weights: Dict[Int, ArcPointer[List[Float64]]]

    def __init__(out self, base: Int):
        self.base = base
        self.pos = _HEADER
        # the child may have written anything, even over the header
        self.end = _HEADER + min(
            max(_WordPtr(unsafe_from_address=base)[], 0), LOG_SIZE - _HEADER
        )
        self.overflowed = _WordPtr(unsafe_from_address=base + 8)[] != 0
        self.intervals = {}
        self.weights = {}

    def more(self) -> Bool:
        return self.pos < self.end

    def u8(mut self) raises -> UInt8:
        if self.pos + 1 > self.end:
            raise Error("proptest: fork log truncated")
        var v = _BytePtr(unsafe_from_address=self.base + self.pos)[]
        self.pos += 1
        return v

    def u64(mut self) raises -> UInt64:
        if self.pos + 8 > self.end:
            raise Error("proptest: fork log truncated")
        var v = UInt64(0)
        for k in range(8):
            v |= UInt64(
                _BytePtr(unsafe_from_address=self.base + self.pos + k)[]
            ) << UInt64(8 * k)
        self.pos += 8
        return v

    def int(mut self) raises -> Int:
        return Int(self.u64())

    def i128(mut self) raises -> Int128:
        var lo = Int128(self.u64())
        var hi = Int128(Int64(self.u64()))
        return (hi << 64) | lo

    def f64(mut self) raises -> Float64:
        return Float64(from_bits=self.u64())

    def bool(mut self) raises -> Bool:
        return self.u8() != 0

    def length(mut self, item_size: Int) raises -> Int:
        """A count of items of `item_size` bytes that must fit in the rest
        of the log."""
        var n = self.int()
        if n < 0 or n * item_size > self.end - self.pos:
            raise Error("proptest: fork log has a bad length")
        return n

    def string(mut self) raises -> String:
        var n = self.length(1)
        var bytes = List[UInt8](capacity=n)
        for _ in range(n):
            bytes.append(self.u8())
        return String(from_utf8_lossy=bytes)

    def strings(mut self) raises -> List[String]:
        var out = List[String]()
        for _ in range(self.int()):
            out.append(self.string())
        return out^

    def seq(mut self) raises -> List[UInt32]:
        var n = self.length(8)
        var out = List[UInt32](capacity=n)
        for _ in range(n):
            out.append(UInt32(self.u64()))
        return out^

    def value(mut self) raises -> ChoiceValue:
        var v = ChoiceValue(integer=0)
        v.kind = self.u8()
        v.i = self.i128()
        v.f = self.f64()
        v.seq = self.seq()
        return v^

    def constraints(mut self) raises -> Constraints:
        var c = Constraints(self.u8())
        c.has_min = self.bool()
        c.has_max = self.bool()
        c.min_value = self.i128()
        c.max_value = self.i128()
        c.shrink_towards = self.i128()
        c.fmin = self.f64()
        c.fmax = self.f64()
        c.allow_nan = self.bool()
        c.smallest_nonzero_magnitude = self.f64()
        c.p = self.f64()
        c.min_size = self.int()
        c.max_size = self.int()
        var wid = self.int()
        if wid >= 0:
            if wid not in self.weights:
                var w = List[Float64]()
                for _ in range(self.int()):
                    w.append(self.f64())
                self.weights[wid] = ArcPointer(w^)
            c.weights = self.weights[wid]
        var iid = self.int()
        if iid >= 0:
            if iid not in self.intervals:
                var ivs = List[Tuple[UInt32, UInt32]]()
                for _ in range(self.int()):
                    var lo = UInt32(self.u64())
                    var hi = UInt32(self.u64())
                    ivs.append((lo, hi))
                self.intervals[iid] = ArcPointer(IntervalSet(ivs^))
            c.intervals = self.intervals[iid]
        return c^


# ===----------------------------------------------------------------------=== #
# Processes
# ===----------------------------------------------------------------------=== #


def fork_process() -> Int:
    """`fork()`: 0 in the child, the child's pid in the parent, -1 on
    failure."""
    return Int(external_call["fork", Int32]())


def wait_process(pid: Int) -> Int:
    """Wait for the child `pid` to finish; its wait status."""
    var status = Int32(0)
    while True:
        var r = external_call["waitpid", Int32](
            Int32(pid), Pointer(to=status), Int32(0)
        )
        if r == Int32(pid):
            return Int(status)
        if r < 0 and get_errno() != ErrNo.EINTR:
            return -1


def exit_child(code: Int):
    """End the child at once: no atexit handlers (the Mojo runtime's
    crash when run in a forked child) and no buffers flushed twice."""
    external_call["_exit", NoneType](Int32(code))


def prepare_child(timeout_ms: Optional[Float64], quiet: Bool):
    """Set up a new child: no core dumps (writing one can take a second
    per crash), the default action for fatal signals, an alarm after
    `timeout_ms`, and with `quiet`, stderr sent to /dev/null (sanitizers
    print long reports, which only the final replay should show)."""
    comptime if CompilationTarget.is_linux():
        # PR_SET_DUMPABLE: unlike RLIMIT_CORE, this also stops a piped
        # core_pattern (apport, systemd-coredump) from being run
        _ = external_call["prctl", Int32](
            Int32(4), Int(0), Int(0), Int(0), Int(0)
        )
    else:
        var limit = Array[UInt64, 2](fill=0)
        _ = external_call["setrlimit", Int32](
            Int32(4), Pointer(to=limit)
        )  # RLIMIT_CORE
    # the default action for fatal signals: the Mojo runtime's crash
    # handler doesn't work in a forked child (it ends in a SIGSEGV, hiding
    # the signal, and is slow)
    comptime SIGBUS = 10 if CompilationTarget.is_macos() else 7
    for sig in [4, 5, 6, 8, SIGBUS, 11]:
        _ = external_call["signal", Int](Int32(sig), Int(0))  # SIG_DFL
    if quiet:
        var path = String("/dev/null")
        var fd = external_call["open", Int32, num_fixed_args=2](
            path.as_c_string_span(), Int32(1), Int32(0)
        )
        if fd >= 0:
            _ = external_call["dup2", Int32](fd, Int32(2))
    if timeout_ms:
        var us = max(Int(timeout_ms.value() * 1000), 1)
        # struct itimerval {it_interval, it_value}, each {tv_sec, tv_usec}
        var timer = Array[Int, 4](fill=0)
        timer[2] = us // 1_000_000
        timer[3] = us % 1_000_000
        _ = external_call["setitimer", Int32](
            Int32(0), Pointer(to=timer), Int(0)
        )  # ITIMER_REAL: SIGALRM


comptime SIGALRM = 14


def exited(status: Int) -> Bool:
    return status & 0x7F == 0


def exit_code(status: Int) -> Int:
    return (status >> 8) & 0xFF


def term_signal(status: Int) -> Int:
    """The signal that killed the child, or 0."""
    var sig = status & 0x7F
    return sig if sig != 0 and sig != 0x7F else 0


def signal_name(sig: Int) -> String:
    if sig == 4:
        return "SIGILL"
    if sig == 5:
        return "SIGTRAP"
    if sig == 6:
        return "SIGABRT"
    if sig == 8:
        return "SIGFPE"
    if sig == 9:
        return "SIGKILL"
    if sig == 11:
        return "SIGSEGV"
    if sig == 13:
        return "SIGPIPE"
    if sig == 14:
        return "SIGALRM"
    if sig == 15:
        return "SIGTERM"
    comptime if CompilationTarget.is_macos():
        if sig == 10:
            return "SIGBUS"
    else:
        if sig == 7:
            return "SIGBUS"
    return String("signal ", sig)
