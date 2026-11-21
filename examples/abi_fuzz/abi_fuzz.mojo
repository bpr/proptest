# Differential testing of Mojo's C ABI against clang. Each test case draws
# a few C-compatible struct types and functions over them, and writes:
#
# - abi.h: the C types, and the hash and value-making functions for them
# - callee.c: C functions that Mojo calls, and drivers that call Mojo
# - program.mojo: the same types and functions in Mojo, and a main that
#   makes every call and prints what each side received
# - ref.c: C versions of the Mojo functions and a main that makes the same
#   calls in C
#
# Every function hashes all its arguments (FNV over each field's bits),
# records the hash with set_seen(), and returns a value made from the
# hash. So for each call, the program prints the hash the callee saw and
# a hash of the value the caller got back, and any argument or return
# value passed wrongly changes the line. build_and_compare.sh builds
# program.mojo at -O0 and -O3, linked with callee.c, and ref.c with clang,
# and compares the outputs. Any difference is a bug in Mojo's C ABI
# (or in clang). gcc disagrees with clang on structs with zero-length
# arrays, so it isn't the default reference (see build_and_compare.sh).
#
# Types: integers of 8 to 128 bits, Int, Float32, Float64, Bool, SIMD
# vectors (gcc vector types), nested structs, `Array` fields (C arrays),
# empty structs, and `@align`. A struct without `Array` fields may be
# `RegisterPassable`.
#
# Calls from Mojo to C go through `@extern`, `external_call`, a function
# pointer from C, and `external_call` with `num_fixed_args` to a variadic
# C function, each from an `@inline(.never)` wrapper that makes the call
# in tail position or not. Calls from C to Mojo go through a function
# pointer to an `abi("C")` Mojo function and an `@export` one.
#
# Build and run from the repository root:
#
#   pixi run mojo build -I . -o build/abi_fuzz examples/abi_fuzz/abi_fuzz.mojo
#   pixi run build/abi_fuzz build/abi_fuzz_work
#
# The compiler under test is $MOJO (default `mojo`); see
# build_and_compare.sh. ABI_FUZZ_NO_SHRINK=1 skips shrinking, and
# PROPTEST_SEED and PROPTEST_MAX_EXAMPLES set the seed and the number of
# programs. The failing case is kept in the work directory as failing_*.
# ABI_FUZZ_NO_EMPTY_WORKAROUND=1 passes empty structs through
# `external_call` and function pointers too, which Mojo gets wrong
# (#7710), and ABI_FUZZ_NO_SRET_WORKAROUND=1 lets Mojo functions that C
# calls take and return large structs, which Mojo miscompiles at -O1 and
# above (#7711).
#
# ABI_FUZZ_SECONDS=N runs proptest's fuzz loop (`FuzzTarget.fuzz`) for N
# seconds instead of `max_examples` random programs; ABI_FUZZ_BLIND=1
# makes it unguided, as a baseline. The loop's coverage features are
# each argument's and result's ABI shape on each call path: its size
# and x86-64 eightbyte classes, and how many argument registers the
# arguments before it took (see `Gen.record_features`).

from std.os import getenv
from std.subprocess import run
from std.sys import argv

from proptest import *


# Scalars: Mojo type, C type, kind (0 signed, 1 unsigned, 2 Float32,
# 3 Float64, 4 Bool, 5 Int128, 6 UInt128), and bits.
comptime MOJO_SCALARS: List[String] = [
    "Int8",
    "Int16",
    "Int32",
    "Int64",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "Int",
    "Float32",
    "Float64",
    "Bool",
    "Int128",
    "UInt128",
]
comptime C_SCALARS: List[String] = [
    "int8_t",
    "int16_t",
    "int32_t",
    "int64_t",
    "uint8_t",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "int64_t",
    "float",
    "double",
    "bool",
    "__int128",
    "unsigned __int128",
]
comptime DTYPES: List[String] = [
    "int8",
    "int16",
    "int32",
    "int64",
    "uint8",
    "uint16",
    "uint32",
    "uint64",
    "int",
    "float32",
    "float64",
    "bool",
    "int128",
    "uint128",
]
comptime KINDS: List[Int] = [0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 3, 4, 5, 6]
comptime BITS: List[Int] = [
    8,
    16,
    32,
    64,
    8,
    16,
    32,
    64,
    64,
    32,
    64,
    8,
    128,
    128,
]
# Scalars that a variadic call can pass unpromoted
comptime VARIADIC_OK: List[Bool] = [
    False,
    False,
    True,
    True,
    False,
    False,
    True,
    True,
    True,
    False,
    True,
    False,
    True,
    True,
]

# SIMD vectors: lane scalar and lane count (8 or 16 bytes)
comptime SIMD_SCALARS: List[Int] = [9, 9, 10, 2, 2, 3, 1, 4]
comptime SIMD_LANES: List[Int] = [4, 2, 2, 4, 2, 2, 8, 16]

comptime N_SCALARS = 14
comptime N_VECTORS = 8
comptime SEED = "14695981039346656037"

# Field and type kinds
comptime SCALAR = 0
comptime STRUCT = 1
comptime ARRAY = 2  # of a scalar
comptime VECTOR = 3
comptime STRUCT_ARRAY = 4
comptime VOID = 5

# Call paths
comptime PATH_NAMES: List[String] = [
    "extern",
    "external_call",
    "pointer",
    "variadic",
    "callback",
    "export",
]


@fieldwise_init
struct Ty(Copyable, ImplicitlyCopyable):
    var kind: Int
    var a: Int  # scalar, struct or vector index
    var n: Int  # array length


@fieldwise_init
struct StructDef(Copyable):
    var fields: List[Ty]
    var register_passable: Bool
    var align: Int  # 0 for none


@fieldwise_init
struct FnDef(Copyable):
    var params: List[Ty]
    var ret: Ty
    var to_c: Bool  # Mojo calls C (else C calls Mojo)
    var paths: List[Int]
    var tail: List[Bool]
    var args: List[Tuple[String, String]]  # (Mojo, C) argument values


def fnv(xs: List[UInt64]) -> UInt64:
    var h: UInt64 = 14695981039346656037
    for x in xs:
        h = (h ^ x) * 0x100000001B3
    return h


def H(var a: String, b: String) -> String:
    return String("H(", a, ", ", b, ")")


struct Gen(Movable):
    var structs: List[StructDef]
    var fns: List[FnDef]
    var empty_workaround: Bool
    var sret_workaround: Bool

    def __init__(out self):
        self.structs = List[StructDef]()
        self.fns = List[FnDef]()
        self.empty_workaround = getenv("ABI_FUZZ_NO_EMPTY_WORKAROUND") == ""
        self.sret_workaround = getenv("ABI_FUZZ_NO_SRET_WORKAROUND") == ""

    # ---- drawing types

    def scalar(self, mut data: ConjectureData) raises -> Int:
        return data.draw(integers(0, N_SCALARS - 1))

    def field_type(self, mut data: ConjectureData, n_structs: Int) raises -> Ty:
        var c = data.draw(integers(0, 9))
        if c <= 4 or (c <= 6 and n_structs == 0):
            return Ty(SCALAR, self.scalar(data), 0)
        if c <= 6:
            return Ty(STRUCT, data.draw(integers(0, n_structs - 1)), 0)
        if c == 7:
            return Ty(ARRAY, self.scalar(data), self.length(data))
        if c == 8:
            return Ty(VECTOR, data.draw(integers(0, N_VECTORS - 1)), 0)
        if n_structs == 0:
            return Ty(ARRAY, self.scalar(data), self.length(data))
        return Ty(
            STRUCT_ARRAY,
            data.draw(integers(0, n_structs - 1)),
            self.length(data),
        )

    def length(self, mut data: ConjectureData) raises -> Int:
        # a zero-length array is a GNU C extension, as is an empty struct
        return 0 if data.draw(integers(0, 15)) == 0 else data.draw(
            integers(1, 5)
        )

    def value_type(self, mut data: ConjectureData) raises -> Ty:
        """A parameter or return type."""
        var c = data.draw(integers(0, 9))
        if c <= 3 or len(self.structs) == 0:
            return Ty(SCALAR, self.scalar(data), 0)
        if c <= 8:
            return Ty(STRUCT, data.draw(integers(0, len(self.structs) - 1)), 0)
        return Ty(VECTOR, data.draw(integers(0, N_VECTORS - 1)), 0)

    def draw_structs(mut self, mut data: ConjectureData) raises:
        for k in range(data.draw(integers(1, 5))):
            var fields = List[Ty]()
            var n_fields = data.draw(integers(1, 6))
            if data.draw(integers(0, 19)) == 0:
                n_fields = 0
            var passable = True
            for _ in range(n_fields):
                var t = self.field_type(data, k)
                if t.kind == ARRAY or t.kind == STRUCT_ARRAY:
                    passable = False
                if t.kind == STRUCT and not self.structs[t.a].register_passable:
                    passable = False
                fields.append(t)
            if passable and data.draw(integers(0, 3)) == 0:
                passable = False
            var align = 0
            if data.draw(integers(0, 7)) == 0:
                align = 16 if data.draw(booleans()) else 32
            self.structs.append(StructDef(fields^, passable, align))

    def passable(self, t: Ty) -> Bool:
        """Whether `external_call` can return a `t`."""
        if t.kind == STRUCT:
            return self.structs[t.a].register_passable
        return True

    def empty(self, t: Ty) -> Bool:
        """Whether a `t` has size zero."""
        if t.kind == ARRAY or t.kind == STRUCT_ARRAY:
            return t.n == 0 or (
                t.kind == STRUCT_ARRAY and self.empty(Ty(STRUCT, t.a, 0))
            )
        if t.kind != STRUCT:
            return False
        for f in self.structs[t.a].fields:
            if not self.empty(f):
                return False
        return True

    def indirect(self, t: Ty) -> Bool:
        """Whether Mojo may pass a `t` through a pointer."""
        return t.kind == STRUCT and not self.structs[t.a].register_passable

    def variadic_ok(self, t: Ty) -> Bool:
        if t.kind == SCALAR:
            return materialize[VARIADIC_OK]()[t.a]
        return t.kind != VOID

    # ---- ABI shapes, for the fuzz loop's coverage features

    def size_align(self, t: Ty) -> Tuple[Int, Int]:
        """A `t`'s size and alignment on x86-64, as C lays it out."""
        if t.kind == SCALAR:
            var n = materialize[BITS]()[t.a] // 8
            return (n, n)
        if t.kind == VECTOR:
            var n = (
                materialize[SIMD_LANES]()[t.a]
                * materialize[BITS]()[materialize[SIMD_SCALARS]()[t.a]]
                // 8
            )
            return (n, n)
        if t.kind == ARRAY or t.kind == STRUCT_ARRAY:
            var e = self.size_align(
                Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
            )
            return (e[0] * t.n, e[1])
        if t.kind == VOID:
            return (0, 1)
        var size = 0
        var align = 1
        for f in self.structs[t.a].fields:
            var fa = self.size_align(f)
            size = (size + fa[1] - 1) // fa[1] * fa[1] + fa[0]
            align = max(align, fa[1])
        align = max(align, self.structs[t.a].align)
        return ((size + align - 1) // align * align, align)

    def classify(self, t: Ty, offset: Int, mut classes: List[Int]):
        """Merge the classes of `t`'s scalars at `offset` into the
        eightbyte classes `classes` (0 none, 1 INTEGER, 2 SSE, 3 both:
        INTEGER wins)."""
        if offset >= 16:
            return
        if t.kind == SCALAR or t.kind == VECTOR:
            var sse = t.kind == VECTOR or materialize[KINDS]()[t.a] in (2, 3)
            var n = self.size_align(t)[0]
            var e = offset // 8
            while e < 2 and e * 8 < offset + n:
                classes[e] |= 2 if sse else 1
                e += 1
            return
        if t.kind == ARRAY or t.kind == STRUCT_ARRAY:
            var et = Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
            var n = self.size_align(et)[0]
            for i in range(t.n):
                self.classify(et, offset + i * n, classes)
            return
        if t.kind == STRUCT:
            var off = offset
            for f in self.structs[t.a].fields:
                var fa = self.size_align(f)
                off = (off + fa[1] - 1) // fa[1] * fa[1]
                self.classify(f, off, classes)
                off += fa[0]

    def shape(self, t: Ty) -> Tuple[UInt64, Int, Int]:
        """A summary of how x86-64 passes a `t`, and the INTEGER and SSE
        registers it takes (0, 0 in memory)."""
        if t.kind == VOID:
            return (UInt64(0x100), 0, 0)
        if t.kind == SCALAR:
            var k = materialize[KINDS]()[t.a]
            var regs = 2 if k >= 5 else 1
            return (
                UInt64(0x200 + t.a),
                0 if k in (2, 3) else regs,
                1 if k in (2, 3) else 0,
            )
        if t.kind == VECTOR:
            return (UInt64(0x300 + t.a), 0, 1)
        var sa = self.size_align(t)
        var size = sa[0]
        var bucket = size if size <= 16 else (
            17 if size
            <= 32 else (18 if size <= 64 else (19 if size <= 256 else 20))
        )
        var classes: List[Int] = [0, 0]
        if size <= 16:
            self.classify(t, 0, classes)
        var ints = 0
        var sses = 0
        for c in classes:
            if c & 1:
                ints += 1
            elif c == 2:
                sses += 1
        ref s = self.structs[t.a]
        var code = UInt64(
            0x10000
            + bucket * 256
            + classes[0] * 32
            + classes[1] * 8
            + (4 if s.align > 0 else 0)
            + (2 if s.register_passable else 0)
            + (1 if self.indirect(t) else 0)
        )
        return (code, ints, sses)

    def record_features(self, mut data: ConjectureData, f: FnDef):
        """Record, for each call path, the shape of the result and of
        each argument with the registers the arguments before it took."""
        var ret = self.shape(f.ret)
        for j in range(len(f.paths)):
            var tag = UInt64(f.paths[j] * 2 + (1 if f.tail[j] else 0))
            data.feature(fnv([tag, 0xFE, ret[0]]))
            var ints = 0
            var sses = 0
            # a result in memory takes a register for its address
            if f.ret.kind == STRUCT and self.size_align(f.ret)[0] > 16:
                ints = 1
            for i in range(len(f.params)):
                var sh = self.shape(f.params[i])
                data.feature(
                    fnv(
                        [
                            tag,
                            sh[0],
                            UInt64(min(ints, 7)),
                            UInt64(min(sses, 9)),
                        ]
                    )
                )
                if ints + sh[1] <= 6 and sses + sh[2] <= 8:
                    ints += sh[1]
                    sses += sh[2]
            data.feature(fnv([tag, 0xFF, UInt64(len(f.params))]))

    def draw_fns(mut self, mut data: ConjectureData) raises:
        for _ in range(data.draw(integers(1, 6))):
            var params = List[Ty]()
            for _ in range(data.draw(integers(0, 6))):
                params.append(self.value_type(data))
            var ret = Ty(VOID, 0, 0) if data.draw(
                integers(0, 5)
            ) == 0 else self.value_type(data)
            var to_c = data.draw(integers(0, 2)) > 0
            # An abi("C") Mojo function passes a large struct argument or
            # result through a local temporary to a call marked `tail`,
            # which -O1 and above miscompile (#7711), so only C gets
            # those.
            if self.sret_workaround:
                var indirect = self.indirect(ret)
                for p in params:
                    indirect = indirect or self.indirect(p)
                if indirect:
                    to_c = True
            var paths = List[Int]()
            var tail = List[Bool]()
            if to_c:
                var can_variadic = len(params) > 0 and self.passable(ret)
                # external_call and function pointers pass an empty
                # struct argument as an i32 (#7710); @extern gets it
                # right
                var has_empty = False
                for p in params:
                    can_variadic = can_variadic and self.variadic_ok(p)
                    has_empty = has_empty or self.empty(p)
                for path in range(4):
                    if path > 0 and has_empty and self.empty_workaround:
                        continue
                    if path == 1 and not self.passable(ret):
                        continue
                    if path == 3 and not can_variadic:
                        continue
                    if data.draw(booleans()):
                        paths.append(path)
                        tail.append(data.draw(booleans()))
                if len(paths) == 0:
                    paths.append(0)
                    tail.append(True)
            else:
                for path in range(4, 6):
                    if data.draw(booleans()):
                        paths.append(path)
                        tail.append(False)
                if len(paths) == 0:
                    paths.append(4)
                    tail.append(False)
            var args = List[Tuple[String, String]]()
            for p in params:
                args.append(self.value(data, p))
            var fn_def = FnDef(params^, ret, to_c, paths^, tail^, args^)
            self.record_features(data, fn_def)
            self.fns.append(fn_def^)

    # ---- values (Mojo, C)

    def scalar_value(
        self, mut data: ConjectureData, s: Int
    ) raises -> Tuple[String, String]:
        var kind = materialize[KINDS]()[s]
        var bits = materialize[BITS]()[s]
        var m = materialize[MOJO_SCALARS]()[s]
        var c = materialize[C_SCALARS]()[s]
        if kind == 4:
            if data.draw(booleans()):
                return (String("True"), String("true"))
            return (String("False"), String("false"))
        if kind == 2 or kind == 3:
            var k = data.draw(integers(-4000, 4000))
            return (
                String(m, "(", k, ".0 / 8.0)"),
                String("((", c, ")(", k, ".0 / 8.0))"),
            )
        if kind == 5 or kind == 6:
            var hi = data.draw(integers(-3, 3))
            # the low half is an unsigned 64-bit value in both languages
            var lo = self.int_literal(data, 64, False)
            return (
                String("((", m, "(", hi, ") << 64) | ", m, "(", lo, "))"),
                String(
                    "((((", c, ")", hi, "LL) << 64) | (", c, ")", lo, "ULL)"
                ),
            )
        var lit = self.int_literal(data, bits, kind == 0)
        var suffix = "LL" if kind == 0 else "ULL"
        return (
            String(m, "(", lit, ")"),
            String("((", c, ")", lit, suffix, ")"),
        )

    def int_literal(
        self, mut data: ConjectureData, bits: Int, signed: Bool
    ) raises -> String:
        """A decimal literal for a `bits`-bit integer, unsigned for 128."""
        var c = data.draw(integers(0, 3))
        if bits == 64 and not signed or (bits == 64 and c == 3):
            # full 64-bit range, as an unsigned value
            var x = data.draw(integers(Int.MIN, Int.MAX))
            if signed and x != Int.MIN:
                return String(x)
            return String(Scalar[DType.int64](x).cast[DType.uint64]())
        if c == 0:
            return String(data.draw(integers(0 if not signed else -9, 9)))
        if signed:
            var half = 1 << (bits - 1)
            return String(data.draw(integers(-half + 1, half - 1)))
        return String(data.draw(integers(0, (1 << bits) - 1)))

    def value(
        self, mut data: ConjectureData, t: Ty
    ) raises -> Tuple[String, String]:
        if t.kind == SCALAR:
            return self.scalar_value(data, t.a)
        if t.kind == VECTOR:
            var s = materialize[SIMD_SCALARS]()[t.a]
            var m = String(self.mojo_type(t), "(")
            var c = String("((", self.c_type(t), "){")
            for i in range(materialize[SIMD_LANES]()[t.a]):
                var v = self.scalar_value(data, s)
                if i > 0:
                    m += ", "
                    c += ", "
                m += v[0]
                c += v[1]
            return (m + ")", c + "})")
        if t.kind == ARRAY or t.kind == STRUCT_ARRAY:
            var elem = Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
            # a bare list literal, typed by the field it initializes
            var m = String("[")
            var c = String("{")
            for i in range(t.n):
                var v = self.value(data, elem)
                if i > 0:
                    m += ", "
                    c += ", "
                m += v[0]
                c += v[1]
            return (m + "]", c + "}")
        # a struct
        var m = String("S", t.a, "(")
        var c = String("((S", t.a, "){")
        ref fields = self.structs[t.a].fields
        for i in range(len(fields)):
            var v = self.value(data, fields[i])
            if i > 0:
                m += ", "
                c += ", "
            m += v[0]
            c += v[1]
        return (m + ")", c + "})")

    # ---- type names

    def mojo_type(self, t: Ty) -> String:
        if t.kind == SCALAR:
            return materialize[MOJO_SCALARS]()[t.a]
        if t.kind == STRUCT:
            return String("S", t.a)
        if t.kind == VECTOR:
            var s = materialize[SIMD_SCALARS]()[t.a]
            return String(
                "SIMD[DType.",
                materialize[DTYPES]()[s],
                ", ",
                materialize[SIMD_LANES]()[t.a],
                "]",
            )
        if t.kind == ARRAY:
            return String(
                "Array[", materialize[MOJO_SCALARS]()[t.a], ", ", t.n, "]"
            )
        if t.kind == STRUCT_ARRAY:
            return String("Array[S", t.a, ", ", t.n, "]")
        return "NoneType"

    def c_type(self, t: Ty) -> String:
        if t.kind == SCALAR:
            return materialize[C_SCALARS]()[t.a]
        if t.kind == STRUCT:
            return String("S", t.a)
        if t.kind == VECTOR:
            return String("V", t.a)
        return "void"

    def c_field(self, t: Ty, name: String) -> String:
        if t.kind == ARRAY:
            return String(
                materialize[C_SCALARS]()[t.a], " ", name, "[", t.n, "]"
            )
        if t.kind == STRUCT_ARRAY:
            return String("S", t.a, " ", name, "[", t.n, "]")
        return String(self.c_type(t), " ", name)

    # ---- hashing: statements that fold `x` into `h`

    def mojo_hash(self, t: Ty, x: String, indent: String) -> String:
        if t.kind == SCALAR:
            var kind = materialize[KINDS]()[t.a]
            if kind == 0:
                return String(indent, "h = H(h, UInt64(Int64(", x, ")))\n")
            if kind == 1:
                return String(indent, "h = H(h, UInt64(", x, "))\n")
            if kind == 2 or kind == 3:
                return String(indent, "h = H(h, UInt64(", x, ".to_bits()))\n")
            if kind == 4:
                return String(indent, "h = H(h, UInt64(Int(", x, ")))\n")
            return String(
                indent,
                "h = H(h, ",
                x,
                ".cast[DType.uint64]())\n",
                indent,
                "h = H(h, (",
                x,
                " >> 64).cast[DType.uint64]())\n",
            )
        if t.kind == STRUCT:
            return String(indent, "h = hS", t.a, "(h, ", x, ")\n")
        if t.kind == VECTOR:
            var s = Ty(SCALAR, materialize[SIMD_SCALARS]()[t.a], 0)
            var out = String()
            for i in range(materialize[SIMD_LANES]()[t.a]):
                out += self.mojo_hash(s, String(x, "[", i, "]"), indent)
            return out
        var elem = Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
        var out = String()
        for i in range(t.n):
            out += self.mojo_hash(elem, String(x, "[", i, "]"), indent)
        return out

    def c_hash(self, t: Ty, x: String, indent: String) -> String:
        if t.kind == SCALAR:
            var kind = materialize[KINDS]()[t.a]
            if kind == 0:
                return String(
                    indent, "h = H(h, (uint64_t)(int64_t)(", x, "));\n"
                )
            if kind == 1 or kind == 4:
                return String(indent, "h = H(h, (uint64_t)(", x, "));\n")
            if kind == 2:
                return String(indent, "h = H(h, f32b(", x, "));\n")
            if kind == 3:
                return String(indent, "h = H(h, f64b(", x, "));\n")
            return String(
                indent,
                "h = H(h, (uint64_t)(",
                x,
                "));\n",
                indent,
                "h = H(h, (uint64_t)((",
                x,
                ") >> 64));\n",
            )
        if t.kind == STRUCT:
            return String(indent, "h = hS", t.a, "(h, ", x, ");\n")
        if t.kind == VECTOR:
            var s = Ty(SCALAR, materialize[SIMD_SCALARS]()[t.a], 0)
            var out = String()
            for i in range(materialize[SIMD_LANES]()[t.a]):
                out += self.c_hash(s, String("(", x, ")[", i, "]"), indent)
            return out
        var elem = Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
        var out = String()
        for i in range(t.n):
            out += self.c_hash(elem, String(x, "[", i, "]"), indent)
        return out

    # ---- making a value from a hash `u`

    def mojo_make(self, t: Ty, u: String) -> String:
        if t.kind == SCALAR:
            var kind = materialize[KINDS]()[t.a]
            var dt = materialize[DTYPES]()[t.a]
            if kind == 0 and t.a == 8:
                return String("Int(", u, ".cast[DType.int64]())")
            if kind == 0 or kind == 1:
                return String(u, ".cast[DType.", dt, "]()")
            if kind == 2 or kind == 3:
                return String(
                    "((((",
                    u,
                    (
                        ") >> 20) & 0xFFFF).cast[DType.int64]() -"
                        " 32768).cast[DType."
                    ),
                    dt,
                    "]() * 0.25",
                )
            if kind == 4:
                return String("((", u, ") & 1) == 1")
            if kind == 5:
                return String(
                    u, ".cast[DType.int64]().cast[DType.int128]() * 3"
                )
            return String(u, ".cast[DType.uint128]() * 0x1000000001")
        if t.kind == STRUCT:
            return String("mkS", t.a, "(", u, ")")
        if t.kind == VECTOR:
            var s = Ty(SCALAR, materialize[SIMD_SCALARS]()[t.a], 0)
            var out = String(self.mojo_type(t), "(")
            for i in range(materialize[SIMD_LANES]()[t.a]):
                if i > 0:
                    out += ", "
                out += self.mojo_make(s, H(String(u), String(i)))
            return out + ")"
        var elem = Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
        var out = String("[")
        for i in range(t.n):
            if i > 0:
                out += ", "
            out += self.mojo_make(elem, H(String(u), String(i)))
        return out + "]"

    def c_make(self, t: Ty, u: String) -> String:
        """An initializer: an expression, or braces for an array."""
        if t.kind == SCALAR:
            var kind = materialize[KINDS]()[t.a]
            var c = materialize[C_SCALARS]()[t.a]
            if kind == 0 or kind == 1:
                return String("((", c, ")(", u, "))")
            if kind == 2 or kind == 3:
                return String(
                    "((",
                    c,
                    ")((int64_t)(((",
                    u,
                    ") >> 20) & 0xFFFF) - 32768) * (",
                    c,
                    ")0.25)",
                )
            if kind == 4:
                return String("(((", u, ") & 1) != 0)")
            if kind == 5:
                return String("((__int128)(int64_t)(", u, ") * 3)")
            return String("((unsigned __int128)(", u, ") * 0x1000000001ULL)")
        if t.kind == STRUCT:
            return String("mkS", t.a, "(", u, ")")
        if t.kind == VECTOR:
            var s = Ty(SCALAR, materialize[SIMD_SCALARS]()[t.a], 0)
            var out = String("((V", t.a, "){")
            for i in range(materialize[SIMD_LANES]()[t.a]):
                if i > 0:
                    out += ", "
                out += self.c_make(s, H(String(u), String(i)))
            return out + "})"
        var elem = Ty(SCALAR if t.kind == ARRAY else STRUCT, t.a, 0)
        var out = String("{")
        for i in range(t.n):
            if i > 0:
                out += ", "
            out += self.c_make(elem, H(String(u), String(i)))
        return out + "}"

    # ---- signatures

    def mojo_params(self, f: FnDef) -> String:
        var out = String()
        for i in range(len(f.params)):
            if i > 0:
                out += ", "
            out += String("p", i, ": ", self.mojo_type(f.params[i]))
        return out

    def mojo_ret(self, f: FnDef) -> String:
        if f.ret.kind == VOID:
            return ""
        return String(" -> ", self.mojo_type(f.ret))

    def c_params(self, f: FnDef) -> String:
        if len(f.params) == 0:
            return "void"
        var out = String()
        for i in range(len(f.params)):
            if i > 0:
                out += ", "
            out += String(self.c_type(f.params[i]), " p", i)
        return out

    def c_param_types(self, f: FnDef) -> String:
        if len(f.params) == 0:
            return "void"
        var out = String()
        for i in range(len(f.params)):
            if i > 0:
                out += ", "
            out += self.c_type(f.params[i])
        return out

    def names(self, n: Int) -> String:
        var out = String()
        for i in range(n):
            if i > 0:
                out += ", "
            out += String("p", i)
        return out

    def mojo_args(self, f: FnDef) -> String:
        var out = String()
        for i in range(len(f.args)):
            if i > 0:
                out += ", "
            out += f.args[i][0]
        return out

    def c_args(self, f: FnDef) -> String:
        var out = String()
        for i in range(len(f.args)):
            if i > 0:
                out += ", "
            out += f.args[i][1]
        return out

    # ---- files

    def header(self) -> String:
        var s = String(
            "#include <stdint.h>\n#include <stdbool.h>\n#include"
            " <stdarg.h>\n#include <stdio.h>\n#include <string.h>\n\n"
        )
        for i in range(N_VECTORS):
            var sc = materialize[SIMD_SCALARS]()[i]
            var lanes = materialize[SIMD_LANES]()[i]
            s += String(
                "typedef ",
                materialize[C_SCALARS]()[sc],
                " V",
                i,
                " __attribute__((vector_size(",
                lanes * materialize[BITS]()[sc] // 8,
                ")));\n",
            )
        s += "\n"
        for k in range(len(self.structs)):
            ref sd = self.structs[k]
            s += "typedef struct "
            if sd.align > 0:
                s += String("__attribute__((aligned(", sd.align, "))) ")
            s += "{\n"
            for j in range(len(sd.fields)):
                s += String(
                    "    ", self.c_field(sd.fields[j], String("f", j)), ";\n"
                )
            s += String("} S", k, ";\n")
        s += """
static inline uint64_t H(uint64_t h, uint64_t x) {
    return (h ^ x) * 0x100000001b3ULL;
}
static inline uint64_t f32b(float f) {
    uint32_t u;
    memcpy(&u, &f, 4);
    return u;
}
static inline uint64_t f64b(double f) {
    uint64_t u;
    memcpy(&u, &f, 8);
    return u;
}
int64_t get_seen(void);
void set_seen(int64_t);

"""
        for k in range(len(self.structs)):
            ref sd = self.structs[k]
            s += String(
                "static inline uint64_t hS", k, "(uint64_t h, S", k, " s) {\n"
            )
            for j in range(len(sd.fields)):
                s += self.c_hash(sd.fields[j], String("s.f", j), "    ")
            s += "    return h;\n}\n"
            s += String("static inline S", k, " mkS", k, "(uint64_t u) {\n")
            s += String("    S", k, " s = {")
            for j in range(len(sd.fields)):
                if j > 0:
                    s += ", "
                s += self.c_make(sd.fields[j], H(String("u"), String(j + 1)))
            s += "};\n    return s;\n}\n"
        for i in range(len(self.fns)):
            ref f = self.fns[i]
            # the hash of a returned value
            s += String("static inline uint64_t hR", i, "(")
            if f.ret.kind == VOID:
                s += "void) {\n    return 0;\n}\n"
            else:
                s += String(self.c_type(f.ret), " r) {\n    uint64_t h = 7;\n")
                s += self.c_hash(f.ret, "r", "    ")
                s += "    return h;\n}\n"
            # the body of every implementation of function i
            s += String(
                "static inline ",
                self.c_type(f.ret),
                " body",
                i,
                "(",
                self.c_params(f),
                ") {\n    uint64_t h = ",
                SEED,
                "ULL;\n",
            )
            for j in range(len(f.params)):
                s += self.c_hash(f.params[j], String("p", j), "    ")
            s += "    set_seen((int64_t)h);\n"
            if f.ret.kind != VOID:
                s += String("    return ", self.c_make(f.ret, "h"), ";\n")
            s += "}\n"
            s += String(
                "typedef ",
                self.c_type(f.ret),
                " (*F",
                i,
                ")(",
                self.c_param_types(f),
                ");\n",
            )
            if f.to_c:
                s += String(
                    self.c_type(f.ret), " c", i, "(", self.c_params(f), ");\n"
                )
            else:
                s += String(
                    self.c_type(f.ret), " mx", i, "(", self.c_params(f), ");\n"
                )
                s += String(
                    self.c_type(f.ret), " mf", i, "(", self.c_params(f), ");\n"
                )
                s += String("int64_t drive", i, "(F", i, " f);\n")
                s += String("int64_t drive_x", i, "(void);\n")
        return s

    def callee(self) -> String:
        var s = String(
            '#include "abi.h"\n\nstatic int64_t seen;\nint64_t'
            " get_seen(void) {\n    return seen;\n}\nvoid set_seen(int64_t h)"
            " {\n    seen = h;\n}\n\n"
        )
        for i in range(len(self.fns)):
            ref f = self.fns[i]
            var ret = self.c_type(f.ret)
            var ret_kw = "" if f.ret.kind == VOID else "return "
            var names = self.names(len(f.params))
            if f.to_c:
                s += String(
                    ret,
                    " c",
                    i,
                    "(",
                    self.c_params(f),
                    ") {\n    ",
                    ret_kw,
                    "body",
                    i,
                    "(",
                    names,
                    ");\n}\n",
                )
                s += String(
                    ret,
                    " c",
                    i,
                    "_e(",
                    self.c_params(f),
                    ") {\n    ",
                    ret_kw,
                    "body",
                    i,
                    "(",
                    names,
                    ");\n}\n",
                )
                s += String(
                    "F", i, " get_c", i, "(void) {\n    return c", i, ";\n}\n"
                )
                if 3 in f.paths:
                    s += String(ret, " c", i, "_v(int64_t n, ...) {\n")
                    s += "    va_list ap;\n    va_start(ap, n);\n"
                    for j in range(len(f.params)):
                        var t = self.c_type(f.params[j])
                        s += String(
                            "    ", t, " p", j, " = va_arg(ap, ", t, ");\n"
                        )
                    s += "    va_end(ap);\n"
                    if f.ret.kind == VOID:
                        s += String("    body", i, "(", names, ");\n}\n")
                    else:
                        s += String("    return body", i, "(", names, ");\n}\n")
            else:
                for x in range(2):
                    if x == 0:
                        s += String("int64_t drive", i, "(F", i, " f) {\n")
                    else:
                        s += String("int64_t drive_x", i, "(void) {\n")
                    var callee = "f" if x == 0 else String("mx", i)
                    if f.ret.kind == VOID:
                        s += String(
                            "    ",
                            callee,
                            "(",
                            self.c_args(f),
                            ");\n    return 0;\n}\n",
                        )
                    else:
                        s += String(
                            "    return (int64_t)hR",
                            i,
                            "(",
                            callee,
                            "(",
                            self.c_args(f),
                            "));\n}\n",
                        )
        return s

    def reference(self) -> String:
        var s = String('#include "abi.h"\n\n')
        for i in range(len(self.fns)):
            ref f = self.fns[i]
            if f.to_c:
                continue
            var ret_kw = "" if f.ret.kind == VOID else "return "
            for name in ["mf", "mx"]:
                s += String(
                    self.c_type(f.ret),
                    " ",
                    name,
                    i,
                    "(",
                    self.c_params(f),
                    ") {\n    ",
                    ret_kw,
                    "body",
                    i,
                    "(",
                    self.names(len(f.params)),
                    ");\n}\n",
                )
        s += "\nint main(void) {\n"
        for i in range(len(self.fns)):
            ref f = self.fns[i]
            for p in f.paths:
                var label = String("f", i, " ", materialize[PATH_NAMES]()[p])
                if f.to_c:
                    s += "    {\n        "
                    if f.ret.kind == VOID:
                        s += String("c", i, "(", self.c_args(f), ");\n")
                        s += String(
                            '        printf("',
                            label,
                            ' %lld 0\\n", (long long)get_seen());\n',
                        )
                    else:
                        s += String(
                            self.c_type(f.ret),
                            " r = c",
                            i,
                            "(",
                            self.c_args(f),
                            ");\n",
                        )
                        s += String(
                            '        printf("',
                            label,
                            (
                                ' %lld %llu\\n", (long long)get_seen(),'
                                " (unsigned long long)hR"
                            ),
                            i,
                            "(r));\n",
                        )
                    s += "    }\n"
                else:
                    var call = String(
                        "drive", i, "(mf", i, ")"
                    ) if p == 4 else String("drive_x", i, "()")
                    s += String(
                        "    {\n        int64_t d = ",
                        call,
                        ";\n",
                        '        printf("',
                        label,
                        (
                            ' %lld %lld\\n", (long long)get_seen(), (long'
                            " long)d);\n"
                        ),
                        "    }\n",
                    )
        s += "    return 0;\n}\n"
        return s

    def program(self) -> String:
        var s = String(
            "from std.collections import Array\nfrom std.ffi import"
            " external_call\n\n\n"
        )
        s += "def H(h: UInt64, x: UInt64) -> UInt64:\n"
        s += "    return (h ^ x) * 0x100000001B3\n\n\n"
        s += "def get_seen() -> Int64:\n"
        s += '    return external_call["get_seen", Int64]()\n\n\n'
        for k in range(len(self.structs)):
            ref sd = self.structs[k]
            if sd.align > 0:
                s += String("@align(", sd.align, ")\n")
            s += "@fieldwise_init\n"
            if sd.register_passable:
                s += String("struct S", k, "(Copyable, RegisterPassable):\n")
            else:
                s += String("struct S", k, "(Copyable):\n")
            for j in range(len(sd.fields)):
                s += String(
                    "    var f", j, ": ", self.mojo_type(sd.fields[j]), "\n"
                )
            if len(sd.fields) == 0:
                s += "    pass\n"
            s += "\n\n"
            s += String("def hS", k, "(h0: UInt64, s: S", k, ") -> UInt64:\n")
            s += "    var h = h0\n"
            for j in range(len(sd.fields)):
                s += self.mojo_hash(sd.fields[j], String("s.f", j), "    ")
            s += "    return h\n\n\n"
            s += String("def mkS", k, "(u: UInt64) -> S", k, ":\n")
            s += String("    return S", k, "(")
            for j in range(len(sd.fields)):
                if j > 0:
                    s += ", "
                s += self.mojo_make(sd.fields[j], H(String("u"), String(j + 1)))
            s += ")\n\n\n"
        for i in range(len(self.fns)):
            ref f = self.fns[i]
            var params = self.mojo_params(f)
            var ret = self.mojo_ret(f)
            var names = self.names(len(f.params))
            # the hash of a returned value
            if f.ret.kind != VOID:
                s += String(
                    "def hR", i, "(r: ", self.mojo_type(f.ret), ") -> UInt64:\n"
                )
                s += "    var h: UInt64 = 7\n"
                s += self.mojo_hash(f.ret, "r", "    ")
                s += "    return h\n\n\n"
            s += String(
                "comptime F",
                i,
                " = def(",
                self.mojo_param_types(f),
                ') thin abi("C")',
                ret,
                "\n\n\n",
            )
            if f.to_c:
                s += String(
                    '@extern("c',
                    i,
                    '")\ndef c',
                    i,
                    "(",
                    params,
                    ') abi("C")',
                    ret,
                    ":\n    ...\n\n\n",
                )
                for j in range(len(f.paths)):
                    var p = f.paths[j]
                    var rt = (
                        "NoneType" if f.ret.kind
                        == VOID else self.mojo_type(f.ret)
                    )
                    var call: String
                    if p == 0:
                        call = String("c", i, "(", names, ")")
                    elif p == 1:
                        call = String(
                            'external_call["c', i, '_e", ', rt, "](", names, ")"
                        )
                    elif p == 2:
                        call = String(
                            'external_call["get_c',
                            i,
                            '", F',
                            i,
                            "]()(",
                            names,
                            ")",
                        )
                    else:
                        call = String(
                            'external_call["c',
                            i,
                            '_v", ',
                            rt,
                            ", num_fixed_args=1](Int64(",
                            len(f.params),
                            "), ",
                            names,
                            ")",
                        )
                    s += String(
                        "@inline(.never)\ndef w",
                        i,
                        "_",
                        p,
                        "(",
                        params,
                        ")",
                        ret,
                        ":\n",
                    )
                    if f.ret.kind == VOID:
                        s += String("    ", call, "\n")
                        if not f.tail[j]:
                            s += "    _ = get_seen()\n"
                    elif f.tail[j]:
                        s += String("    return ", call, "\n")
                    else:
                        s += String("    var r = ", call, "\n    return r^\n")
                    s += "\n\n"
            else:
                for name in ["mf", "mx"]:
                    if name == "mx":
                        s += "@export\n"
                    s += String(
                        "def ", name, i, "(", params, ') abi("C")', ret, ":\n"
                    )
                    s += String("    var h: UInt64 = ", SEED, "\n")
                    for j in range(len(f.params)):
                        s += self.mojo_hash(f.params[j], String("p", j), "    ")
                    s += (
                        '    external_call["set_seen",'
                        " NoneType](h.cast[DType.int64]())\n"
                    )
                    if f.ret.kind != VOID:
                        s += String(
                            "    return ", self.mojo_make(f.ret, "h"), "\n"
                        )
                    s += "\n\n"
        s += "def main():\n"
        for i in range(len(self.fns)):
            ref f = self.fns[i]
            for p in f.paths:
                var label = String("f", i, " ", materialize[PATH_NAMES]()[p])
                if f.to_c:
                    var call = String(
                        "w", i, "_", p, "(", self.mojo_args(f), ")"
                    )
                    if f.ret.kind == VOID:
                        s += String("    ", call, "\n")
                        s += String('    print("', label, '", get_seen(), 0)\n')
                    else:
                        s += String("    var r", i, "_", p, " = ", call, "\n")
                        s += String(
                            '    print("',
                            label,
                            '", get_seen(), hR',
                            i,
                            "(r",
                            i,
                            "_",
                            p,
                            "))\n",
                        )
                else:
                    var call = String(
                        'external_call["drive', i, '", Int64](mf', i, ")"
                    ) if p == 4 else String(
                        'external_call["drive_x', i, '", Int64]()'
                    )
                    s += String("    var d", i, "_", p, " = ", call, "\n")
                    s += String(
                        '    print("',
                        label,
                        '", get_seen(), d',
                        i,
                        "_",
                        p,
                        ")\n",
                    )
        if len(self.fns) == 0:
            s += "    pass\n"
        return s

    def mojo_param_types(self, f: FnDef) -> String:
        var out = String()
        for i in range(len(f.params)):
            if i > 0:
                out += ", "
            out += self.mojo_type(f.params[i])
        return out


def write_file(path: String, text: String) raises:
    with open(path, "w") as f:
        f.write(text)


def main() raises:
    var work_dir = (
        String(argv()[1]) if len(argv()) > 1 else "build/abi_fuzz_work"
    )
    var script = (
        String(argv()[2]) if len(argv())
        > 2 else "examples/abi_fuzz/build_and_compare.sh"
    )
    _ = run(String("mkdir -p ", work_dir))

    def differential(
        mut data: ConjectureData,
    ) raises {imm work_dir, imm script}:
        var gen = Gen()
        gen.draw_structs(data)
        gen.draw_fns(data)
        write_file(String(work_dir, "/abi.h"), gen.header())
        write_file(String(work_dir, "/callee.c"), gen.callee())
        write_file(String(work_dir, "/ref.c"), gen.reference())
        write_file(String(work_dir, "/program.mojo"), gen.program())
        var verdict = run(String("bash ", script, " ", work_dir, " 2>&1"))
        if not verdict.startswith("OK"):
            data.note(verdict)
            for name in ["abi.h", "callee.c", "ref.c", "program.mojo"]:
                _ = run(
                    String(
                        "cp ",
                        work_dir,
                        "/",
                        name,
                        " ",
                        work_dir,
                        "/failing_",
                        name,
                    )
                )
            # BUILD_FAIL means the generator wrote invalid code (or a
            # compiler rejected valid code); everything else is a bug
            fail(String(verdict.split("\n")[0]))

    var settings = Settings(
        database=None, deadline=None, max_examples=200, print_blob=True
    )
    if getenv("ABI_FUZZ_NO_SHRINK") != "":
        settings.phases = Phases(shrink=False, explain=False)
    var seconds = getenv("ABI_FUZZ_SECONDS")
    if seconds == "":
        given_data(differential, settings)
        print("no differences")
        return
    var target = fuzz_target_data(differential, settings)
    var report = target.fuzz(
        Float64(atof(seconds)), guided=getenv("ABI_FUZZ_BLIND") == ""
    )
    print("no differences:", report)
