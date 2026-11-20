# Differential testing of the Mojo compiler. Each test case draws a small
# program, builds it at -O0 and at -O3, evaluates its functions at compile
# time as well, and compares the three results. Any difference is a
# compiler bug, and proptest shrinks the program to a small one.
#
# Every generated program has exactly one defined result:
# - Integer overflow wraps (the manual says so).
# - `//` and `%` by zero give 0. `MIN // -1` and `MIN % -1` trap at run
#   time but wrap at compile time, so division goes through the `_div` and
#   `_mod` helpers, which handle -1 themselves.
# - Shift amounts are masked to 0..63.
# - Array and pool indices are masked to their sizes, and loops are
#   bounded.
#
# A program has up to six functions `fN(a, b, c) -> Int`. Each one works
# on four Int variables, an `Array` that it also writes through a raw
# pointer, an `Optional[Int]`, and a pool of four heap-allocated doubly linked
# nodes, reached through `Optional[Pointer]` cursors. It also has narrow and
# wide integers (8 to 256 bits, with the `std.bit` functions), SIMD
# vectors, and `Tracked` values, which count their copies and destructions
# and keep their value in a heap cell of their own (so that a build with
# `--sanitize address` reports any use of a destroyed one):
# in variables, struct fields, a `List`, an `Optional`, a `Dict`, a
# `Variant`, an `__enum`, and two heap cells that are written, taken and
# destroyed in place, plus a `Set[Int]`. Statements reach them through `ref`
# bindings, functions returning `ref`, and `match` and `if case` bindings
# (`match` also takes Ints, tuples and Optionals). Generic code runs
# through a trait `Op` (an associated constant, a default method, a static
# constructor) and generic structs nested over it, generic functions over
# `Copyable` values (Ints, narrow integers, `Tracked`), and a trait with an
# associated type. Closures get random capture lists (`imm`, `mut`, `var`,
# `var x^`, `{var^}`), may nest or raise, and go to generic higher-order
# functions. Each function returns a hash of all of them. `main` prints
# each function's result on constant arguments (lines starting with "c")
# and on the same arguments hidden behind `black_box` ("b"). A second file, comptime.mojo, computes the "c" lines
# with `comptime` and prints them.
#
# Build and run from the repository root:
#
#   pixi run mojo build -I . -o build/compiler_fuzz \
#       examples/compiler_fuzz/compiler_fuzz.mojo
#   pixi run build/compiler_fuzz build/compiler_fuzz_work
#
# To build with AddressSanitizer instead (without the comptime check), add
# examples/compiler_fuzz/asan_compare.sh as a second argument.
#
# Each test case takes a second or two, nearly all of it compiling.
# The compiler under test is $MOJO (default `mojo`); see
# build_and_compare.sh. COMPILER_FUZZ_NO_SHRINK=1 skips shrinking,
# COMPILER_FUZZ_NO_7593_WORKAROUND=1 lets `range` loops overwrite tracked
# values without reading them first (compilers before 1.3.0.dev2026111605
# then fail with UNBALANCED), and
# PROPTEST_SEED and PROPTEST_MAX_EXAMPLES set the seed and the number of
# programs. The failing program is kept as failing_program.mojo in the
# work directory.

from std.os import getenv
from std.subprocess import run
from std.sys import argv

from proptest import *


comptime CONSTANTS: List[String] = [
    "0",
    "1",
    "(-1)",
    "2",
    "3",
    "7",
    "8",
    "63",
    "64",
    "255",
    "(-128)",
    "65536",
    "(1 << 32)",
    "Int.MAX",
    "Int.MIN",
    "(Int.MAX - 1)",
    "(-7)",
    "1000003",
]
comptime N_VARIABLES = 4
comptime BUFFER_SIZE = 8
comptime POOL_SIZE = 4
comptime ASSIGNABLE_CURSORS: List[String] = ["q0", "q1"]
comptime NARROW_TYPES: List[String] = [
    "Int8",
    "UInt8",
    "Int16",
    "UInt16",
    "Int32",
    "UInt32",
    "UInt64",
    "Int128",
    "UInt128",
    "Int256",
    "UInt256",
]
"""The type of each narrow variable: `n0: Int8`, `n1: UInt8`, ..."""
comptime NARROW_DTYPES: List[String] = [
    "int8",
    "uint8",
    "int16",
    "uint16",
    "int32",
    "uint32",
    "uint64",
    "int128",
    "uint128",
    "int256",
    "uint256",
]
comptime NARROW_BITS: List[Int] = [8, 8, 16, 16, 32, 32, 64, 128, 128, 256, 256]
comptime N_NARROW = 11
comptime VEC_DTYPES: List[String] = [
    "int32",
    "uint16",
    "int16",
    "uint32",
    "uint8",
    "int64",
]
"""The lane type of each vector type `Vk` (the type of `sk`)."""
comptime VEC_SCALARS: List[String] = [
    "Int32",
    "UInt16",
    "Int16",
    "UInt32",
    "UInt8",
    "Int64",
]
comptime VEC_LANES: List[Int] = [4, 4, 8, 8, 16, 2]
comptime VEC_BITS: List[Int] = [32, 16, 16, 32, 8, 64]
comptime N_VEC = 6


struct ProgramGenerator(Movable):
    """Draws one function's body. Tracks the names in scope."""

    var loop_variables: List[String]
    """`for` loop indices in scope."""
    var cursors: List[String]
    """`Optional[NodePtr]` variables in scope."""
    var live_cursors: List[String]
    """Cursors known to be non-empty here (inside a walk over them)."""
    var loop_depth: Int
    var function_index: Int
    var calls: Int
    var guards: Int
    """Counters made so far for bounded `while` loops."""
    var budget: Int
    """Statements left in this function."""
    var tracked: List[String]
    """`Tracked` variables in scope."""
    var tracked_ok: Bool
    """Whether expressions may read tracked values here. Off in the
    arguments of anything that mutates one, to avoid exclusivity errors."""
    var try_depth: Int
    var touch_loops: Bool
    """Whether `range` loops read the tracked values first (the #7593
    workaround; see `block`)."""

    def __init__(out self, function_index: Int):
        self.loop_variables = []
        self.cursors = materialize[ASSIGNABLE_CURSORS]()
        self.live_cursors = []
        self.loop_depth = 0
        self.function_index = function_index
        self.calls = 0
        self.guards = 0
        self.budget = 30
        self.tracked = ["t0", "t1", "pr.x", "pr.y"]
        self.tracked_ok = True
        self.try_depth = 0
        self.touch_loops = getenv("COMPILER_FUZZ_NO_7593_WORKAROUND") == ""

    @staticmethod
    def pick(
        mut data: ConjectureData, var choices: List[String]
    ) raises -> String:
        return choices[data.draw(integers(0, len(choices) - 1))]

    # ---- Int expressions

    def atom(mut self, mut data: ConjectureData) raises -> String:
        var names: List[String] = ["a", "b", "c"]
        for i in range(N_VARIABLES):
            names.append(String("v", i))
        names += self.loop_variables.copy()
        return Self.pick(data, names^)

    @staticmethod
    def ternary(a: String, cond: String, b: String) -> String:
        # When the condition folds to a constant, a vector constructor
        # `Vk(x)` in the dead branch is typed as a scalar
        # (https://github.com/modular/modular/issues/7664), so the condition
        # goes through _cond if either branch builds a vector.
        if "V" in a or "V" in b:
            return String("(", a, " if _cond(", cond, ") else ", b, ")")
        return String("(", a, " if ", cond, " else ", b, ")")

    def int_expr(
        mut self, mut data: ConjectureData, depth: Int
    ) raises -> String:
        var choice = data.draw(integers(0, 18 if depth < 3 else 1))
        if choice == 0:
            return self.atom(data)
        if choice >= 17:
            return self.generic_expr(data, depth + 1)
        if choice == 1:
            return Self.pick(data, materialize[CONSTANTS]())
        var d = depth + 1
        if choice == 2:
            var op = Self.pick(data, ["+", "-", "*", "&", "|", "^"])
            return String(
                "(",
                self.int_expr(data, d),
                " ",
                op,
                " ",
                self.int_expr(data, d),
                ")",
            )
        if choice == 3:
            var f = "_div" if data.draw(booleans()) else "_mod"
            return String(
                f,
                "(",
                self.int_expr(data, d),
                ", ",
                self.int_expr(data, d),
                ")",
            )
        if choice == 4:
            var op = "<<" if data.draw(booleans()) else ">>"
            return String(
                "(",
                self.int_expr(data, d),
                " ",
                op,
                " (",
                self.int_expr(data, d),
                " & 63))",
            )
        if choice == 5:
            return String(
                "buf[", self.int_expr(data, d), " & ", BUFFER_SIZE - 1, "]"
            )
        if choice == 6:
            return String("opt.or_else(", self.int_expr(data, d), ")")
        if choice == 7:
            return self.ternary(
                self.int_expr(data, d),
                self.condition(data, d),
                self.int_expr(data, d),
            )
        if choice == 8:
            # not Int(cond): see unfiled-mojo-issue-ternary-dead-branch.md
            return String("(1 if ", self.condition(data, d), " else 0)")
        if choice == 9:
            var f = "_min" if data.draw(booleans()) else "_max"
            return String(
                f,
                "(",
                self.int_expr(data, d),
                ", ",
                self.int_expr(data, d),
                ")",
            )
        if choice == 10:
            # a node's value through a cursor
            if len(self.live_cursors) > 0 and data.draw(booleans()):
                return String(
                    Self.pick(data, self.live_cursors.copy()), ".value()[].val"
                )
            var c = self.cursor_expr(data, d)
            return String(
                "(",
                c,
                ".value()[].val if ",
                c,
                " else ",
                self.int_expr(data, d),
                ")",
            )
        if choice == 11:
            return String("pool.at(", self.int_expr(data, d), ")[].val")
        if choice == 12 and self.tracked_ok:
            var kind = data.draw(integers(0, 8))
            if kind == 4:
                return String("cells.at(", self.int_expr(data, d), ")[].val")
            if kind == 5:
                return "len(d)"
            if kind == 6:
                return "len(st)"
            if kind == 7:
                return "_tmix(en)"
            if kind == 8:
                return "_varmix(vr)"
            if kind == 0:
                return String(Self.pick(data, self.tracked.copy()), ".val")
            if kind == 1:
                return "len(lst)"
            if kind == 2:
                return "_sum(lst)"
            return String(
                "(ot.value().val if ot else ", self.int_expr(data, d), ")"
            )
        if choice == 13:
            var k = data.draw(integers(0, N_NARROW - 1))
            return String("Int(", self.narrow_expr(data, k, depth + 1), ")")
        if choice == 15:
            # a lane
            var k = data.draw(integers(0, N_VEC - 1))
            return String(
                "Int(",
                self.vec_expr(data, k, depth + 1),
                "[",
                self.int_expr(data, depth + 1),
                " & ",
                materialize[VEC_LANES]()[k] - 1,
                "])",
            )
        if choice == 16:
            var k = data.draw(integers(0, N_VEC - 1))
            var x = self.vec_expr(data, k, depth + 1)
            if data.draw(integers(0, 6)) == 0:
                return String(x, ".reduce_bit_count()")
            var f = Self.pick(
                data,
                [
                    "reduce_add",
                    "reduce_mul",
                    "reduce_max",
                    "reduce_min",
                    "reduce_and",
                    "reduce_or",
                ],
            )
            return String("Int(", x, ".", f, "())")
        # a call to an earlier function, at most twice per function and
        # never inside a loop, so run time stays linear
        if self.function_index > 0 and self.loop_depth == 0 and self.calls < 2:
            self.calls += 1
            var j = data.draw(integers(0, self.function_index - 1))
            return String(
                "f",
                j,
                "(",
                self.int_expr(data, d),
                ", ",
                self.int_expr(data, d),
                ", ",
                self.int_expr(data, d),
                ", L)",
            )
        return self.atom(data)

    # ---- narrow integer expressions: fixed width, signed or unsigned

    def narrow_expr(
        mut self, mut data: ConjectureData, k: Int, depth: Int
    ) raises -> String:
        """An expression of type `NARROW_TYPES[k]`, the type of `nk`."""
        var t = materialize[NARROW_TYPES]()[k]
        var bits = materialize[NARROW_BITS]()[k]
        var choice = data.draw(integers(0, 11 if depth < 3 else 1))
        var d = depth + 1
        if choice == 0:
            return String("n", k)
        if choice == 1:
            # out-of-range literals truncate
            return String(
                t, "(", Self.pick(data, materialize[CONSTANTS]()), ")"
            )
        if choice == 2:
            var op = Self.pick(data, ["+", "-", "*", "&", "|", "^"])
            return String(
                "(",
                self.narrow_expr(data, k, d),
                " ",
                op,
                " ",
                self.narrow_expr(data, k, d),
                ")",
            )
        if choice == 3:
            var f = "_ndiv" if data.draw(booleans()) else "_nmod"
            return String(
                f,
                "(",
                self.narrow_expr(data, k, d),
                ", ",
                self.narrow_expr(data, k, d),
                ")",
            )
        if choice == 4:
            # shifts of at least the width are undefined
            var op = "<<" if data.draw(booleans()) else ">>"
            return String(
                "(",
                self.narrow_expr(data, k, d),
                " ",
                op,
                " (",
                self.narrow_expr(data, k, d),
                " & ",
                t,
                "(",
                bits - 1,
                ")))",
            )
        if choice == 5:
            # a narrowing (truncating) conversion from Int
            return String(t, "(", self.int_expr(data, d), ")")
        if choice == 6:
            # a conversion from another width or signedness
            var j = data.draw(integers(0, N_NARROW - 1))
            var x = self.narrow_expr(data, j, d)
            if data.draw(booleans()):
                return String(t, "(", x, ")")
            return String(
                x, ".cast[DType.", materialize[NARROW_DTYPES]()[k], "]()"
            )
        if choice == 7:
            return self.ternary(
                self.narrow_expr(data, k, d),
                self.condition(data, d),
                self.narrow_expr(data, k, d),
            )
        if choice == 8:
            var f = "min" if data.draw(booleans()) else "max"
            return String(
                f,
                "(",
                self.narrow_expr(data, k, d),
                ", ",
                self.narrow_expr(data, k, d),
                ")",
            )
        if choice == 9:
            var op = "~" if data.draw(booleans()) else "-"
            return String("(", op, self.narrow_expr(data, k, d), ")")
        if choice == 10:
            # std.bit functions: LLVM intrinsics (ctpop, ctlz, cttz, bswap,
            # bitreverse, fshl/fshr)
            var x = self.narrow_expr(data, k, d)
            var f = data.draw(integers(0, 6))
            if f == 5 or f == 6:
                var name = "rotate_bits_left" if f == 5 else "rotate_bits_right"
                return String(
                    name, "[", data.draw(integers(0, bits - 1)), "](", x, ")"
                )
            var names: List[String] = [
                "pop_count",
                "count_leading_zeros",
                "count_trailing_zeros",
                "byte_swap",
                "bit_reverse",
            ]
            return String(names[f], "(", x, ")")
        return String("n", k)

    # ---- SIMD vector expressions

    def vec_expr(
        mut self, mut data: ConjectureData, k: Int, depth: Int
    ) raises -> String:
        """An expression of type `Vk`, a SIMD vector type (that of `sk`)."""
        var v = String("V", k)
        var t = materialize[VEC_SCALARS]()[k]
        var n = materialize[VEC_LANES]()[k]
        var bits = materialize[VEC_BITS]()[k]
        var choice = data.draw(integers(0, 19 if depth < 3 else 1))
        var d = depth + 1
        if choice == 0:
            return String("s", k)
        if choice == 1:
            # a splat, truncating
            return String(v, "(", self.int_expr(data, 3), ")")
        if choice == 2:
            var lanes = String(v, "(")
            for i in range(n):
                if i > 0:
                    lanes += ", "
                lanes += String(t, "(", self.int_expr(data, 3), ")")
            return lanes + ")"
        if choice == 3:
            var op = Self.pick(data, ["+", "-", "*", "&", "|", "^"])
            return String(
                "(",
                self.vec_expr(data, k, d),
                " ",
                op,
                " ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 4:
            var f = "_vdiv" if data.draw(booleans()) else "_vmod"
            return String(
                f,
                "(",
                self.vec_expr(data, k, d),
                ", ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 5:
            # shifts of at least the width are undefined
            var op = "<<" if data.draw(booleans()) else ">>"
            return String(
                "(",
                self.vec_expr(data, k, d),
                " ",
                op,
                " (",
                self.vec_expr(data, k, d),
                " & ",
                v,
                "(",
                bits - 1,
                ")))",
            )
        if choice == 6:
            # The condition goes through _cond: when it folds to a constant,
            # `V(x)` in the dead branch is typed as a scalar, which can
            # reject valid code or change the result's type
            # (https://github.com/modular/modular/issues/7664).
            return String(
                "(",
                self.vec_expr(data, k, d),
                " if _cond(",
                self.condition(data, d),
                ") else ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 7:
            var f = "min" if data.draw(booleans()) else "max"
            return String(
                f,
                "(",
                self.vec_expr(data, k, d),
                ", ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 8:
            var cmp = Self.pick(data, ["eq", "ne", "lt", "le", "gt", "ge"])
            return String(
                self.vec_expr(data, k, d),
                ".",
                cmp,
                "(",
                self.vec_expr(data, k, d),
                ").select(",
                self.vec_expr(data, k, d),
                ", ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 9:
            # a shuffle of one vector or two
            var two = data.draw(booleans())
            var top = 2 * n - 1 if two else n - 1
            var mask = String()
            for i in range(n):
                if i > 0:
                    mask += ", "
                mask += String(data.draw(integers(0, top)))
            var x = self.vec_expr(data, k, d)
            if two:
                return String(
                    x, ".shuffle[", mask, "](", self.vec_expr(data, k, d), ")"
                )
            return String(x, ".shuffle[", mask, "]()")
        if choice == 10:
            return String(self.vec_expr(data, k, d), ".reversed()")
        if choice == 11:
            # lane rotations and shifts (LLVM intrinsics at run time)
            var kind = data.draw(integers(0, 3))
            var x = self.vec_expr(data, k, d)
            if kind < 2:
                # rotate_left takes -n <= s < n, rotate_right -n < s <= n
                var f = "_rotl" if kind == 0 else "_rotr"
                return String(
                    f, "[", data.draw(integers(-n, n - 1)) + kind, "](", x, ")"
                )
            var f = "_lshift" if kind == 2 else "_rshift"
            return String(f, "[", data.draw(integers(0, n)), "](", x, ")")
        if choice == 12:
            # a lane conversion from a vector with as many lanes
            var lanes = materialize[VEC_LANES]()
            var same = List[Int]()
            for j in range(N_VEC):
                if lanes[j] == n:
                    same.append(j)
            var j = same[data.draw(integers(0, len(same) - 1))]
            return String(
                self.vec_expr(data, j, d),
                ".cast[DType.",
                materialize[VEC_DTYPES]()[k],
                "]()",
            )
        if choice == 13 or choice == 14:
            var f = ".join(" if choice == 13 else ".interleave("
            return String(
                self.vec_expr(data, k, d),
                f,
                self.vec_expr(data, k, d),
                ").slice[",
                n,
                ", offset=",
                data.draw(integers(0, n)),
                "]()",
            )
        if choice == 15:
            # insert a slice of width m at a multiple of m
            var m = 1
            var limit = data.draw(integers(0, 4))
            while m * 2 <= n and limit > 0:
                m *= 2
                limit -= 1
            var offset = m * data.draw(integers(0, n // m - 1))
            return String(
                "_vinsert[",
                offset,
                "](",
                self.vec_expr(data, k, d),
                ", ",
                self.vec_expr(data, k, d),
                ".slice[",
                m,
                ", offset=",
                data.draw(integers(0, n - m)),
                "]())",
            )
        if choice == 16:
            return String(
                "_vdeint[",
                data.draw(integers(0, 1)),
                "](",
                self.vec_expr(data, k, d),
                ", ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 17:
            return String(
                self.vec_expr(data, k, d),
                ".fma(",
                self.vec_expr(data, k, d),
                ", ",
                self.vec_expr(data, k, d),
                ")",
            )
        if choice == 18:
            var op = Self.pick(data, ["-", "~", "abs"])
            if op == "abs":
                return String("abs(", self.vec_expr(data, k, d), ")")
            return String("(", op, self.vec_expr(data, k, d), ")")
        if choice == 19:
            return String(
                "_vset(",
                self.vec_expr(data, k, d),
                ", ",
                self.int_expr(data, d),
                " & ",
                n - 1,
                ", ",
                t,
                "(",
                self.int_expr(data, d),
                "))",
            )
        return String("s", k)

    # ---- Optional[NodePtr] expressions

    @staticmethod
    def link(mut data: ConjectureData) raises -> String:
        """A node's link field."""
        return "next" if data.draw(booleans()) else "prev"

    def cursor_expr(
        mut self, mut data: ConjectureData, depth: Int
    ) raises -> String:
        """An `Optional[NodePtr]` without side effects, safe to evaluate twice.
        """
        var choice = data.draw(integers(0, 3 if depth < 3 else 0))
        if choice == 0:
            return Self.pick(data, self.cursors.copy())
        if choice == 1:
            return String(
                "pool.at(",
                self.int_expr(data, depth + 1),
                ")[].",
                Self.link(data),
            )
        if choice == 2 and len(self.live_cursors) > 0:
            # a field read through a cursor, as in issue 7534
            return String(
                Self.pick(data, self.live_cursors.copy()),
                ".value()[].",
                Self.link(data),
            )
        return String(
            "Optional[NodePtr](pool.at(", self.int_expr(data, depth + 1), "))"
        )

    # ---- Bool expressions

    def condition(
        mut self, mut data: ConjectureData, depth: Int
    ) raises -> String:
        var choice = data.draw(integers(0, 13 if depth < 3 else 0))
        var d = depth + 1
        if choice == 13 and self.tracked_ok:
            var coll = "d" if data.draw(booleans()) else "st"
            return String("((", self.int_expr(data, d), " & 7) in ", coll, ")")
        if choice == 0:
            var op = Self.pick(data, ["<", "==", "!=", ">="])
            return String(
                "(",
                self.int_expr(data, d),
                " ",
                op,
                " ",
                self.int_expr(data, d),
                ")",
            )
        if choice == 1:
            return "Bool(opt)"
        if choice == 2:
            return String(
                "(Bool(opt) and opt.value() < ", self.int_expr(data, d), ")"
            )
        if choice == 3:
            return String("(not ", self.condition(data, d), ")")
        if choice == 4:
            return String(
                "(",
                self.condition(data, d),
                " and ",
                self.condition(data, d),
                ")",
            )
        if choice == 5:
            return String(
                "(",
                self.condition(data, d),
                " or ",
                self.condition(data, d),
                ")",
            )
        if choice == 6:
            return String("((", self.int_expr(data, d), " & 1) == 1)")
        if choice == 7:
            return String("Bool(", self.cursor_expr(data, d), ")")
        if choice == 8:
            var c = self.cursor_expr(data, d)
            return String(
                "(Bool(",
                c,
                ") and ",
                c,
                ".value()[].val < ",
                self.int_expr(data, d),
                ")",
            )
        if choice == 9:
            var op = "==" if data.draw(booleans()) else "!="
            return String(
                "(",
                self.cursor_expr(data, d),
                " ",
                op,
                " ",
                self.cursor_expr(data, d),
                ")",
            )
        if choice == 11:
            var k = data.draw(integers(0, N_NARROW - 1))
            var op = Self.pick(data, ["<", "==", "!=", ">="])
            return String(
                "(",
                self.narrow_expr(data, k, d),
                " ",
                op,
                " ",
                self.narrow_expr(data, k, d),
                ")",
            )
        if choice == 12:
            var k = data.draw(integers(0, N_VEC - 1))
            var x = self.vec_expr(data, k, d)
            var y = self.vec_expr(data, k, d)
            if data.draw(booleans()):
                return String("(", x, " == ", y, ")")
            var cmp = Self.pick(data, ["eq", "ne", "lt", "le", "gt", "ge"])
            var f = "reduce_or" if data.draw(booleans()) else "reduce_and"
            return String(x, ".", cmp, "(", y, ").", f, "()")
        # x != y for Optional pointers, spelled out as in
        # https://github.com/modular/modular/issues/7534
        var x = self.cursor_expr(data, d)
        var y = self.cursor_expr(data, d)
        return String(
            "(Bool(",
            x,
            ") != Bool(",
            y,
            ") or (Bool(",
            y,
            ") and ",
            x,
            ".value() != ",
            y,
            ".value()))",
        )

    # ---- statements

    def variable(mut self, mut data: ConjectureData) raises -> String:
        return String("v", data.draw(integers(0, N_VARIABLES - 1)))

    def block(
        mut self, mut data: ConjectureData, indent: String, depth: Int
    ) raises -> String:
        var out = String()
        var n = data.draw(integers(0, 4 if depth < 3 else 1))
        var n_tracked = len(self.tracked)
        for _ in range(n):
            if self.budget <= 0:
                break
            self.budget -= 1
            out += self.statement(data, indent, depth)
        # locals declared in this block go out of scope
        while len(self.tracked) > n_tracked:
            _ = self.tracked.pop()
        if out == "":
            out = String(indent, "pass\n")
        return out

    def statement(
        mut self, mut data: ConjectureData, indent: String, depth: Int
    ) raises -> String:
        var choice = data.draw(integers(0, 46))
        var inner = indent + "    "
        if choice >= 41:
            return self.generic_statement(data, choice, indent, depth)
        if choice == 0:
            return String(
                indent, self.variable(data), " = ", self.int_expr(data, 0), "\n"
            )
        if choice == 1:
            var op = Self.pick(data, ["+=", "-=", "^=", "*="])
            return String(
                indent,
                self.variable(data),
                " ",
                op,
                " ",
                self.int_expr(data, 0),
                "\n",
            )
        if choice == 2:
            return String(
                indent,
                "buf[",
                self.int_expr(data, 1),
                " & ",
                BUFFER_SIZE - 1,
                "] = ",
                self.int_expr(data, 0),
                "\n",
            )
        if choice == 3:
            if data.draw(booleans()):
                return String(indent, "opt = None\n")
            return String(
                indent, "opt = Optional[Int](", self.int_expr(data, 0), ")\n"
            )
        if choice == 4 and depth < 3:
            var s = String(
                indent,
                "if ",
                self.condition(data, 0),
                ":\n",
                self.block(data, inner, depth + 1),
            )
            if data.draw(booleans()):
                s += String(
                    indent, "else:\n", self.block(data, inner, depth + 1)
                )
            return s
        if choice == 5 and depth < 3:
            var index = String("i", depth)
            var bound = data.draw(integers(0, 9))
            # Reading the tracked values first works around a bug: a
            # value overwritten in a range loop, unread before, isn't
            # destroyed at -O2/-O3
            # (https://github.com/modular/modular/issues/7593), fixed on
            # nightly 1.3.0.dev2026111605.
            # COMPILER_FUZZ_NO_7593_WORKAROUND=1 leaves the reads out.
            var touch = String()
            if self.touch_loops:
                touch = String(inner, "_ = Bool(ot)\n", inner, "_ = len(lst)\n")
                for name in self.tracked:
                    touch += String(inner, "_ = ", name, ".val\n")
            self.loop_variables.append(index)
            self.loop_depth += 1
            var body = String()
            # #7593's shape: a value overwritten before anything in the
            # loop reads it
            if data.draw(integers(0, 3)) == 0:
                body += self.overwrite_statement(data, inner)
            body += self.block(data, inner, depth + 1)
            self.loop_depth -= 1
            _ = self.loop_variables.pop()
            return String(
                indent, "for ", index, " in range(", bound, "):\n", touch, body
            )
        if choice == 6 and depth < 3:
            var guard = String("g", self.guards)
            self.guards += 1
            self.loop_depth += 1
            var cond = self.condition(data, 0)
            var body = self.block(data, inner, depth + 1)
            self.loop_depth -= 1
            # the counter is read after the loop, as in issue 7534
            return String(
                indent,
                "var ",
                guard,
                " = 0\n",
                indent,
                "while ",
                guard,
                " < 10 and ",
                cond,
                ":\n",
                inner,
                guard,
                " += 1\n",
                body,
                indent,
                self.variable(data),
                " ^= ",
                guard,
                "\n",
            )
        if choice == 7 and self.loop_depth > 0:
            var keyword = "break" if data.draw(booleans()) else "continue"
            return String(
                indent,
                "if ",
                self.condition(data, 0),
                ":\n",
                inner,
                keyword,
                "\n",
            )
        if choice == 8:
            return String(
                indent,
                "if ",
                self.condition(data, 0),
                ":\n",
                inner,
                "return ",
                Self.checksum(),
                "\n",
            )
        if choice == 9:
            # write through a raw pointer into buf, aliasing buf[...]
            return String(
                indent,
                "p[unsafe_offset=",
                self.int_expr(data, 1),
                " & ",
                BUFFER_SIZE - 1,
                "] = ",
                self.int_expr(data, 0),
                "\n",
            )
        if choice == 10:
            # relink a node
            var target = String(
                "pool.at(", self.int_expr(data, 1), ")[].", Self.link(data)
            )
            if data.draw(booleans()):
                return String(indent, target, " = None\n")
            var c = self.cursor_expr(data, 0)
            return String(indent, target, " = ", c, "\n")
        if choice == 11:
            # change a node's value, directly or through a cursor
            if data.draw(booleans()):
                return String(
                    indent,
                    "pool.at(",
                    self.int_expr(data, 1),
                    ")[].val = ",
                    self.int_expr(data, 0),
                    "\n",
                )
            var c = Self.pick(data, self.cursors.copy())
            if c in self.live_cursors:
                return String(
                    indent,
                    c,
                    ".value()[].val += ",
                    self.int_expr(data, 0),
                    "\n",
                )
            return String(
                indent,
                "if ",
                c,
                ":\n",
                inner,
                c,
                ".value()[].val += ",
                self.int_expr(data, 0),
                "\n",
            )
        if choice == 12:
            # move an assignable cursor
            var q = Self.pick(data, materialize[ASSIGNABLE_CURSORS]())
            var kind = data.draw(integers(0, 2))
            if kind == 0:
                return String(indent, q, " = None\n")
            if kind == 1:
                return String(indent, q, " = ", self.cursor_expr(data, 0), "\n")
            return String(
                indent,
                "if ",
                q,
                ":\n",
                inner,
                q,
                " = ",
                q,
                ".value()[].",
                Self.link(data),
                "\n",
            )
        if choice == 13 and depth < 3:
            # walk the list from a cursor, at most ten steps (lists can
            # be cycles); the body sees the cursor as non-empty
            var guard = String("g", self.guards)
            var walker = String("w", self.guards)
            self.guards += 1
            var start = self.cursor_expr(data, 0)
            var direction = Self.link(data)
            var cond = String("")
            if data.draw(booleans()):
                cond = String(" and ", self.condition(data, 0))
            self.cursors.append(walker)
            self.live_cursors.append(walker)
            self.loop_depth += 1
            var body = self.block(data, inner, depth + 1)
            # The usual idiom for checking a list: a cursor trailing the
            # walker, and a check that the walker's back link points at it
            # (the shape of issue 7534).
            var trail = String("")
            if data.draw(booleans()):
                var q = Self.pick(data, materialize[ASSIGNABLE_CURSORS]())
                trail = String(inner, q, " = ", walker, "\n")
                if data.draw(booleans()):
                    var back = "prev" if direction == "next" else "next"
                    var x = String(walker, ".value()[].", back)
                    var check = String(
                        inner,
                        "if Bool(",
                        x,
                        ") != Bool(",
                        q,
                        ") or (Bool(",
                        q,
                        ") and ",
                        x,
                        ".value() != ",
                        q,
                        ".value()):\n",
                    )
                    if data.draw(booleans()):
                        check += String(
                            inner, "    return ", Self.checksum(), "\n"
                        )
                    else:
                        check += String(
                            inner, "    ", self.variable(data), " += 1\n"
                        )
                    body = check + body
            self.loop_depth -= 1
            _ = self.live_cursors.pop()
            _ = self.cursors.pop()
            return String(
                indent,
                "var ",
                guard,
                " = 0\n",
                indent,
                "var ",
                walker,
                " = ",
                start,
                "\n",
                indent,
                "while ",
                walker,
                " and ",
                guard,
                " < 10",
                cond,
                ":\n",
                inner,
                guard,
                " += 1\n",
                body,
                trail,
                inner,
                walker,
                " = ",
                walker,
                ".value()[].",
                direction,
                "\n",
                indent,
                self.variable(data),
                " ^= ",
                guard,
                "\n",
            )
        if choice == 15:
            # build a doubly linked chain from node 0
            var n = data.draw(integers(1, POOL_SIZE - 1))
            return String(
                indent,
                "for k in range(",
                n,
                "):\n",
                inner,
                "pool.at(k)[].next = Optional[NodePtr](pool.at(k + 1))\n",
                inner,
                "pool.at(k + 1)[].prev = Optional[NodePtr](pool.at(k))\n",
            )
        if choice == 14:
            # link two nodes both ways, keeping next and prev consistent
            var i = self.int_expr(data, 1)
            var j = self.int_expr(data, 1)
            return String(
                indent,
                "pool.at(",
                i,
                ")[].next = Optional[NodePtr](pool.at(",
                j,
                "))\n",
                indent,
                "pool.at(",
                j,
                ")[].prev = Optional[NodePtr](pool.at(",
                i,
                "))\n",
            )
        if choice == 24:
            var k = data.draw(integers(0, N_NARROW - 1))
            var op = Self.pick(data, ["=", "+=", "-=", "*=", "^=", "<<="])
            var e = self.narrow_expr(data, k, 0)
            if op == "<<=":
                e = String(
                    "(",
                    e,
                    " & ",
                    materialize[NARROW_TYPES]()[k],
                    "(",
                    materialize[NARROW_BITS]()[k] - 1,
                    "))",
                )
            return String(indent, "n", k, " ", op, " ", e, "\n")
        if choice == 25:
            var k = data.draw(integers(0, N_VEC - 1))
            var op = Self.pick(data, ["=", "+=", "-=", "*=", "^=", "&=", "|="])
            return String(
                indent, "s", k, " ", op, " ", self.vec_expr(data, k, 0), "\n"
            )
        if choice == 26:
            # a lane store
            var k = data.draw(integers(0, N_VEC - 1))
            return String(
                indent,
                "s",
                k,
                "[",
                self.int_expr(data, 1),
                " & ",
                materialize[VEC_LANES]()[k] - 1,
                "] = ",
                materialize[VEC_SCALARS]()[k],
                "(",
                self.int_expr(data, 0),
                ")\n",
            )
        if choice >= 37:
            # more weight on Dict, __enum and match statements
            var c = [32, 32, 35, 36][choice - 37]
            return self.collection_statement(data, c, indent, depth)
        if choice >= 32:
            return self.collection_statement(data, choice, indent, depth)
        if choice >= 27:
            return self.place_statement(data, choice, indent)
        if choice >= 16:
            return self.ownership_statement(data, choice, indent, depth)
        return String(
            indent, self.variable(data), " = ", self.int_expr(data, 0), "\n"
        )

    # ---- ownership: Tracked values, which count their copies and
    # destructions in the ledger L

    def plain_expr(
        mut self, mut data: ConjectureData, depth: Int
    ) raises -> String:
        """An Int expression that reads no tracked value."""
        var saved = self.tracked_ok
        self.tracked_ok = False
        var e = self.int_expr(data, depth)
        self.tracked_ok = saved
        return e

    def two_tracked(
        mut self, mut data: ConjectureData
    ) raises -> Tuple[String, String]:
        """Two different tracked variables."""
        var i = data.draw(integers(0, len(self.tracked) - 1))
        var j = data.draw(integers(0, len(self.tracked) - 2))
        if j >= i:
            j += 1
        return (self.tracked[i], self.tracked[j])

    def overwrite_statement(
        mut self, mut data: ConjectureData, indent: String
    ) raises -> String:
        """Overwrites a tracked value without reading it first."""
        var t = Self.pick(data, self.tracked.copy())
        var fresh = String("Tracked(", self.plain_expr(data, 0), ", L)")
        var kind = data.draw(integers(0, 3))
        if kind == 0:
            return String(indent, t, " = ", fresh, "\n")
        if kind == 1:
            return String(indent, "ot = ", fresh, "\n")
        if kind == 2:
            return String(indent, "ot = ", t, ".copy()\n")
        var pair = self.two_tracked(data)
        return String(
            indent,
            pair[0],
            " = ",
            pair[1],
            "^\n",
            indent,
            pair[1],
            " = ",
            fresh,
            "\n",
        )

    def ownership_statement(
        mut self,
        mut data: ConjectureData,
        choice: Int,
        indent: String,
        depth: Int,
    ) raises -> String:
        var inner = indent + "    "
        var t = Self.pick(data, self.tracked.copy())
        var fresh = String("Tracked(", self.atom(data), ", L)")
        if choice == 16:
            # assign, copy, swap, mutate in place or through a mut argument
            var kind = data.draw(integers(0, 4))
            if kind == 0:
                return String(
                    indent, t, " = Tracked(", self.plain_expr(data, 0), ", L)\n"
                )
            if kind == 1:
                return String(
                    indent,
                    t,
                    " = ",
                    Self.pick(data, self.tracked.copy()),
                    ".copy()\n",
                )
            if kind == 2:
                var pair = self.two_tracked(data)
                return String(indent, "swap(", pair[0], ", ", pair[1], ")\n")
            if kind == 3:
                var op = Self.pick(data, ["+=", "-=", "^=", "*="])
                return String(
                    indent, t, ".val ", op, " ", self.plain_expr(data, 0), "\n"
                )
            return String(
                indent, "_bump(", t, ", ", self.plain_expr(data, 0), ")\n"
            )
        if choice == 17:
            # moves; a moved-from variable is reinitialized at once
            var kind = data.draw(integers(0, 2))
            if kind == 0:
                return String(
                    indent,
                    self.variable(data),
                    " += _consume(",
                    t,
                    "^)\n",
                    indent,
                    t,
                    " = ",
                    fresh,
                    "\n",
                )
            if kind == 1:
                return String(
                    indent,
                    self.variable(data),
                    " += _consume(",
                    t,
                    ".copy())\n",
                )
            var pair = self.two_tracked(data)
            return String(
                indent,
                pair[0],
                " = ",
                pair[1],
                "^\n",
                indent,
                pair[1],
                " = ",
                fresh,
                "\n",
            )
        if choice == 18:
            # the list owns its elements
            var kind = data.draw(integers(0, 11))
            if kind == 8:
                return String(
                    indent,
                    "if len(lst) > 1:\n",
                    inner,
                    "lst.swap_elements((",
                    self.plain_expr(data, 1),
                    " & 1023) % len(lst), (",
                    self.plain_expr(data, 1),
                    " & 1023) % len(lst))\n",
                )
            if kind == 9:
                return String(indent, "lst.reverse()\n")
            if kind == 10:
                return String(
                    indent,
                    "if lst:\n",
                    inner,
                    t,
                    " = _pop_at(lst, ",
                    self.plain_expr(data, 1),
                    ")\n",
                )
            if kind == 11:
                return String(
                    indent,
                    "if lst:\n",
                    inner,
                    "lst[(",
                    self.plain_expr(data, 1),
                    " & 1023) % len(lst)] = ",
                    fresh,
                    "\n",
                )
            if kind == 0:
                return String(
                    indent,
                    "lst.append(Tracked(",
                    self.plain_expr(data, 0),
                    ", L))\n",
                )
            if kind == 1:
                return String(indent, "lst.append(", t, ".copy())\n")
            if kind == 2:
                return String(
                    indent,
                    "lst.append(",
                    t,
                    "^)\n",
                    indent,
                    t,
                    " = ",
                    fresh,
                    "\n",
                )
            if kind == 3:
                return String(indent, "if lst:\n", inner, t, " = lst.pop()\n")
            if kind == 4:
                return String(indent, "if lst:\n", inner, "_ = lst.pop()\n")
            if kind == 5:
                return String(indent, "lst.clear()\n")
            if kind == 6:
                return String(
                    indent,
                    "_insert(lst, ",
                    self.plain_expr(data, 1),
                    ", ",
                    t,
                    ".copy())\n",
                )
            var k = String("k", self.guards)
            self.guards += 1
            return String(
                indent,
                "if lst:\n",
                inner,
                "var ",
                k,
                " = (",
                self.plain_expr(data, 1),
                " & 1023) % len(lst)\n",
                inner,
                "lst[",
                k,
                "].val += ",
                self.plain_expr(data, 0),
                "\n",
            )
        if choice == 19:
            # an Optional owns at most one
            var kind = data.draw(integers(0, 4))
            if kind == 0:
                return String(
                    indent, "ot = Tracked(", self.plain_expr(data, 0), ", L)\n"
                )
            if kind == 1:
                return String(indent, "ot = None\n")
            if kind == 2:
                return String(indent, "ot = ", t, ".copy()\n")
            if kind == 3:
                return String(
                    indent,
                    "if ot:\n",
                    inner,
                    "ot.value().val += ",
                    self.plain_expr(data, 0),
                    "\n",
                )
            return String(indent, "if ot:\n", inner, t, " = ot.take()\n")
        if choice == 20:
            # a local, destroyed after its last use
            var name = String("l", self.guards)
            self.guards += 1
            var init = self.plain_expr(data, 0)
            self.tracked.append(name)
            return String(indent, "var ", name, " = Tracked(", init, ", L)\n")
        if choice == 21:
            # a closure that captures a tracked value by reference (a
            # variable, not a field)
            var plain = List[String]()
            for name in self.tracked:
                if "." not in name:
                    plain.append(name)
            t = Self.pick(data, plain^)
            var name = String("cl", self.guards)
            self.guards += 1
            var s = String(
                indent,
                "def ",
                name,
                "(x: Int) {mut ",
                t,
                "} -> Int:\n",
                inner,
                t,
                ".val = ",
                t,
                ".val * 3 + x\n",
                inner,
                "return ",
                t,
                ".val\n",
                indent,
                self.variable(data),
                " += ",
                name,
                "(",
                self.plain_expr(data, 0),
                ")\n",
            )
            if data.draw(booleans()):
                s += String(
                    indent,
                    self.variable(data),
                    " ^= ",
                    name,
                    "(",
                    self.plain_expr(data, 0),
                    ")\n",
                )
            return s
        if choice == 22 and depth < 3:
            # values made in a try block are destroyed when it raises
            self.try_depth += 1
            var body = self.block(data, inner, depth + 1)
            self.try_depth -= 1
            var s = String(
                indent,
                "try:\n",
                body,
                indent,
                "except:\n",
                inner,
                self.variable(data),
                " += 1\n",
            )
            if data.draw(booleans()):
                s += String(
                    indent, "finally:\n", inner, self.variable(data), " ^= 2\n"
                )
            return s
        if choice == 23 and self.try_depth > 0:
            return String(
                indent,
                "if ",
                self.condition(data, 0),
                ":\n",
                inner,
                'raise Error("r")\n',
            )
        return String(indent, t, ".val += ", self.plain_expr(data, 0), "\n")

    def place_statement(
        mut self, mut data: ConjectureData, choice: Int, indent: String
    ) raises -> String:
        """References (`ref` bindings and functions returning `ref`), heap
        cells of tracked values, and tuple assignment."""
        var inner = indent + "    "
        var t = Self.pick(data, self.tracked.copy())
        var fresh = String("Tracked(", self.plain_expr(data, 0), ", L)")
        var r = String("r", self.guards)
        self.guards += 1
        if choice == 27:
            # a reference to a buf element, used across a write through
            # the raw pointer p, which may alias it
            var target = String("buf[", self.int_expr(data, 1), " & 7]")
            if data.draw(booleans()):
                target = String("_elem(buf, ", self.int_expr(data, 1), ")")
            if data.draw(integers(0, 3)) == 0:
                var op = Self.pick(data, ["+=", "^=", "*="])
                return String(
                    indent, target, " ", op, " ", self.int_expr(data, 0), "\n"
                )
            var s = String(indent, "ref ", r, " = ", target, "\n")
            if data.draw(booleans()):
                s += String(
                    indent,
                    "p[unsafe_offset=",
                    self.int_expr(data, 1),
                    " & 7] = ",
                    self.int_expr(data, 0),
                    "\n",
                )
            if data.draw(booleans()):
                s += String(
                    indent, r, " = ", r, " * 3 + ", self.int_expr(data, 0), "\n"
                )
            else:
                s += String(indent, r, " += ", self.int_expr(data, 0), "\n")
            if data.draw(booleans()):
                s += String(indent, self.variable(data), " ^= ", r, "\n")
            return s
        if choice == 28:
            # a reference to a tracked value
            var kind = data.draw(integers(0, 3))
            var s: String
            if kind == 0:
                var pair = self.two_tracked(data)
                var saved = self.tracked_ok
                self.tracked_ok = False
                var cond = self.condition(data, 1)
                self.tracked_ok = saved
                s = String(
                    indent,
                    "ref ",
                    r,
                    " = _pick(",
                    cond,
                    ", ",
                    pair[0],
                    ", ",
                    pair[1],
                    ")\n",
                )
            elif kind == 1:
                s = String(indent, "ref ", r, " = ", t, "\n")
            elif kind == 2:
                s = String(
                    indent,
                    "ref ",
                    r,
                    " = cells.at(",
                    self.plain_expr(data, 1),
                    ")[]\n",
                )
            else:
                var k = String("k", self.guards)
                self.guards += 1
                return String(
                    indent,
                    "if lst:\n",
                    inner,
                    "var ",
                    k,
                    " = (",
                    self.plain_expr(data, 1),
                    " & 1023) % len(lst)\n",
                    inner,
                    "ref ",
                    r,
                    " = lst[",
                    k,
                    "]\n",
                    inner,
                    r,
                    ".val = ",
                    r,
                    ".val * 5 + ",
                    self.plain_expr(data, 0),
                    "\n",
                )
            if data.draw(booleans()):
                s += String(
                    indent,
                    r,
                    ".val = ",
                    r,
                    ".val * 5 + ",
                    self.plain_expr(data, 0),
                    "\n",
                )
            else:
                s += String(
                    indent, "_bump(", r, ", ", self.plain_expr(data, 0), ")\n"
                )
            if data.draw(booleans()):
                s += String(indent, self.variable(data), " += ", r, ".val\n")
            return s
        if choice == 29:
            # heap cells: values written, taken and destroyed in place
            var i = String("ci", self.guards)
            self.guards += 1
            var at = String("cells.at(", i, ")")
            var s = String(
                indent, "var ", i, " = ", self.plain_expr(data, 1), "\n"
            )
            var kind = data.draw(integers(0, 7))
            if kind == 0:
                return s + String(indent, at, "[] = ", fresh, "\n")
            if kind == 1:
                return s + String(indent, at, "[] = ", t, ".copy()\n")
            if kind == 2:
                return s + String(indent, t, " = ", at, "[].copy()\n")
            if kind == 3:
                var x = String("tk", self.guards)
                self.guards += 1
                return s + String(
                    indent,
                    "var ",
                    x,
                    " = ",
                    at,
                    ".unsafe_take_pointee()\n",
                    indent,
                    at,
                    ".unsafe_write(Tracked(",
                    x,
                    ".val * 3 + ",
                    self.plain_expr(data, 0),
                    ", L))\n",
                )
            if kind == 4:
                return s + String(
                    indent,
                    at,
                    ".unsafe_deinit_pointee()\n",
                    indent,
                    at,
                    ".unsafe_write(",
                    t,
                    ".copy())\n",
                )
            if kind == 5:
                return s + String(
                    indent,
                    at,
                    ".swap_pointees(cells.at(",
                    self.plain_expr(data, 1),
                    "))\n",
                )
            if kind == 6:
                # rotate: take one, move the other into it, put it back
                var x = String("tk", self.guards)
                self.guards += 1
                return s + String(
                    indent,
                    "var ",
                    x,
                    " = ",
                    at,
                    ".unsafe_take_pointee()\n",
                    indent,
                    at,
                    ".unsafe_write_move_from(cells.at(",
                    i,
                    " + 1))\n",
                    indent,
                    "cells.at(",
                    i,
                    " + 1).unsafe_write(",
                    x,
                    "^)\n",
                )
            return s + String(indent, "swap(", at, "[], ", t, ")\n")
        if choice == 30:
            # a node through a reference
            var s = String(
                indent,
                "ref ",
                r,
                " = pool.at(",
                self.int_expr(data, 1),
                ")[]\n",
            )
            s += String(
                indent,
                r,
                ".val = ",
                r,
                ".val * 5 + ",
                self.int_expr(data, 0),
                "\n",
            )
            if data.draw(booleans()):
                s += String(
                    indent,
                    r,
                    ".",
                    Self.link(data),
                    " = ",
                    self.cursor_expr(data, 0),
                    "\n",
                )
            return s
        # tuple assignment
        if data.draw(booleans()):
            var pair = self.two_tracked(data)
            if data.draw(booleans()):
                return String(
                    indent,
                    pair[0],
                    ", ",
                    pair[1],
                    " = ",
                    pair[1],
                    "^, ",
                    pair[0],
                    "^\n",
                )
            return String(
                indent,
                pair[0],
                ", ",
                pair[1],
                " = ",
                pair[1],
                ".copy(), ",
                pair[0],
                "^\n",
            )
        var x = self.variable(data)
        var y = self.variable(data)
        if x == y:
            return String(indent, x, " = ", self.int_expr(data, 0), "\n")
        return String(
            indent, x, ", ", y, " = ", y, ", ", self.int_expr(data, 0), "\n"
        )

    def arm(
        mut self,
        mut data: ConjectureData,
        indent: String,
        depth: Int,
        var bound: List[String],
    ) raises -> String:
        """A `case` body. `bound` names Int bindings to an rvalue subject,
        which the body may read like loop indices."""
        var n = len(self.loop_variables)
        self.loop_variables += bound^
        var body = self.block(data, indent, depth + 1) if depth < 3 else String(
            indent, self.variable(data), " += ", self.atom(data), "\n"
        )
        while len(self.loop_variables) > n:
            _ = self.loop_variables.pop()
        return body

    def collection_statement(
        mut self,
        mut data: ConjectureData,
        choice: Int,
        indent: String,
        depth: Int,
    ) raises -> String:
        """A `Dict` and a `Set`, a `Variant`, and `match` on an `__enum`,
        Optionals, Ints and tuples."""
        var inner = indent + "    "
        var t = Self.pick(data, self.tracked.copy())
        var fresh = String("Tracked(", self.plain_expr(data, 0), ", L)")
        var n = self.guards
        self.guards += 1
        var key = String("dk", n)
        var r = String("r", n)
        var bx = String("x", n)
        var by = String("y", n)
        var s = String(
            indent, "var ", key, " = ", self.plain_expr(data, 1), " & 7\n"
        )
        if choice == 32:
            # a Dict of tracked values
            var kind = data.draw(integers(0, 13))
            if kind == 0:
                return s + String(indent, "d[", key, "] = ", fresh, "\n")
            if kind == 1:
                return s + String(indent, "d[", key, "] = ", t, ".copy()\n")
            if kind == 2:
                return s + String(
                    indent,
                    "if ",
                    key,
                    " in d:\n",
                    inner,
                    "try:\n",
                    inner,
                    "    d[",
                    key,
                    "].val += ",
                    self.plain_expr(data, 0),
                    "\n",
                    inner,
                    "except:\n",
                    inner,
                    "    pass\n",
                )
            if kind == 3:
                return s + String(
                    indent, t, " = d.pop(", key, ", ", fresh, ")\n"
                )
            if kind == 4:
                # the default is the value it replaces
                return s + String(indent, t, " = d.pop(", key, ", ", t, "^)\n")
            if kind == 5:
                return s + String(
                    indent,
                    "try:\n",
                    inner,
                    t,
                    " = d.pop(",
                    key,
                    ")\n",
                    indent,
                    "except:\n",
                    inner,
                    self.variable(data),
                    " += 1\n",
                )
            if kind == 6:
                var g = String("dg", n)
                return s + String(
                    indent,
                    "var ",
                    g,
                    " = d.get(",
                    key,
                    ")\n",
                    indent,
                    "if ",
                    g,
                    ":\n",
                    inner,
                    self.variable(data),
                    " += ",
                    g,
                    ".value().val\n",
                )
            if kind == 7:
                return s + String(
                    indent,
                    "try:\n",
                    inner,
                    "ref ",
                    r,
                    " = d[",
                    key,
                    "]\n",
                    inner,
                    r,
                    ".val = ",
                    r,
                    ".val * 5 + ",
                    self.plain_expr(data, 0),
                    "\n",
                    indent,
                    "except:\n",
                    inner,
                    "pass\n",
                )
            if kind == 8:
                return s + String(
                    indent,
                    "ref ",
                    r,
                    " = d.setdefault(",
                    key,
                    ", ",
                    fresh,
                    ")\n",
                    indent,
                    r,
                    ".val += ",
                    self.plain_expr(data, 0),
                    "\n",
                )
            if kind == 9:
                var e = String("de", n)
                return s + String(
                    indent,
                    "try:\n",
                    inner,
                    "var ",
                    e,
                    " = d.popitem()\n",
                    inner,
                    self.variable(data),
                    " += ",
                    e,
                    ".key * 3 + ",
                    e,
                    ".value.val\n",
                    indent,
                    "except:\n",
                    inner,
                    "pass\n",
                )
            if kind == 10:
                return s + String(indent, "d.clear()\n")
            if kind == 11:
                var v = self.variable(data)
                return s + String(
                    indent,
                    "for e in d.items():\n",
                    inner,
                    v,
                    " = ",
                    v,
                    " * 7 + e.key + e.value.val\n",
                )
            if kind == 12:
                return s + String(
                    indent,
                    "for ref x in d.values():\n",
                    inner,
                    "x.val = x.val * 3 + ",
                    key,
                    "\n",
                )
            # a modified copy swapped in; the old dict dies here
            var dc = String("dc", n)
            return s + String(
                indent,
                "var ",
                dc,
                " = d.copy()\n",
                indent,
                dc,
                "[",
                key,
                "] = ",
                fresh,
                "\n",
                indent,
                "swap(d, ",
                dc,
                ")\n",
            )
        if choice == 33:
            # a Set of Ints
            var kind = data.draw(integers(0, 7))
            if kind == 0:
                return s + String(indent, "st.add(", key, ")\n")
            if kind == 1:
                return s + String(indent, "st.discard(", key, ")\n")
            if kind == 2:
                return s + String(
                    indent,
                    "try:\n",
                    inner,
                    "st.remove(",
                    key,
                    ")\n",
                    indent,
                    "except:\n",
                    inner,
                    self.variable(data),
                    " += 1\n",
                )
            if kind == 3:
                var op = Self.pick(data, ["|", "&", "-", "^"])
                var other = String(
                    "Set[Int](",
                    key,
                    ", (",
                    self.plain_expr(data, 1),
                    ") & 7, ",
                    data.draw(integers(0, 7)),
                    ")",
                )
                if data.draw(booleans()):
                    return s + String(indent, "st ", op, "= ", other, "\n")
                return s + String(indent, "st = st ", op, " ", other, "\n")
            if kind == 4:
                return s + String(
                    indent,
                    "try:\n",
                    inner,
                    self.variable(data),
                    " += st.pop()\n",
                    indent,
                    "except:\n",
                    inner,
                    "pass\n",
                )
            if kind == 5:
                var v = self.variable(data)
                return s + String(
                    indent, "for k in st:\n", inner, v, " = ", v, " * 3 + k\n"
                )
            if kind == 6:
                return s + String(indent, "st.clear()\n")
            return s + String(
                indent,
                "if ",
                key,
                " in st:\n",
                inner,
                self.variable(data),
                " += ",
                key,
                "\n",
            )
        if choice == 34:
            # a Variant[Int, Tracked]
            var kind = data.draw(integers(0, 7))
            var e = self.plain_expr(data, 0)
            if kind == 0:
                return String(indent, "vr = TV(Int(", e, "))\n")
            if kind == 1:
                return String(indent, "vr.set[Tracked](", fresh, ")\n")
            if kind == 2:
                return String(indent, "vr = TV(", t, ".copy())\n")
            if kind == 3:
                return String(
                    indent,
                    "if vr.isa[Tracked]():\n",
                    inner,
                    "vr[Tracked].val += ",
                    e,
                    "\n",
                )
            if kind == 4:
                return String(
                    indent,
                    "if vr.isa[Tracked]():\n",
                    inner,
                    t,
                    " = vr.replace[Int, Tracked](",
                    e,
                    ")\n",
                )
            if kind == 5:
                return String(
                    indent,
                    "if vr.isa[Int]():\n",
                    inner,
                    self.variable(data),
                    " += vr[Int]\n",
                    inner,
                    "vr[Int] = ",
                    e,
                    "\n",
                )
            if kind == 6:
                return String(
                    indent,
                    "if vr.isa[Tracked]():\n",
                    inner,
                    "swap(vr[Tracked], ",
                    t,
                    ")\n",
                )
            return String(
                indent,
                "if vr.isa[Int]():\n",
                inner,
                self.variable(data),
                " ^= vr.replace[Tracked, Int](",
                fresh,
                ")\n",
            )
        if choice == 35:
            # the __enum Tok
            var kind = data.draw(integers(0, 4))
            var e = self.plain_expr(data, 0)
            if kind == 0:
                var value = Self.pick(
                    data,
                    [
                        "materialize[Tok.empty]()",
                        String(".num(", e, ")"),
                        String(".two(", e, ", ", self.plain_expr(data, 0), ")"),
                        String(".tr(", fresh, ")"),
                        String(".tr(", t, ".copy())"),
                        String(".both(", e, ", ", fresh, ")"),
                    ],
                )
                return String(indent, "en = ", value, "\n")
            if kind == 1:
                # bindings into the subject, then a body that may assign it
                var v = self.variable(data)
                var cases = List[String]()
                cases.append(
                    String(
                        indent,
                        "case .tr(ref ",
                        r,
                        "):\n",
                        inner,
                        r,
                        ".val = ",
                        r,
                        ".val * 5 + ",
                        e,
                        "\n",
                    )
                )
                cases.append(
                    String(
                        indent,
                        "case .both(",
                        bx,
                        ", ref ",
                        r,
                        ") if ",
                        bx,
                        " < ",
                        self.plain_expr(data, 1),
                        ":\n",
                        inner,
                        r,
                        ".val += ",
                        bx,
                        "\n",
                    )
                )
                cases.append(
                    String(
                        indent,
                        "case .num(",
                        bx,
                        ") | .two(",
                        bx,
                        ", _) | .both(",
                        bx,
                        ", _):\n",
                        inner,
                        v,
                        " = ",
                        v,
                        " * 3 + ",
                        bx,
                        "\n",
                    )
                )
                cases.append(
                    String(
                        indent,
                        "case .two(",
                        bx,
                        ", ",
                        by,
                        ") if ",
                        bx,
                        " < ",
                        by,
                        ":\n",
                        inner,
                        v,
                        " += ",
                        by,
                        " - ",
                        bx,
                        "\n",
                    )
                )
                cases.append(String(indent, "case .empty:\n", inner, "pass\n"))
                var out = String(indent, "match en:\n")
                # a random subset in a random order, then a catch-all
                var m = data.draw(integers(1, len(cases)))
                for _ in range(m):
                    var j = data.draw(integers(0, len(cases) - 1))
                    out += cases.pop(j)
                    if data.draw(integers(0, 2)) == 0:
                        out += self.arm(data, inner, depth, [])
                out += String(indent, "case _:\n")
                out += self.arm(data, inner, depth, [])
                return out
            if kind == 2:
                # var bindings of Int payloads only: one of a Tracked
                # payload is destroyed twice
                # (https://github.com/modular/modular/issues/7418), and
                # two or an or-pattern copy it (issue 7659). The subject is
                # a copy, not `en^`: a var binding on a moved subject and
                # any other binding on it in the same function fail to
                # compile (issue 7649).
                var v = self.variable(data)
                return String(
                    indent,
                    "match en.copy():\n",
                    indent,
                    "case .num(var ",
                    bx,
                    ") | .two(_, var ",
                    bx,
                    ") | .both(var ",
                    bx,
                    ", _):\n",
                    inner,
                    bx,
                    " = ",
                    bx,
                    " * 3 + ",
                    e,
                    "\n",
                    inner,
                    v,
                    " ^= ",
                    bx,
                    "\n",
                    indent,
                    "case _:\n",
                    inner,
                    "pass\n",
                )
            if kind == 3:
                return String(
                    indent,
                    "if case .tr(ref ",
                    r,
                    ") = en:\n",
                    inner,
                    "swap(",
                    r,
                    ", ",
                    t,
                    ")\n",
                    indent,
                    "elif case .num(",
                    bx,
                    ") = en:\n",
                    inner,
                    "en = .two(",
                    bx,
                    ", ",
                    e,
                    ")\n",
                )
            return String(
                indent,
                self.variable(data),
                " += _tmix(en)\n",
            )
        # match on Ints, tuples and Optionals
        var kind = data.draw(integers(0, 4))
        if kind == 0:
            # an rvalue subject: the body can read the bindings
            var x = String("m", n)
            var out = String(
                indent, "match ", self.int_expr(data, 1), " & 7:\n"
            )
            out += String(
                indent,
                "case ",
                data.draw(integers(0, 7)),
                " | ",
                data.draw(integers(0, 7)),
                ":\n",
            )
            out += self.arm(data, inner, depth, [])
            out += String(
                indent, "case ", x, " if ", x, " > ", data.draw(integers(0, 7))
            )
            out += ":\n"
            out += self.arm(data, inner, depth, [x])
            out += String(indent, "case _:\n")
            out += self.arm(data, inner, depth, [])
            return out
        if kind == 1:
            # an lvalue subject that the arms may change
            var v = self.variable(data)
            var out = String(indent, "match ", v, ":\n")
            for _ in range(data.draw(integers(1, 3))):
                var lit = Self.pick(data, materialize[CONSTANTS]())
                if lit.startswith("(") or "." in lit:
                    lit = String(data.draw(integers(-3, 9)))
                out += String(indent, "case ", lit, ":\n")
                out += self.arm(data, inner, depth, [])
            out += String(indent, "case _:\n")
            out += self.arm(data, inner, depth, [])
            return out
        if kind == 2:
            var x = String("m", n)
            var y = String("u", n)
            var out = String(
                indent,
                "match (",
                self.int_expr(data, 1),
                " & 3, ",
                self.int_expr(data, 1),
                " & 1):\n",
            )
            out += String(indent, "case (0, 0) | (1, 1):\n")
            out += self.arm(data, inner, depth, [])
            out += String(indent, "case (2, ", y, ") | (", y, ", 0):\n")
            out += self.arm(data, inner, depth, [y])
            out += String(indent, "case (", x, ", ", y, ") if ", x, " > ", y)
            out += ":\n"
            out += self.arm(data, inner, depth, [x, y])
            out += String(indent, "case _:\n")
            out += self.arm(data, inner, depth, [])
            return out
        if kind == 3:
            var v = self.variable(data)
            var out = String(indent, "match opt:\n")
            out += String(
                indent,
                "case .Some(",
                bx,
                ") if ",
                bx,
                " < ",
                self.plain_expr(data, 1),
                ":\n",
                inner,
                v,
                " += ",
                bx,
                "\n",
            )
            out += String(
                indent, "case .Some(", bx, "):\n", inner, v, " ^= ", bx, "\n"
            )
            out += String(indent, "case .None:\n")
            out += self.arm(data, inner, depth, [])
            out += String(indent, "match ot:\n")
            out += String(
                indent,
                "case .Some(ref ",
                r,
                "):\n",
                inner,
                r,
                ".val += ",
                self.plain_expr(data, 0),
                "\n",
            )
            out += self.arm(data, inner, depth, [])
            out += String(indent, "case .None:\n")
            out += self.arm(data, inner, depth, [])
            return out
        # while case, bounded
        var g = String("g", n)
        return String(
            indent,
            "var ",
            g,
            " = 0\n",
            indent,
            "while case .Some(",
            bx,
            ") = opt:\n",
            inner,
            g,
            " += 1\n",
            inner,
            "if ",
            g,
            " > ",
            data.draw(integers(0, 4)),
            ":\n",
            inner,
            "    opt = None\n",
            inner,
            "else:\n",
            inner,
            "    opt = Optional[Int](",
            bx,
            " * 3 + ",
            self.plain_expr(data, 1),
            ")\n",
        )

    # ---- generics and closures

    def op_arg(
        mut self, mut data: ConjectureData, names: List[String]
    ) raises -> String:
        if len(names) > 0:
            return self.closure_expr(data, names, 2)
        return self.plain_expr(data, 2)

    def op_value(
        mut self, mut data: ConjectureData, depth: Int, names: List[String]
    ) raises -> Tuple[String, String]:
        """A value of a type that conforms to `Op`, as (type, expression).
        With `names` (in a closure), its Int arguments read only those."""
        var choice = data.draw(integers(0, 6 if depth < 2 else 3))
        if choice == 0:
            return (
                String("AddOp"),
                String("AddOp(", self.op_arg(data, names), ")"),
            )
        if choice == 1:
            return (
                String("MulOp"),
                String("MulOp(", self.op_arg(data, names), ")"),
            )
        if choice == 2:
            var t = String("ShiftOp[", data.draw(integers(1, 62)), "]")
            return (t, String(t, "()"))
        if choice == 3:
            if len(names) > 0:
                # closures don't capture the ledger here
                return (String("AddOp"), String("AddOp(1)"))
            return (
                String("TrackedOp"),
                String("TrackedOp(Tracked(", self.plain_expr(data, 2), ", L))"),
            )
        var a = self.op_value(data, depth + 1, names)
        if choice == 6:
            var t = String(
                "Repeat[", a[0], ", ", data.draw(integers(0, 3)), "]"
            )
            return (t, String(t, "(", a[1], ")"))
        var b = self.op_value(data, depth + 1, names)
        var t: String
        if choice == 4:
            t = String("Compose[", a[0], ", ", b[0], "]")
        else:
            var flag = "True" if data.draw(booleans()) else "False"
            t = String("Pick[", a[0], ", ", b[0], ", ", flag, "]")
        return (t, String(t, "(", a[1], ", ", b[1], ")"))

    def op_expr(mut self, mut data: ConjectureData) raises -> String:
        """An `Op` value, built directly or by its static `make`."""
        var op = self.op_value(data, 0, [])
        if data.draw(integers(0, 3)) == 0:
            return String(op[0], ".make(", self.plain_expr(data, 2), ", L)")
        return op[1]

    def generic_expr(
        mut self, mut data: ConjectureData, depth: Int
    ) raises -> String:
        """An Int expression that instantiates generic functions."""
        var kind = data.draw(integers(0, 7))
        if kind <= 2:
            var fs: List[String] = ["_gapply", "_gtwice", "_gcopy"]
            var f = fs[kind]
            return String(
                f,
                "(",
                self.op_expr(data),
                ", ",
                self.int_expr(data, depth),
                ")",
            )
        if kind == 3:
            var t = self.op_value(data, 0, [])[0]
            return String(
                "_gmake[",
                t,
                "](",
                self.int_expr(data, depth),
                ", ",
                self.int_expr(data, depth),
                ", L)",
            )
        if kind == 4:
            return String(self.op_value(data, 0, [])[0], ".K")
        if kind == 5:
            return String(
                "_gpick[Int](",
                self.condition(data, depth),
                ", ",
                self.int_expr(data, depth),
                ", ",
                self.int_expr(data, depth),
                ")",
            )
        if kind == 6:
            var k = data.draw(integers(0, N_NARROW - 1))
            return String(
                "Int(_gpick[",
                materialize[NARROW_TYPES]()[k],
                "](",
                self.condition(data, depth),
                ", ",
                self.narrow_expr(data, k, depth),
                ", ",
                self.narrow_expr(data, k, depth),
                "))",
            )
        if self.tracked_ok:
            if data.draw(booleans()):
                var pair = self.two_tracked(data)
                return String(
                    "_gpick[Tracked](",
                    self.condition(data, depth),
                    ", ",
                    pair[0],
                    ", ",
                    pair[1],
                    ").val",
                )
            return String(
                "len(_gdup(",
                Self.pick(data, self.tracked.copy()),
                ", ",
                self.int_expr(data, depth),
                "))",
            )
        return String("_gapply(", self.op_expr(data), ", 0)")

    def closure_expr(
        mut self, mut data: ConjectureData, names: List[String], depth: Int
    ) raises -> String:
        """An Int expression that reads only `names` (a closure's
        parameters and captures, or what a call may read beside one)."""
        var choice = data.draw(integers(0, 7 if depth < 3 else 1))
        var d = depth + 1
        if choice == 0:
            return Self.pick(data, names.copy())
        if choice == 1:
            return Self.pick(data, materialize[CONSTANTS]())
        if choice == 2:
            var op = Self.pick(data, ["+", "-", "*", "&", "|", "^"])
            return String(
                "(",
                self.closure_expr(data, names, d),
                " ",
                op,
                " ",
                self.closure_expr(data, names, d),
                ")",
            )
        if choice == 3:
            var f = Self.pick(data, ["_div", "_mod", "_min", "_max"])
            return String(
                f,
                "(",
                self.closure_expr(data, names, d),
                ", ",
                self.closure_expr(data, names, d),
                ")",
            )
        if choice == 4:
            var op = "<<" if data.draw(booleans()) else ">>"
            return String(
                "(",
                self.closure_expr(data, names, d),
                " ",
                op,
                " (",
                self.closure_expr(data, names, d),
                " & 63))",
            )
        if choice == 5:
            var cmp = Self.pick(data, ["<", "==", "!=", ">="])
            return String(
                "(",
                self.closure_expr(data, names, d),
                " if (",
                self.closure_expr(data, names, d),
                " ",
                cmp,
                " ",
                self.closure_expr(data, names, d),
                ") else ",
                self.closure_expr(data, names, d),
                ")",
            )
        if choice == 6:
            return Self.pick(data, names.copy())
        var f = Self.pick(data, ["_gapply", "_gtwice", "_gcopy"])
        var op = self.op_value(data, 1, names)
        return String(
            f, "(", op[1], ", ", self.closure_expr(data, names, d), ")"
        )

    def generic_statement(
        mut self,
        mut data: ConjectureData,
        choice: Int,
        indent: String,
        depth: Int,
    ) raises -> String:
        if choice == 43:
            var kind = data.draw(integers(0, 2))
            if kind == 0:
                var pair = self.two_tracked(data)
                return String(indent, "_gswap(", pair[0], ", ", pair[1], ")\n")
            if kind == 1:
                var i = data.draw(integers(0, N_VARIABLES - 1))
                var j = (
                    i + data.draw(integers(1, N_VARIABLES - 1))
                ) % N_VARIABLES
                return String(indent, "_gswap(v", i, ", v", j, ")\n")
            var pair = self.two_tracked(data)
            return String(
                indent,
                Self.pick(data, self.tracked.copy()),
                " = _gpick[Tracked](",
                self.condition(data, 1),
                ", ",
                pair[0],
                ", ",
                pair[1],
                ")\n",
            )
        if choice == 44:
            var call = String(
                self.variable(data),
                " += _graise(",
                self.op_expr(data),
                ", ",
                self.plain_expr(data, 1),
                ", L)\n",
            )
            if self.try_depth > 0:
                return String(indent, call)
            return String(
                indent,
                "try:\n",
                indent,
                "    ",
                call,
                indent,
                "except:\n",
                indent,
                "    ",
                self.variable(data),
                " -= 1\n",
            )
        if choice == 45:
            # an Op in a local, used several times
            var name = String("g", self.guards)
            self.guards += 1
            var s = String(
                indent, "var ", name, " = ", self.op_expr(data), "\n"
            )
            for _ in range(data.draw(integers(1, 3))):
                var use = data.draw(integers(0, 3))
                var e = self.plain_expr(data, 1)
                var call: String
                if use == 0:
                    call = String("_gapply(", name, ", ", e, ")")
                elif use == 1:
                    call = String(name, ".twice(", e, ")")
                elif use == 2:
                    call = String("type_of(", name, ").K")
                else:
                    call = String("_gcopy(", name, ", ", e, ")")
                s += String(indent, self.variable(data), " ^= ", call, "\n")
            return s
        return self.closure_statement(data, indent, depth)

    def closure_statement(
        mut self,
        mut data: ConjectureData,
        indent: String,
        depth: Int,
        forced_mode: Int = -1,
    ) raises -> String:
        """A closure with a generated capture list and body, passed to
        generic higher-order functions or called directly."""
        var inner = indent + "    "
        var mode = forced_mode if forced_mode >= 0 else data.draw(
            integers(0, 3)
        )
        # 0, 1: an explicit capture list; 2: {var^}, which moves every
        # captured value into the closure; 3: an explicit list, raising
        if mode == 3 and self.try_depth == 0:
            self.try_depth += 1
            var body = self.closure_statement(data, inner, depth, 3)
            self.try_depth -= 1
            return String(
                indent,
                "try:\n",
                body,
                indent,
                "except:\n",
                inner,
                self.variable(data),
                " += 1\n",
            )
        var name = String("h", self.guards)
        self.guards += 1
        var result = self.variable(data)
        var transfer_all = mode == 2
        var raising = mode == 3
        var param = 0 if raising else data.draw(integers(0, 3))
        # 0, 1: (x: Int); 2: (t: Tracked) for _hsum; 3: (i: Int, t: Tracked)
        var captures = List[String]()
        var reads = List[String]()
        var mut_ints = List[String]()
        var mut_tracked = List[String]()
        var moved = List[String]()
        var moved_tracked = List[String]()
        # names that a call beside the closure must not read
        var mutated = List[String]()
        var copyable = transfer_all
        # half the {var^} closures capture only Ints, which keeps them
        # copyable (a Tracked capture doesn't: see
        # unfiled-mojo-issue-var-caret-copyable.md)
        var ints_only = transfer_all and data.draw(booleans())
        var signature: String
        if param <= 1:
            signature = "(x: Int)"
            reads.append("x")
        elif param == 2:
            signature = "(t: Tracked)"
            reads.append("t.val")
        else:
            signature = "(i: Int, t: Tracked)"
            reads.append("i")
            reads.append("t.val")
        for i in range(N_VARIABLES):
            var v = String("v", i)
            if v == result:
                continue
            var how = data.draw(integers(0, 4))
            if how <= 1:
                continue
            reads.append(v)
            if transfer_all:
                moved.append(v)
            elif how == 2:
                captures.append(String("imm ", v))
            elif how == 3:
                captures.append(String("mut ", v))
                mut_ints.append(v)
                mutated.append(v)
            else:
                captures.append(String("var ", v))
        if not transfer_all:
            var args: List[String] = ["a", "b", "c"]
            for v in args:
                if data.draw(integers(0, 3)) == 0:
                    captures.append(String("imm ", v))
                    reads.append(v)
            for v in self.loop_variables:
                if data.draw(booleans()):
                    captures.append(String("imm ", v))
                    reads.append(v)
        for t in self.tracked:
            if "." in t or ints_only:
                continue
            var how = data.draw(integers(0, 6))
            if how <= 2:
                continue
            reads.append(String(t, ".val"))
            if transfer_all:
                moved.append(t)
                moved_tracked.append(t)
            elif how == 3 or how == 4:
                captures.append(String("imm ", t))
            elif how == 5:
                captures.append(String("mut ", t))
                mut_tracked.append(t)
                mutated.append(t)
            else:
                captures.append(String("var ", t, "^"))
                moved.append(t)
                moved_tracked.append(t)
        var ledger = len(mut_tracked) > 0 and data.draw(booleans())
        if ledger:
            captures.append("imm L")
        var capture_list: String
        if transfer_all:
            capture_list = "{var^}"
        else:
            capture_list = "{"
            for i in range(len(captures)):
                if i > 0:
                    capture_list += ", "
                capture_list += captures[i]
            capture_list += "}"
        var s = String(
            indent,
            "def ",
            name,
            signature,
            " raises " if raising else " ",
            capture_list,
            " -> Int:\n",
        )
        for m in mut_ints:
            var op = Self.pick(data, ["=", "+=", "^=", "*="])
            s += String(
                inner, m, " ", op, " ", self.closure_expr(data, reads, 1), "\n"
            )
        for t in mut_tracked:
            if ledger and data.draw(booleans()):
                s += String(
                    inner,
                    t,
                    " = Tracked(",
                    self.closure_expr(data, reads, 1),
                    ", L)\n",
                )
            else:
                s += String(
                    inner,
                    t,
                    ".val += ",
                    self.closure_expr(data, reads, 1),
                    "\n",
                )
        if raising:
            s += String(
                inner,
                "if (",
                self.closure_expr(data, reads, 1),
                " & 3) == 0:\n",
                inner,
                '    raise Error("k")\n',
            )
        if param <= 1 and not transfer_all and data.draw(integers(0, 2)) == 0:
            # a nested closure over the parameter and the mutable captures
            var nested = String(name, "_in")
            var nested_captures = String("{imm x")
            var nested_reads: List[String] = ["y", "x"]
            for m in mut_ints:
                nested_captures += String(", mut ", m)
                nested_reads.append(m)
            nested_captures += "}"
            s += String(
                inner,
                "def ",
                nested,
                "(y: Int) ",
                nested_captures,
                " -> Int:\n",
            )
            for m in mut_ints:
                s += String(inner, "    ", m, " += y\n")
            s += String(
                inner,
                "    return ",
                self.closure_expr(data, nested_reads, 1),
                "\n",
                inner,
                "return _hiter(",
                nested,
                ", x, ",
                self.closure_expr(data, reads, 1),
                ")\n",
            )
        else:
            s += String(
                inner, "return ", self.closure_expr(data, reads, 0), "\n"
            )
        # {var^} captures only what the body uses
        for t in moved_tracked:
            if transfer_all and String(t, ".val") in s:
                copyable = False
        # the moved-from variables are reinitialized at once
        for v in moved:
            var value = Self.pick(data, materialize[CONSTANTS]())
            if v in moved_tracked:
                s += String(indent, v, " = Tracked(", value, ", L)\n")
            else:
                s += String(indent, v, " = ", value, "\n")
        # what the calls may read
        var outside: List[String] = ["a", "b", "c"]
        outside += self.loop_variables.copy()
        for i in range(N_VARIABLES):
            var v = String("v", i)
            if v != result and v not in mutated:
                outside.append(v)
        for t in self.tracked:
            if t not in mutated and "." not in t:
                outside.append(String(t, ".val"))
        for n_call in range(data.draw(integers(1, 2))):
            var arg = self.closure_expr(data, outside, 1)
            var call: String
            if raising:
                if data.draw(booleans()):
                    call = String("_hraise(", name, ", ", arg, ")")
                else:
                    call = String(name, "(", arg, ")")
            elif param == 2:
                var elems = String("Tracked(", arg, ", L)")
                var plain = List[String]()
                for t in self.tracked:
                    if t not in mutated:
                        plain.append(t)
                if len(plain) > 0 and data.draw(booleans()):
                    elems = String(Self.pick(data, plain^), ".copy(), ", elems)
                call = String(
                    "_hsum(ListHolder[Tracked]([", elems, "]), ", name, ")"
                )
            elif param == 3:
                call = String("_hlist(", name, ", lst)")
            else:
                var kind = data.draw(integers(0, 5))
                if copyable and (n_call == 0 or data.draw(booleans())):
                    call = String("_hcall(_hcopy(", name, "), ", arg, ")")
                elif kind == 1:
                    call = String(
                        "_hiter(",
                        name,
                        ", ",
                        self.closure_expr(data, outside, 2),
                        ", ",
                        arg,
                        ")",
                    )
                elif kind == 2 and len(mut_ints) + len(mut_tracked) == 0:
                    # twice: aliasing if it captures anything mutably
                    call = String("_hcomp(", name, ", ", name, ", ", arg, ")")
                elif kind == 3:
                    call = String(name, "(", arg, ")")
                elif kind == 4:
                    call = String(
                        "_hsum(IntHolder(",
                        arg,
                        ", ",
                        self.closure_expr(data, outside, 2),
                        "), ",
                        name,
                        ")",
                    )
                else:
                    call = String("_hcall(", name, ", ", arg, ")")
            var op = Self.pick(data, ["=", "+=", "^="])
            s += String(indent, result, " ", op, " ", call, "\n")
        return s

    @staticmethod
    def checksum() -> String:
        return (
            "_mix(v0, v1, v2, v3, buf, opt, pool, q0, q1, t0, t1, lst, ot)"
            " * 31 + _nmix(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10)"
            " * 31 + _pmix(pr, cells)"
            " * 31 + _cmix(d, st, vr, en)"
            " * 31 + _vmix(s0, s1, s2, s3, s4, s5)"
        )

    def function(mut self, mut data: ConjectureData) raises -> String:
        var s = String(
            "def f",
            self.function_index,
            "(a: Int, b: Int, c: Int, L: LedgerPtr) -> Int:\n",
        )
        s += "    var v0 = a\n    var v1 = b\n    var v2 = c\n    var v3 = 0\n"
        s += String("    var buf = Array[Int, ", BUFFER_SIZE, "](fill=0)\n")
        s += "    var p = buf.unsafe_ptr()\n"
        s += "    var opt = Optional[Int](None)\n"
        s += "    var pool = Pool()\n"
        s += "    var q0: Optional[NodePtr] = None\n"
        s += "    var q1: Optional[NodePtr] = None\n"
        s += "    var t0 = Tracked(a, L)\n"
        s += "    var t1 = Tracked(b, L)\n"
        s += "    var lst = List[Tracked]()\n"
        s += "    var ot = Optional[Tracked](None)\n"
        s += "    var pr = Pair(Tracked(c, L), Tracked(a, L))\n"
        s += "    var cells = Cells(b, c, L)\n"
        s += "    var d = Dict[Int, Tracked]()\n"
        s += "    var st = Set[Int]()\n"
        s += "    var vr = TV(Int(c))\n"
        s += "    var en: Tok = .num(b)\n"
        var types = materialize[NARROW_TYPES]()
        for k in range(len(types)):
            s += String(
                "    var n",
                k,
                " = ",
                types[k],
                "(",
                ["a", "b", "c"][k % 3],
                ")\n",
            )
        for k in range(N_VEC):
            s += String(
                "    var s",
                k,
                " = _ramp[DType.",
                materialize[VEC_DTYPES]()[k],
                ", ",
                materialize[VEC_LANES]()[k],
                "](",
                ["a", "b", "c"][(k + 1) % 3],
                ")\n",
            )
        s += self.block(data, "    ", 0)
        s += String("    return ", Self.checksum(), "\n\n\n")
        # every Tracked value made during the call must be destroyed by
        # the time it returns
        var i = self.function_index
        s += String("def run_f", i, "(a: Int, b: Int, c: Int) -> Int:\n")
        s += "    var ledger = Ledger()\n"
        s += String("    var r = f", i, "(a, b, c, ledger.counts)\n")
        s += String(
            "    _check_balance(", i, ", ledger.counts[unsafe_offset=0])\n"
        )
        s += "    return r * 31 + ledger.summary()\n"
        return s


comptime PRELUDE = """from std.benchmark import black_box
from std.bit import (
    pop_count, count_leading_zeros, count_trailing_zeros, byte_swap,
    bit_reverse, rotate_bits_left, rotate_bits_right,
)
from std.collections import Set
from std.memory import Pointer
from std.memory.alloc import unsafe_alloc
from std.utils import Variant


@always_inline
def _cond(c: Bool) -> Bool:
    return c


@always_inline
def _div(a: Int, b: Int) -> Int:
    return (0 - a) if b == -1 else a // b


@always_inline
def _mod(a: Int, b: Int) -> Int:
    return 0 if b == -1 else a % b


@always_inline
def _ndiv[dt: DType](a: Scalar[dt], b: Scalar[dt]) -> Scalar[dt]:
    comptime if dt.is_signed():
        if b == -1:
            return 0 - a
    return a // b


@always_inline
def _nmod[dt: DType](a: Scalar[dt], b: Scalar[dt]) -> Scalar[dt]:
    comptime if dt.is_signed():
        if b == -1:
            return 0
    return a % b


@always_inline
def _nmix(
    n0: Int8, n1: UInt8, n2: Int16, n3: UInt16, n4: Int32, n5: UInt32,
    n6: UInt64, n7: Int128, n8: UInt128, n9: Int256, n10: UInt256,
) -> Int:
    var h = Int(n0) * 31 + Int(n1)
    h = h * 31 + Int(n2)
    h = h * 31 + Int(n3)
    h = h * 31 + Int(n4)
    h = h * 31 + Int(n5)
    h = h * 31 + Int(n6)
    h = h * 31 + Int(n7) + Int(n7 >> 64)
    h = h * 31 + Int(n8) + Int(n8 >> 64)
    for i in range(4):
        h = h * 31 + Int(n9 >> Int256(64 * i)) + Int(n10 >> UInt256(64 * i))
    return h


comptime V0 = SIMD[DType.int32, 4]
comptime V1 = SIMD[DType.uint16, 4]
comptime V2 = SIMD[DType.int16, 8]
comptime V3 = SIMD[DType.uint32, 8]
comptime V4 = SIMD[DType.uint8, 16]
comptime V5 = SIMD[DType.int64, 2]


@always_inline
def _vdiv[
    dt: DType, n: SIMDLength
](a: SIMD[dt, n], b: SIMD[dt, n]) -> SIMD[dt, n]:
    comptime if dt.is_signed():
        var m = b.eq(SIMD[dt, n](-1))
        return m.select(SIMD[dt, n](0) - a, a // m.select(SIMD[dt, n](1), b))
    return a // b


@always_inline
def _vmod[
    dt: DType, n: SIMDLength
](a: SIMD[dt, n], b: SIMD[dt, n]) -> SIMD[dt, n]:
    comptime if dt.is_signed():
        var m = b.eq(SIMD[dt, n](-1))
        return m.select(SIMD[dt, n](0), a % m.select(SIMD[dt, n](1), b))
    return a % b


def _ramp[dt: DType, n: SIMDLength](x: Int) -> SIMD[dt, n]:
    var r = SIMD[dt, n](0)
    for i in range(Int(n)):
        r[i] = Scalar[dt](x + i * i * 7 - i)
    return r


@always_inline
def _vset[
    dt: DType, n: SIMDLength
](var v: SIMD[dt, n], i: Int, s: Scalar[dt]) -> SIMD[dt, n]:
    v[i] = s
    return v


def _vhash[dt: DType, n: SIMDLength](v: SIMD[dt, n]) -> Int:
    var h = 0
    for i in range(Int(n)):
        h = h * 31 + Int(v[i])
    return h


def _vmix(s0: V0, s1: V1, s2: V2, s3: V3, s4: V4, s5: V5) -> Int:
    var h = _vhash(s0) * 31 + _vhash(s1)
    h = h * 31 + _vhash(s2)
    h = h * 31 + _vhash(s3)
    h = h * 31 + _vhash(s4)
    return h * 31 + _vhash(s5)


FILE_SPECIFIC_HELPERS
comptime NodePtr = Pointer[Node, MutUntrackedOrigin]


struct Node(Movable):
    var val: Int
    var next: Optional[NodePtr]
    var prev: Optional[NodePtr]

    def __init__(out self, val: Int):
        self.val = val
        self.next = None
        self.prev = None


struct Pool(Movable):
    var base: NodePtr

    def __init__(out self):
        self.base = unsafe_alloc[Node](4)
        for i in range(4):
            self.base.unsafe_offset(i).unsafe_write(Node(i))

    def __deinit__(deinit self):
        self.base.unsafe_free()

    @always_inline
    def at(self, i: Int) -> NodePtr:
        return self.base.unsafe_offset(i & 3)

    def index(self, p: Optional[NodePtr]) -> Int:
        if p:
            for i in range(4):
                if p.value() == self.at(i):
                    return i
        return -1


comptime LedgerPtr = Pointer[Int, MutUntrackedOrigin]


struct Tracked(Copyable):
    # Counts itself in a ledger: [0] live values, [1] made, [2] a hash of
    # the destruction order, [3] copies. The value lives in a heap cell of
    # its own, freed by __deinit__, so that under AddressSanitizer any use
    # of a destroyed Tracked is a heap-use-after-free.

    var cell: LedgerPtr
    var ledger: LedgerPtr

    def __init__(out self, val: Int, ledger: LedgerPtr):
        self.cell = unsafe_alloc[Int](1)
        self.cell[unsafe_offset=0] = val
        self.ledger = ledger
        ledger[unsafe_offset=0] += 1
        ledger[unsafe_offset=1] += 1

    def __init__(out self, *, copy: Self):
        self.cell = unsafe_alloc[Int](1)
        self.cell[unsafe_offset=0] = copy.cell[unsafe_offset=0]
        self.ledger = copy.ledger
        self.ledger[unsafe_offset=0] += 1
        self.ledger[unsafe_offset=3] += 1

    def __deinit__(deinit self):
        self.ledger[unsafe_offset=0] -= 1
        self.ledger[unsafe_offset=2] = (
            self.ledger[unsafe_offset=2] * 31 + self.cell[unsafe_offset=0]
        )
        self.cell.unsafe_free()

    @always_inline
    def __getattr__(ref self, name: StaticString) -> ref[self] Int:
        # `t.val`, a reference into the cell that keeps `t` alive
        return self.cell.unsafe_mut_cast[origin_of(self).mut]().unsafe_origin_cast[
            origin_of(self)
        ]()[]


struct Ledger(Movable):
    var counts: LedgerPtr

    def __init__(out self):
        self.counts = unsafe_alloc[Int](4)
        for i in range(4):
            self.counts[unsafe_offset=i] = 0

    def __deinit__(deinit self):
        self.counts.unsafe_free()

    def summary(self) -> Int:
        var h = 0
        for i in range(4):
            h = h * 1000003 + self.counts[unsafe_offset=i]
        return h


comptime CellPtr = Pointer[Tracked, MutUntrackedOrigin]


struct Cells(Movable):
    # Two tracked values on the heap, managed by hand.
    var ptr: CellPtr

    def __init__(out self, a: Int, b: Int, L: LedgerPtr):
        self.ptr = unsafe_alloc[Tracked](2)
        self.ptr.unsafe_write(Tracked(a, L))
        self.ptr.unsafe_offset(1).unsafe_write(Tracked(b, L))

    def __deinit__(deinit self):
        self.ptr.unsafe_deinit_pointee()
        self.ptr.unsafe_offset(1).unsafe_deinit_pointee()
        self.ptr.unsafe_free()

    @always_inline
    def at(self, i: Int) -> CellPtr:
        return self.ptr.unsafe_offset(i & 1)


struct Pair(Copyable):
    var x: Tracked
    var y: Tracked

    def __init__(out self, var x: Tracked, var y: Tracked):
        self.x = x^
        self.y = y^


def _pmix(pr: Pair, cells: Cells) -> Int:
    var h = pr.x.val * 31 + pr.y.val
    return (h * 31 + cells.at(0)[].val) * 31 + cells.at(1)[].val


__enum Tok(Copyable):
    case empty
    case num(Int)
    case two(Int, Int)
    case tr(Tracked)
    case both(Int, Tracked)


comptime TV = Variant[Int, Tracked]


def _tmix(t: Tok) -> Int:
    match t:
        case .empty:
            return -3
        case .num(x):
            return x
        case .two(x, y):
            return x * 7 + y
        case .tr(r):
            return r.val * 11
        case .both(x, r):
            return x * 13 + r.val


def _varmix(v: TV) -> Int:
    if v.isa[Int]():
        return v[Int]
    return v[Tracked].val * 3 + 1


def _cmix(d: Dict[Int, Tracked], st: Set[Int], v: TV, t: Tok) -> Int:
    var h = len(d)
    for e in d.items():
        h = (h * 31 + e.key) * 31 + e.value.val
    h = h * 31 + len(st)
    for k in st:
        h = h * 31 + k
    return (h * 31 + _varmix(v)) * 31 + _tmix(t)


@always_inline
def _elem(ref arr: Array[Int, 8], i: Int) -> ref[arr] Int:
    return arr[i & 7]


@always_inline
def _pick(c: Bool, mut x: Tracked, mut y: Tracked) -> ref[x, y] Tracked:
    if c:
        return x
    return y


def _consume(var t: Tracked) -> Int:
    return t.val


def _bump(mut t: Tracked, x: Int):
    t.val += x


def _sum(lst: List[Tracked]) -> Int:
    var h = 0
    for i in range(len(lst)):
        h = h * 7 + lst[i].val
    return h


@always_inline
def _mix(
    v0: Int, v1: Int, v2: Int, v3: Int, buf: Array[Int, 8], opt: Optional[Int],
    pool: Pool, q0: Optional[NodePtr], q1: Optional[NodePtr],
    t0: Tracked, t1: Tracked, lst: List[Tracked], ot: Optional[Tracked],
) -> Int:
    var h = v0 * 31 + v1
    h = h * 31 + v2
    h = h * 31 + v3
    for i in range(8):
        h = h * 31 + buf[i]
    h = h * 31 + opt.or_else(-17)
    for i in range(4):
        h = h * 31 + pool.at(i)[].val
        h = h * 31 + pool.index(pool.at(i)[].next)
        h = h * 31 + pool.index(pool.at(i)[].prev)
    h = h * 31 + pool.index(q0)
    h = h * 31 + pool.index(q1)
    h = h * 31 + t0.val
    h = h * 31 + t1.val
    h = h * 31 + len(lst)
    h = h * 31 + _sum(lst)
    return h * 31 + (ot.value().val if ot else -5)


# ---- generics: a trait with an associated constant, a default method
# and a static constructor; generic structs over it (value parameters,
# comptime if, comptime for); a trait with an associated type


trait Op(Copyable, Deinitable):
    comptime K: Int

    def apply(self, x: Int) -> Int:
        ...

    def twice(self, x: Int) -> Int:
        return self.apply(self.apply(x))

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        ...


struct AddOp(Op):
    comptime K = 3
    var k: Int

    def __init__(out self, k: Int):
        self.k = k

    def apply(self, x: Int) -> Int:
        return x + self.k

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return AddOp(seed * 7)


struct MulOp(Op):
    comptime K = 5
    var k: Int

    def __init__(out self, k: Int):
        self.k = k

    def apply(self, x: Int) -> Int:
        return x * (self.k | 1)

    def twice(self, x: Int) -> Int:
        return x * (self.k | 1) * (self.k | 1) + 1

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return MulOp(seed ^ 0x55)


struct ShiftOp[s: Int](Op):
    comptime K = Self.s * 2 + 1

    def __init__(out self):
        pass

    def apply(self, x: Int) -> Int:
        return x ^ (x >> Self.s) ^ (x << (63 - Self.s))

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return ShiftOp[Self.s]()


struct TrackedOp(Op):
    comptime K = 7
    var t: Tracked

    def __init__(out self, var t: Tracked):
        self.t = t^

    def apply(self, x: Int) -> Int:
        return x * 3 + self.t.val

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return TrackedOp(Tracked(seed, L))


struct Compose[A: Op, B: Op](Op):
    comptime K = Self.A.K * 31 + Self.B.K
    var a: Self.A
    var b: Self.B

    def __init__(out self, var a: Self.A, var b: Self.B):
        self.a = a^
        self.b = b^

    def apply(self, x: Int) -> Int:
        return self.b.apply(self.a.apply(x))

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return Compose(Self.A.make(seed, L), Self.B.make(seed + 1, L))


struct Pick[A: Op, B: Op, flag: Bool](Op):
    comptime K = Self.A.K if Self.flag else Self.B.K
    var a: Self.A
    var b: Self.B

    def __init__(out self, var a: Self.A, var b: Self.B):
        self.a = a^
        self.b = b^

    def apply(self, x: Int) -> Int:
        comptime if Self.flag:
            return self.a.twice(x)
        else:
            return self.b.apply(x) - 1

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return Pick[Self.A, Self.B, Self.flag](
            Self.A.make(seed * 3, L), Self.B.make(seed - 2, L)
        )


struct Repeat[A: Op, n: Int](Op):
    comptime K = Self.A.K * Self.n
    var a: Self.A

    def __init__(out self, var a: Self.A):
        self.a = a^

    def apply(self, x: Int) -> Int:
        var r = x
        comptime for i in range(Self.n):
            r = self.a.apply(r) + i
        return r

    @staticmethod
    def make(seed: Int, L: LedgerPtr) -> Self:
        return Repeat[Self.A, Self.n](Self.A.make(seed, L))


def _gapply[T: Op](op: T, x: Int) -> Int:
    return op.apply(x) * 31 + T.K


def _gtwice[T: Op](op: T, x: Int) -> Int:
    return op.twice(x)


def _gmake[T: Op](seed: Int, x: Int, L: LedgerPtr) -> Int:
    return T.make(seed, L).apply(x)


def _gcopy[T: Op](op: T, x: Int) -> Int:
    var c = op.copy()
    var lst: List[T] = [op.copy(), c^]
    return lst[0].apply(x) ^ lst[1].twice(x)


def _graise[T: Op](op: T, x: Int, L: LedgerPtr) raises -> Int:
    var t = Tracked(x, L)
    var r = op.apply(x)
    if (r & 3) == 0:
        raise Error("g")
    return r + t.val


def _gpick[T: Copyable](c: Bool, a: T, b: T) -> T:
    return a.copy() if c else b.copy()


def _gswap[T: Movable](mut a: T, mut b: T):
    swap(a, b)


def _gdup[T: Copyable & Deinitable](x: T, n: Int) -> List[T]:
    var out = List[T]()
    for _ in range(n & 3):
        out.append(x.copy())
    return out^


trait Holder:
    comptime Item: Copyable & Deinitable

    def size(self) -> Int:
        ...

    def get(self, i: Int) -> Self.Item:
        ...


struct IntHolder(Holder):
    comptime Item = Int
    var xs: List[Int]

    def __init__(out self, a: Int, b: Int):
        self.xs = [a, b, a ^ b]

    def size(self) -> Int:
        return len(self.xs)

    def get(self, i: Int) -> Int:
        return self.xs[i]


struct ListHolder[T: Copyable & Deinitable](Holder):
    comptime Item = Self.T
    var xs: List[Self.T]

    def __init__(out self, var xs: List[Self.T]):
        self.xs = xs^

    def size(self) -> Int:
        return len(self.xs)

    def get(self, i: Int) -> Self.T:
        return self.xs[i].copy()


# ---- higher-order functions over closure types


def _hcall[F: def(Int) -> Int](f: F, x: Int) -> Int:
    return f(x)


def _hiter[F: def(Int) -> Int](f: F, n: Int, x: Int) -> Int:
    var r = x
    for _ in range(n & 7):
        r = f(r)
    return r


def _hcomp[F: def(Int) -> Int, G: def(Int) -> Int](f: F, g: G, x: Int) -> Int:
    return g(f(x)) * 3 + f(g(x))


def _hraise[F: def(Int) raises -> Int](f: F, x: Int) raises -> Int:
    return f(x) + f(x + 1)


def _hlist[F: def(Int, Tracked) -> Int](f: F, lst: List[Tracked]) -> Int:
    var h = 0
    for i in range(len(lst)):
        h = h * 7 + f(i, lst[i])
    return h


def _hsum[H: Holder, F: def(H.Item) -> Int](h: H, f: F) -> Int:
    var r = 0
    for i in range(h.size()):
        r = r * 7 + f(h.get(i))
    return r


def _hcopy[F: Copyable](f: F) -> F:
    # not f.copy(): https://github.com/modular/modular/issues/7554
    return F(copy=f)


"""


comptime RUN_TIME_HELPERS = """@always_inline
def _min(a: Int, b: Int) -> Int:
    return min(a, b)


@always_inline
def _max(a: Int, b: Int) -> Int:
    return max(a, b)


def _check_balance(f: Int, live: Int):
    if live != 0:
        print("UNBALANCED", f, live)


def _insert(mut lst: List[Tracked], i: Int, var t: Tracked):
    lst.insert((i & 1023) % (len(lst) + 1), t^)


def _pop_at(mut lst: List[Tracked], i: Int) -> Tracked:
    return lst.pop((i & 1023) % len(lst))


@always_inline
def _rotl[dt: DType, n: SIMDLength, //, s: Int](v: SIMD[dt, n]) -> SIMD[dt, n]:
    return v.rotate_left[s]()


@always_inline
def _rotr[dt: DType, n: SIMDLength, //, s: Int](v: SIMD[dt, n]) -> SIMD[dt, n]:
    return v.rotate_right[s]()


@always_inline
def _lshift[
    dt: DType, n: SIMDLength, //, s: Int
](v: SIMD[dt, n]) -> SIMD[dt, n]:
    return v.shift_left[s]()


@always_inline
def _rshift[
    dt: DType, n: SIMDLength, //, s: Int
](v: SIMD[dt, n]) -> SIMD[dt, n]:
    return v.shift_right[s]()


@always_inline
def _vinsert[
    dt: DType, n: SIMDLength, m: SIMDLength, //, offset: Int
](x: SIMD[dt, n], y: SIMD[dt, m]) -> SIMD[dt, n]:
    return x.insert[offset=offset](y)


@always_inline
def _vdeint[
    dt: DType, n: SIMDLength, //, which: Int
](x: SIMD[dt, n], y: SIMD[dt, n]) -> SIMD[dt, n]:
    return rebind[SIMD[dt, n]](x.join(y).deinterleave()[which])


"""
# Compile time can't evaluate min/max of a small and a large Int
# (unfiled-mojo-issue-comptime-index-min-max.md), so comptime.mojo
# defines them without pop.min/pop.max.
comptime COMPILE_TIME_HELPERS = """def _min(a: Int, b: Int) -> Int:
    return a if a < b else b


def _max(a: Int, b: Int) -> Int:
    return b if a < b else a


def _check_balance(f: Int, live: Int):
    pass  # the live count is part of run_fN's result


# At compile time, List.insert and List.pop(i) on Tracked values fail
# ("write clobbers a pointer region"; unsafe_memmove copies bytes, see
# unfiled-mojo-issue-comptime-memmove.md), so these move by swaps.
def _insert(mut lst: List[Tracked], i: Int, var t: Tracked):
    var k = (i & 1023) % (len(lst) + 1)
    lst.append(t^)
    var j = len(lst) - 1
    while j > k:
        lst.swap_elements(j, j - 1)
        j -= 1


def _pop_at(mut lst: List[Tracked], i: Int) -> Tracked:
    var k = (i & 1023) % len(lst)
    for j in range(k, len(lst) - 1):
        lst.swap_elements(j, j + 1)
    return lst.pop()


# Lane loops for the operations that are LLVM intrinsics, which compile
# time can't evaluate


def _rotl[dt: DType, n: SIMDLength, //, s: Int](v: SIMD[dt, n]) -> SIMD[dt, n]:
    var r = v
    for i in range(Int(n)):
        r[i] = v[(i + s + Int(n)) % Int(n)]
    return r


def _rotr[dt: DType, n: SIMDLength, //, s: Int](v: SIMD[dt, n]) -> SIMD[dt, n]:
    var r = v
    for i in range(Int(n)):
        r[i] = v[(i - s + Int(n)) % Int(n)]
    return r


def _lshift[
    dt: DType, n: SIMDLength, //, s: Int
](v: SIMD[dt, n]) -> SIMD[dt, n]:
    var r = SIMD[dt, n](0)
    for i in range(Int(n) - s):
        r[i] = v[i + s]
    return r


def _rshift[
    dt: DType, n: SIMDLength, //, s: Int
](v: SIMD[dt, n]) -> SIMD[dt, n]:
    var r = SIMD[dt, n](0)
    for i in range(s, Int(n)):
        r[i] = v[i - s]
    return r


def _vinsert[
    dt: DType, n: SIMDLength, m: SIMDLength, //, offset: Int
](x: SIMD[dt, n], y: SIMD[dt, m]) -> SIMD[dt, n]:
    var r = x
    for j in range(Int(m)):
        r[offset + j] = y[j]
    return r


def _vdeint[
    dt: DType, n: SIMDLength, //, which: Int
](x: SIMD[dt, n], y: SIMD[dt, n]) -> SIMD[dt, n]:
    var r = x
    for i in range(Int(n)):
        var j = 2 * i + which
        r[i] = x[j] if j < Int(n) else y[j - Int(n)]
    return r


"""


def draw_program(mut data: ConjectureData) raises -> Tuple[String, String]:
    """Returns the program and its compile-time twin."""
    var n_functions = data.draw(integers(1, 6))
    var functions = String(PRELUDE)
    for i in range(n_functions):
        var generator = ProgramGenerator(i)
        functions += generator.function(data)
        functions += "\n\n"
    var arg_lists = List[String]()
    for _ in range(data.draw(integers(1, 3))):
        var args = String()
        for j in range(3):
            if j > 0:
                args += ", "
            if data.draw(booleans()):
                args += ProgramGenerator.pick(data, materialize[CONSTANTS]())
            else:
                args += String(data.draw(integers(-20, 20)))
        arg_lists.append(args)

    var program = String(
        functions.replace("FILE_SPECIFIC_HELPERS\n", RUN_TIME_HELPERS),
        "def main():\n",
    )
    var comptime_program = String(
        functions.replace("FILE_SPECIFIC_HELPERS\n", COMPILE_TIME_HELPERS),
        "def main():\n",
    )
    for i in range(n_functions):
        for j in range(len(arg_lists)):
            ref args = arg_lists[j]
            # constant arguments, which -O3 can propagate, and opaque ones
            var hidden = args.replace(", ", "), black_box(")
            program += String(
                '    print("c", ', i, ", run_f", i, "(", args, "))\n"
            )
            program += String(
                '    print("b", ',
                i,
                ", run_f",
                i,
                "(black_box(",
                hidden,
                ")))\n",
            )
            var name = String("k", i, "_", j)
            comptime_program += String(
                "    comptime ", name, " = run_f", i, "(", args, ")\n"
            )
            comptime_program += String('    print("c", ', i, ", ", name, ")\n")
    return (program^, comptime_program^)


def main() raises:
    var work_dir = (
        String(argv()[1]) if len(argv()) > 1 else "build/compiler_fuzz_work"
    )
    var script = (
        String(argv()[2]) if len(argv())
        > 2 else "examples/compiler_fuzz/build_and_compare.sh"
    )
    _ = run(String("mkdir -p ", work_dir))

    def differential(
        mut data: ConjectureData,
    ) raises {imm work_dir, imm script}:
        var programs = draw_program(data)
        with open(String(work_dir, "/program.mojo"), "w") as f:
            f.write(programs[0])
        with open(String(work_dir, "/comptime.mojo"), "w") as f:
            f.write(programs[1])
        var verdict = run(String("bash ", script, " ", work_dir, " 2>&1"))
        if not verdict.startswith("OK"):
            data.note(programs[0])
            data.note(verdict)
            _ = run(
                String(
                    "cp ",
                    work_dir,
                    "/program.mojo ",
                    work_dir,
                    "/failing_program.mojo",
                )
            )
            _ = run(
                String(
                    "cp ",
                    work_dir,
                    "/comptime.mojo ",
                    work_dir,
                    "/failing_comptime.mojo",
                )
            )
            # BUILD_FAIL means the generator wrote invalid Mojo (or the
            # compiler rejected valid Mojo); everything else is a bug
            fail(String(verdict.split("\n")[0]))

    var settings = Settings(
        database=None, deadline=None, max_examples=200, print_blob=True
    )
    if getenv("COMPILER_FUZZ_NO_SHRINK") != "":
        settings.phases = Phases(shrink=False, explain=False)
    given_data(differential, settings)
    print("no differences")
