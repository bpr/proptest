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
# nodes, reached through `Optional[Pointer]` cursors. It returns a hash of
# all of them. `main` prints each function's result on constant arguments
# (lines starting with "c") and on the same arguments hidden behind
# `black_box` ("b"). A second file, comptime.mojo, computes the "c" lines
# with `comptime` and prints them.
#
# Build and run from the repository root:
#
#   pixi run mojo build -I . -o build/compiler_fuzz \
#       examples/compiler_fuzz/compiler_fuzz.mojo
#   pixi run build/compiler_fuzz build/compiler_fuzz_work
#
# Each test case takes about half a minute, nearly all of it compiling.
# The compiler under test is $MOJO (default `mojo`); see
# build_and_compare.sh. COMPILER_FUZZ_NO_SHRINK=1 skips shrinking, and
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
]
comptime NARROW_BITS: List[Int] = [8, 8, 16, 16, 32, 32, 64]
comptime N_NARROW = 7
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

    def __init__(out self, function_index: Int):
        self.loop_variables = []
        self.cursors = materialize[ASSIGNABLE_CURSORS]()
        self.live_cursors = []
        self.loop_depth = 0
        self.function_index = function_index
        self.calls = 0
        self.guards = 0
        self.budget = 30
        self.tracked = ["t0", "t1"]
        self.tracked_ok = True
        self.try_depth = 0

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

    def int_expr(
        mut self, mut data: ConjectureData, depth: Int
    ) raises -> String:
        var choice = data.draw(integers(0, 16 if depth < 3 else 1))
        if choice == 0:
            return self.atom(data)
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
            return String(
                "(",
                self.int_expr(data, d),
                " if ",
                self.condition(data, d),
                " else ",
                self.int_expr(data, d),
                ")",
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
            var kind = data.draw(integers(0, 3))
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
        var choice = data.draw(integers(0, 10 if depth < 3 else 1))
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
            return String(
                "(",
                self.narrow_expr(data, k, d),
                " if ",
                self.condition(data, d),
                " else ",
                self.narrow_expr(data, k, d),
                ")",
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
            return String(
                "(",
                self.vec_expr(data, k, d),
                " if ",
                self.condition(data, d),
                " else ",
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
        var choice = data.draw(integers(0, 12 if depth < 3 else 0))
        var d = depth + 1
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
        var choice = data.draw(integers(0, 26))
        var inner = indent + "    "
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
            # (https://github.com/modular/modular/issues/7593).
            var touch = String(inner, "_ = Bool(ot)\n", inner, "_ = len(lst)\n")
            for name in self.tracked:
                touch += String(inner, "_ = ", name, ".val\n")
            self.loop_variables.append(index)
            self.loop_depth += 1
            var body = self.block(data, inner, depth + 1)
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
            var kind = data.draw(integers(0, 7))
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
                return String(indent, "lst.insert(0, ", t, ".copy())\n")
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
            # a closure that captures a tracked value by reference
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

    @staticmethod
    def checksum() -> String:
        return (
            "_mix(v0, v1, v2, v3, buf, opt, pool, q0, q1, t0, t1, lst, ot)"
            " * 31 + _nmix(n0, n1, n2, n3, n4, n5, n6)"
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
from std.memory import Pointer
from std.memory.alloc import unsafe_alloc


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
    n6: UInt64,
) -> Int:
    var h = Int(n0) * 31 + Int(n1)
    h = h * 31 + Int(n2)
    h = h * 31 + Int(n3)
    h = h * 31 + Int(n4)
    h = h * 31 + Int(n5)
    return h * 31 + Int(n6)


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
    # the destruction order, [3] copies.

    var val: Int
    var ledger: LedgerPtr

    def __init__(out self, val: Int, ledger: LedgerPtr):
        self.val = val
        self.ledger = ledger
        ledger[unsafe_offset=0] += 1
        ledger[unsafe_offset=1] += 1

    def __init__(out self, *, copy: Self):
        self.val = copy.val
        self.ledger = copy.ledger
        self.ledger[unsafe_offset=0] += 1
        self.ledger[unsafe_offset=3] += 1

    def __deinit__(deinit self):
        self.ledger[unsafe_offset=0] -= 1
        self.ledger[unsafe_offset=2] = (
            self.ledger[unsafe_offset=2] * 31 + self.val
        )


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
