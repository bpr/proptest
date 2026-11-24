# Differential testing of the Mojo front end with generated declarations,
# after "Generating Random Well-Typed Featherweight Java Programs Using
# QuickCheck" (Feitosa, Ribeiro, Du Bois; https://github.com/sfeitosa/fj-qc).
#
# Each test case draws a whole program in Featherweight Mojo (FM, see
# docs/featherweight-mojo.md): traits with refinement, required and default
# methods, static constructors and associated `comptime` constants;
# concrete and generic structs that conform to them; generic functions over
# trait bounds; and entry points `run_fN(a, b, c) -> Int`. Every
# expression is drawn for a type wanted in an environment, by reading the
# typing rules of FM backwards, so the program is well typed by
# construction: a `BUILD_FAIL` is a bug in this generator or in the
# compiler.
#
# Stage 2 adds ownership: types are `ImplicitlyCopyable`, `Copyable` (they
# need `.copy()`) or only `Movable` (they need `^`); arguments are read,
# `mut` or `var`; bodies are statements (`var`, assignment to variables
# and fields, `if`, bounded `for`) that move, copy and mutate values. The
# environment tracks which variables are live, and the exclusivity rules
# of each statement. `Res` values count their constructions, copies and
# destructions, and `main` checks that every one was destroyed (UNBALANCED
# otherwise).
#
# Stage 3 (DECL_FUZZ_MUTANTS=1) makes ill-typed mutants instead: each
# program gets exactly one error of a kind drawn first (MU_*: a wrong
# type, a use after `^`, an overlapping `mut` argument, a missing method,
# ...), made at one of the places the generator could make it, and the
# line it's on is marked `# MUTANT`. check_rejected.sh then wants the
# compiler to reject the program, with an error on a marked line, and not
# to crash. DECL_FUZZ_MUTANTS=alias,sig asks for only those kinds.
#
# Every program terminates: each method and function has a rank, and a
# body calls only methods and functions of lower rank; loops have constant
# bounds. The generator also evaluates the program itself (`Program.eval`,
# the reference semantics in the rules doc). The script then compares four
# results: -O0, -O3, `comptime` and the generator's. -O0 and -O3 agreeing
# on a wrong answer (a front-end bug in dispatch, substitution, associated
# constants or argument conventions) shows up as DIFF_EXPECTED.
#
# Build and run from the repository root:
#
#   pixi run mojo build -I . -o build/decl_fuzz \
#       examples/decl_fuzz/decl_fuzz.mojo
#   pixi run build/decl_fuzz build/decl_fuzz_work
#
# The compiler under test is $MOJO (default `mojo`); see
# build_and_compare.sh. DECL_FUZZ_NO_SHRINK=1 skips shrinking;
# DECL_FUZZ_STATS=1 prints what evaluation reached in each program (for
# mutants, which kind each got);
# PROPTEST_SEED, PROPTEST_MAX_EXAMPLES and PROPTEST_WORKERS set the seed,
# the number of programs, and the worker processes (0: one per physical
# core). The failing program is kept as failing_program.mojo in the work
# directory. A second argument replaces build_and_compare.sh or
# check_rejected.sh (for example with a script that just echoes OK, to
# check the generator alone).

from std.ffi import external_call
from std.os import getenv
from std.subprocess import run
from std.sys import argv

from proptest import *

comptime WORKERS = 0
comptime MAX_RANK = 4
"""Methods and functions have ranks 0..MAX_RANK; entry points are above."""
comptime BODY_SIZE = 4
"""The size budget of a body's result expression."""
comptime STEP_LIMIT = 20000
"""Evaluation steps per program; a program that takes more is rejected."""
comptime POOL_LIMIT = 40
"""At most this many types in a context's type pool."""
comptime MAX_DEPTH = 2
"""Blocks (`if`, `for`) nest at most this deep."""

# type kinds
comptime INT = 0
comptime STRUCT = 1
"""A struct; generic ones carry their type argument."""
comptime PARAM = 2
"""A type parameter of the context: `T`, `U`, `Self.T` or a trait's `Self`."""
comptime RES = 3
"""`Res`, the prelude's counted resource (Copyable, one Int field `val`)."""

# capabilities, weakest first
comptime CAP_M = 0
comptime CAP_C = 1
comptime CAP_IC = 2
comptime CAP_NAMES: List[String] = [
    "Movable",
    "Copyable",
    "ImplicitlyCopyable",
]

# argument conventions
comptime CONV_READ = 0
comptime CONV_MUT = 1
comptime CONV_VAR = 2
comptime CONV_PREFIX: List[String] = ["", "mut ", "var "]

# kinds of variables in Γ
comptime V_READ = 0
"""A read argument, a read `self`, or a loop variable."""
comptime V_MUT = 1
"""A `mut` argument or `mut self`: assignable, not movable."""
comptime V_OWNED = 2
"""A local `var` or a `var` argument: assignable and movable."""

# positions an expression is drawn for
comptime P_READ = 0
"""Borrowed: a read argument, a receiver, an operand."""
comptime P_OWNED = 1
"""Consumed: a `var` argument, a field initializer, an assigned value, a
result. A place there needs `.copy()` or `^` unless implicitly copyable."""

# expression kinds
comptime E_LIT = 0
comptime E_VAR = 1
comptime E_BIN = 2
comptime E_TERN = 3
comptime E_FIELD = 4
comptime E_NEW = 5
comptime E_METHOD = 6
comptime E_STATIC = 7
comptime E_K = 8
comptime E_CALL = 9
comptime E_COPY = 10
comptime E_MOVE = 11

# statement kinds
comptime S_VAR = 0
comptime S_ASSIGN = 1
comptime S_EXPR = 2
comptime S_IF = 3
comptime S_FOR = 4
comptime S_USE = 5
"""`_use(v)`: a read with no effect (the workaround in `gen_stmt`)."""

# generation rules, simplest first (shrinking moves toward rule 0)
comptime R_ATOM = 0
comptime R_NEW = 1
comptime R_MAKE = 2
comptime R_BIN = 3
comptime R_TERN = 4
comptime R_FIELD = 5
comptime R_METHOD = 6
comptime R_K = 7
comptime R_CALL = 8

# how an atom uses its variable
comptime A_PLAIN = 0
comptime A_COPY = 1
comptime A_MOVE = 2

# what evaluation reached, for tuning the generator
comptime STAT_OWN = 0
comptime STAT_REQUIRED = 1
comptime STAT_OVERRIDE = 2
comptime STAT_DEFAULT = 3
comptime STAT_STATIC = 4
comptime STAT_GENERIC = 5
comptime STAT_K = 6
comptime STAT_K_SOURCE = 7
comptime STAT_MUT_CALL = 8
comptime STAT_MOVE = 9
comptime STAT_COPY = 10
comptime STAT_ASSIGN = 11
comptime STAT_LOOP = 12
comptime STAT_RES = 13
comptime N_STATS = 14
comptime STAT_NAMES: List[String] = [
    "own",
    "required",
    "override",
    "default",
    "static",
    "generic",
    "K",
    "K_source",
    "mut_call",
    "move",
    "copy",
    "assign",
    "loop",
    "res",
]

# Stage 3: ill-typed mutants (DECL_FUZZ_MUTANTS=1). Each program gets one
# error of one kind; the compiler must reject it on a line marked
# `# MUTANT`.
comptime MU_TYPE = 0
"""An expression of another type where a type is expected."""
comptime MU_USE_MOVED = 1
"""A use of a moved variable."""
comptime MU_IMPLICIT_COPY = 2
"""`.copy()` or `^` left out on a value that isn't `ImplicitlyCopyable`."""
comptime MU_ASSIGN_READ = 3
"""An assignment to a read variable or its field."""
comptime MU_MUT_READ = 4
"""A read variable passed `mut`."""
comptime MU_ALIAS = 5
"""An argument overlapping a `mut` argument of the same call."""
comptime MU_MOVE_READ = 6
"""`^` on a read variable that isn't an Int."""
comptime MU_LOOP_MOVE = 7
"""A loop that moves an outer variable without reinitializing it."""
comptime MU_NO_METHOD = 8
"""A call of a method that the receiver's type doesn't have."""
comptime MU_BOUND = 9
"""A type argument that doesn't conform to its bound."""
comptime MU_MISSING = 10
"""A struct missing a required method or associated constant."""
comptime MU_SIG = 11
"""A method whose signature differs from its trait's."""
comptime MU_CAP = 12
"""A struct declared more copyable than its fields."""
comptime N_MU = 13
comptime MU_NAMES: List[String] = [
    "type",
    "use_moved",
    "implicit_copy",
    "assign_read",
    "mut_read",
    "alias",
    "move_read",
    "loop_move",
    "no_method",
    "bound",
    "missing",
    "sig",
    "cap",
]
comptime MU_ODDS = 6
"""Each chance to apply the mutation is taken 1 time in MU_ODDS."""
comptime MARK = "@@M@@"
"""In generated text, marks the line of the mutation."""

comptime BIN_OPS: List[String] = ["+", "-", "*", "&", "|", "^"]
comptime CMP_OPS: List[String] = ["<", "==", "!="]
comptime LITERALS: List[String] = [
    "0",
    "1",
    "2",
    "(-1)",
    "7",
    "(-3)",
    "100",
    "9223372036854775807",
    "4611686018427387904",
    "(-1000003)",
]
comptime LITERAL_VALUES: List[Int] = [
    0,
    1,
    2,
    -1,
    7,
    -3,
    100,
    9223372036854775807,
    4611686018427387904,
    -1000003,
]

comptime PRELUDE_HEAD = """from std.benchmark import black_box
from std.ffi import external_call


def _use[T: AnyType](x: T):
    pass


"""

comptime RUN_TIME_RES = """comptime _LEDGER = 0x7E5500000000


def _live() -> Pointer[Int, MutUntrackedOrigin]:
    \"\"\"The number of live `Res` values, at a fixed address (no globals).\"\"\"
    return Pointer[Int, MutUntrackedOrigin](unsafe_from_address=_LEDGER)


def _ledger_init():
    # PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE
    _ = external_call["mmap", Int](_LEDGER, 4096, 3, 0x100022, -1, 0)


def _check(i: Int):
    if _live()[] != 0:
        print("UNBALANCED", i, _live()[])
        _live()[] = 0


struct Res(Copyable):
    var val: Int

    def __init__(out self, val: Int):
        self.val = val
        _live()[] += 1

    def __init__(out self, *, copy: Self):
        self.val = copy.val
        _live()[] += 1

    def __deinit__(deinit self):
        _live()[] -= 1


"""

comptime COMPILE_TIME_RES = """struct Res(Copyable):
    var val: Int

    def __init__(out self, val: Int):
        self.val = val

    def __init__(out self, *, copy: Self):
        self.val = copy.val


"""


def env_int(name: String, default: Int) -> Int:
    """The integer in environment variable `name`, or `default`."""
    try:
        var v = getenv(name)
        return Int(v) if v.byte_length() > 0 else default
    except:
        return default


def has(lst: List[Int], x: Int) -> Bool:
    for y in lst:
        if y == x:
            return True
    return False


def index_of(lst: List[Int], x: Int) -> Int:
    for i in range(len(lst)):
        if lst[i] == x:
            return i
    return -1


def pick(mut data: ConjectureData, n: Int) raises -> Int:
    """An index in 0..n-1."""
    return data.draw(integers(0, n - 1))


def draw_conv(mut data: ConjectureData) raises -> Int:
    """Read 1/2, `var` 1/3, `mut` 1/6 of the time.

    A call with a `mut` argument goes only at the root of a statement, so
    `mut` arguments would otherwise rule out most calls."""
    var c = data.draw(integers(0, 5))
    if c <= 2:
        return CONV_READ
    return CONV_VAR if c <= 4 else CONV_MUT


@fieldwise_init
struct TraitDecl(Copyable):
    var parents: List[Int]
    var methods: List[Int]
    """Methods declared in this trait (not its parents), static make too."""
    var has_k: Bool
    """Whether it declares `comptime K<t>: Int`."""
    var make: Int
    """Its `@staticmethod def make<t>(x: Int) -> Self`, or -1."""
    var cap: Int
    """CAP_C or CAP_IC: what it requires of its conforming types."""
    var strengthens: Bool
    """Whether it adds `ImplicitlyCopyable` to Copyable parents."""


@fieldwise_init
struct MethodDecl(Copyable):
    var name: String
    var trait_id: Int
    """The declaring trait, or -1 for a struct's own method."""
    var struct_id: Int
    """The struct of an own method, or -1."""
    var is_static: Bool
    var self_conv: Int
    var params: List[Int]
    """Parameter types, without `self`. In a trait, PARAM 0 is `Self`; in a
    generic struct, the struct's `T`."""
    var convs: List[Int]
    var ret: Int
    var rank: Int
    var has_default: Bool
    var body: Int
    """Default body (trait methods) or the body (own methods), or -1."""


@fieldwise_init
struct StructDecl(Copyable):
    var name: String
    var generic: Bool
    var bound: Int
    """The bound of `T` (generic structs), or -1."""
    var cap: Int
    var fields: List[Int]
    """Field types; field 0 of a generic struct is `Self.T`."""
    var traits: List[Int]
    """Declared conformances."""
    var own: List[Int]
    var impl_methods: List[Int]
    """Trait methods this struct implements (required ones and overrides)."""
    var impl_bodies: List[Int]
    var k_traits: List[Int]
    """The traits whose `K<t>` this struct defines..."""
    var k_values: List[Int]
    """...as this constant..."""
    var k_sources: List[Int]
    """...plus `Self.T.K<source>` when the source isn't -1."""


@fieldwise_init
struct FnDecl(Copyable):
    var name: String
    var bounds: List[Int]
    """One trait bound per type parameter (`T`, `U`)."""
    var params: List[Int]
    """Parameter types; parameter i < len(bounds) has type PARAM i."""
    var convs: List[Int]
    var ret: Int
    var rank: Int
    var body: Int


@fieldwise_init
struct Body(Copyable):
    var stmts: List[Int]
    var ret: Int
    var self_print: Int
    """The type written `Self` in this body and its signature, or -1."""


@fieldwise_init
struct Expr(Copyable):
    var kind: Int
    var a: Int
    """Literal value, variable slot, operator, field, method or function."""
    var ty: Int
    """Its static type, in its context."""
    var kids: List[Int]
    var tys: List[Int]
    """Type arguments of E_CALL; the type of E_STATIC and E_K."""
    var text: String


@fieldwise_init
struct Stmt(Copyable):
    var kind: Int
    var target: Int
    """The place assigned (S_ASSIGN), or -1."""
    var e: Int
    """The value (S_VAR, S_ASSIGN, S_EXPR) or the left operand (S_IF)."""
    var e2: Int
    """The right operand of the condition (S_IF), or -1."""
    var a: Int
    """The comparison (S_IF) or the trip count (S_FOR)."""
    var body: List[Int]
    var orelse: List[Int]
    var name: String
    """The variable declared (S_VAR) or the loop variable (S_FOR)."""


@fieldwise_init
struct Ctx(Copyable):
    """Γ with each variable's kind and state, the type parameters in scope,
    the rank of the body, and the exclusivity state of the statement being
    drawn."""

    var names: List[String]
    var types: List[Int]
    var kinds: List[Int]
    var live: List[Bool]
    var move_depth: List[Int]
    """The block depth where a dead variable was moved."""
    var touched: List[Bool]
    """Used in the current statement (so no longer movable or mut-able)."""
    var excl: List[Bool]
    """Passed as `mut` in the current statement (so unusable in it)."""
    var taken: List[Int]
    """The places passed as `mut` in the current statement (v * 64 + f +
    1), for mutants that overlap them."""
    var bounds: List[Int]
    var param_names: List[String]
    var rank: Int
    var self_print: Int
    var pool: List[Int]
    """The types this context draws from."""
    var depth: Int
    var no_move: Int
    """Inside a ternary branch, where moves would be conditional."""
    var discard: Bool
    """The next expression drawn is the root of `_ = e`, which Mojo
    evaluates without copying (`_ = x.f` of a `Copyable` field is fine)."""
    var counter: Int
    """For fresh local names."""

    def __init__(
        out self,
        var bounds: List[Int],
        var param_names: List[String],
        rank: Int,
        self_print: Int,
        var pool: List[Int],
    ):
        self.names = []
        self.types = []
        self.kinds = []
        self.live = []
        self.move_depth = []
        self.touched = []
        self.excl = []
        self.taken = []
        self.bounds = bounds^
        self.param_names = param_names^
        self.rank = rank
        self.self_print = self_print
        self.pool = pool^
        self.depth = 0
        self.no_move = 0
        self.discard = False
        self.counter = 0

    def push(mut self, var name: String, ty: Int, kind: Int):
        self.names.append(name^)
        self.types.append(ty)
        self.kinds.append(kind)
        self.live.append(True)
        self.move_depth.append(-1)
        self.touched.append(False)
        self.excl.append(False)

    def truncate(mut self, n: Int):
        while len(self.names) > n:
            _ = self.names.pop()
            _ = self.types.pop()
            _ = self.kinds.pop()
            _ = self.live.pop()
            _ = self.move_depth.pop()
            _ = self.touched.pop()
            _ = self.excl.pop()

    def new_statement(mut self):
        for i in range(len(self.names)):
            self.touched[i] = False
            self.excl[i] = False
        self.taken = []


def kind_of_conv(conv: Int) -> Int:
    if conv == CONV_MUT:
        return V_MUT
    return V_OWNED if conv == CONV_VAR else V_READ


@fieldwise_init
struct Cands(Copyable):
    """The candidates of each generation rule for one expression."""

    var atom_vars: List[Int]
    var atom_fields: List[Int]
    var atom_modes: List[Int]
    var makes: List[Int]
    var field_recv: List[Int]
    var field_idx: List[Int]
    var meth_recv: List[Int]
    var meth_id: List[Int]
    var k_recv: List[Int]
    var k_trait: List[Int]
    var call_fn: List[Int]


struct Program(Movable):
    var tkind: List[Int]
    var tid: List[Int]
    var targ: List[Int]
    var traits: List[TraitDecl]
    var structs: List[StructDecl]
    var methods: List[MethodDecl]
    var fns: List[FnDecl]
    var bodies: List[Body]
    var exprs: List[Expr]
    var stmts: List[Stmt]
    var entries: List[Int]
    """Bodies of run_f0, run_f1, ..."""
    var vtag: List[Int]
    """Values: -1 for an Int, -2 for a Res, else the struct."""
    var vint: List[Int]
    var vkids: List[List[Int]]
    var steps: Int
    var stats: List[Int]
    """Dynamic counts per STAT_* kind (DECL_FUZZ_STATS=1 prints them)."""
    var literals: List[String]
    var literal_values: List[Int]
    var int_ty: Int
    var res_ty: Int
    var p0_ty: Int
    var mutant: Int
    """The kind of mutation to make (MU_*), or -1 for a well-typed program."""
    var mutated: Bool
    """Whether the mutation has been made."""
    var loop_mark: Int
    """The depth of the loop body where MU_LOOP_MOVE moved an outer
    variable, until its loop is made (and marked); else -1."""
    var marked_stmts: List[Int]
    """Statements whose every line is marked."""
    var mark_struct: Int
    """The struct whose header line is marked, or -1..."""
    var mark_fields: Bool
    """...and its field lines..."""
    var mark_impl: Int
    """...and the signature of this one of its impl_methods, or -1."""

    def __init__(out self):
        self.tkind = []
        self.tid = []
        self.targ = []
        self.traits = []
        self.structs = []
        self.methods = []
        self.fns = []
        self.bodies = []
        self.exprs = []
        self.stmts = []
        self.entries = []
        self.vtag = []
        self.vint = []
        self.vkids = []
        self.steps = 0
        self.stats = List[Int](length=N_STATS, fill=0)
        self.literals = materialize[LITERALS]()
        self.literal_values = materialize[LITERAL_VALUES]()
        self.int_ty = 0
        self.res_ty = 0
        self.p0_ty = 0
        self.mutant = -1
        self.mutated = False
        self.loop_mark = -1
        self.marked_stmts = []
        self.mark_struct = -1
        self.mark_fields = False
        self.mark_impl = -1
        self.int_ty = self.intern(INT, -1, -1)
        self.res_ty = self.intern(RES, -1, -1)
        self.p0_ty = self.intern(PARAM, 0, -1)

    # ---- types

    def intern(mut self, kind: Int, id: Int, arg: Int) -> Int:
        for i in range(len(self.tkind)):
            if (
                self.tkind[i] == kind
                and self.tid[i] == id
                and self.targ[i] == arg
            ):
                return i
        self.tkind.append(kind)
        self.tid.append(id)
        self.targ.append(arg)
        return len(self.tkind) - 1

    def subst(mut self, ty: Int, args: List[Int]) -> Int:
        """Replaces PARAM i by args[i]."""
        var kind = self.tkind[ty]
        if kind == PARAM:
            return args[self.tid[ty]]
        if kind == STRUCT and self.targ[ty] >= 0:
            var arg = self.subst(self.targ[ty], args)
            return self.intern(STRUCT, self.tid[ty], arg)
        return ty

    def subst_all(mut self, tys: List[Int], args: List[Int]) -> List[Int]:
        var out = List[Int]()
        for t in tys:
            out.append(self.subst(t, args))
        return out^

    def ty_str(self, ty: Int, names: List[String], self_print: Int) -> String:
        if ty == self_print:
            return "Self"
        var kind = self.tkind[ty]
        if kind == INT:
            return "Int"
        if kind == RES:
            return "Res"
        if kind == PARAM:
            return names[self.tid[ty]]
        var s = self.structs[self.tid[ty]].name
        if self.targ[ty] >= 0:
            return String(
                s, "[", self.ty_str(self.targ[ty], names, self_print), "]"
            )
        return s

    def cty(self, ty: Int, ctx: Ctx) -> String:
        return self.ty_str(ty, ctx.param_names, ctx.self_print)

    def refines(self, a: Int, b: Int) -> Bool:
        """Whether trait a is b or refines it (a <= b)."""
        if a == b:
            return True
        for p in self.traits[a].parents:
            if self.refines(p, b):
                return True
        return False

    def conforms(self, ty: Int, t: Int, bounds: List[Int]) -> Bool:
        var kind = self.tkind[ty]
        if kind == INT or kind == RES:
            return False
        if kind == PARAM:
            return self.refines(bounds[self.tid[ty]], t)
        for x in self.structs[self.tid[ty]].traits:
            if self.refines(x, t):
                return True
        return False

    def cap_of(self, ty: Int, bounds: List[Int]) -> Int:
        var kind = self.tkind[ty]
        if kind == INT:
            return CAP_IC
        if kind == RES:
            return CAP_C
        if kind == PARAM:
            return self.traits[bounds[self.tid[ty]]].cap
        return self.structs[self.tid[ty]].cap

    def fields_of(mut self, ty: Int) -> List[Int]:
        if self.tkind[ty] == RES:
            return [self.int_ty]
        if self.tkind[ty] != STRUCT:
            return []
        var s = self.tid[ty]
        var fields = self.structs[s].fields.copy()
        if self.structs[s].generic:
            return self.subst_all(fields, [self.targ[ty]])
        return fields^

    def field_name(self, ty: Int, f: Int) -> String:
        if self.tkind[ty] == RES:
            return "val"
        return String("f", f)

    def type_pool(mut self, bounds: List[Int], n_structs: Int) -> List[Int]:
        """Int, Res, the concrete structs, the parameters in scope, and
        generic structs over them (two levels deep)."""
        var pool: List[Int] = [self.int_ty, self.res_ty]
        for s in range(n_structs):
            if not self.structs[s].generic:
                pool.append(self.intern(STRUCT, s, -1))
        for p in range(len(bounds)):
            pool.append(self.intern(PARAM, p, -1))
        var start = 0
        for _ in range(2):
            var end = len(pool)
            for s in range(n_structs):
                if not self.structs[s].generic:
                    continue
                var b = self.structs[s].bound
                for i in range(start, end):
                    if len(pool) >= POOL_LIMIT:
                        break
                    if self.conforms(pool[i], b, bounds):
                        var t = self.intern(STRUCT, s, pool[i])
                        if not has(pool, t):
                            pool.append(t)
            start = end
        return pool^

    def methods_on(self, ty: Int, bounds: List[Int]) -> List[Int]:
        """Non-static methods callable on a value of type ty."""
        var out = List[Int]()
        if self.tkind[ty] == STRUCT:
            out += self.structs[self.tid[ty]].own.copy()
        for t in range(len(self.traits)):
            if self.conforms(ty, t, bounds):
                for m in self.traits[t].methods:
                    if not self.methods[m].is_static:
                        out.append(m)
        return out^

    def method_args(self, m: Int, recv: Int) -> List[Int]:
        """What to substitute into m's signature for receiver type recv."""
        if self.methods[m].trait_id >= 0:
            return [recv]
        if self.structs[self.methods[m].struct_id].generic:
            return [self.targ[recv]]
        return []

    def method_ret(mut self, m: Int, recv: Int) -> Int:
        var args = self.method_args(m, recv)
        if len(args) == 0:
            return self.methods[m].ret
        return self.subst(self.methods[m].ret, args)

    def method_params(mut self, m: Int, recv: Int) -> List[Int]:
        var args = self.method_args(m, recv)
        var params = self.methods[m].params.copy()
        if len(args) == 0:
            return params^
        return self.subst_all(params, args)

    def has_mut(self, m: Int) -> Bool:
        """Whether m takes `mut self` or a `mut` argument; such calls go
        only at the root of a statement."""
        if self.methods[m].self_conv == CONV_MUT:
            return True
        return has(self.methods[m].convs, CONV_MUT)

    def unify(self, pat: Int, ty: Int, mut assign: List[Int]) -> Bool:
        var kind = self.tkind[pat]
        if kind == PARAM:
            var i = self.tid[pat]
            if assign[i] < 0:
                assign[i] = ty
                return True
            return assign[i] == ty
        if kind == INT or kind == RES:
            return self.tkind[ty] == kind
        if self.tkind[ty] != STRUCT or self.tid[ty] != self.tid[pat]:
            return False
        if self.targ[pat] < 0:
            return True
        return self.unify(self.targ[pat], self.targ[ty], assign)

    def closure(self, declared: List[Int]) -> List[Int]:
        """Every trait some trait in `declared` refines."""
        var out = List[Int]()
        for u in range(len(self.traits)):
            for x in declared:
                if self.refines(x, u):
                    out.append(u)
                    break
        return out^

    def make_ok(self, t: Int, bound: Int) -> Bool:
        """Whether a generic struct with bound `bound` can conform to `t`:
        each static make it must write needs a make of `T` of lower rank,
        to build its `Self.T` field."""
        for x in self.closure([t]):
            var mx = self.traits[x].make
            if mx < 0:
                continue
            var found = False
            for y in self.closure([bound]):
                var my = self.traits[y].make
                if my >= 0 and self.methods[my].rank < self.methods[mx].rank:
                    found = True
            if not found:
                return False
        return True

    # ---- declarations

    def draw_type(
        mut self, mut data: ConjectureData, pool: List[Int]
    ) raises -> Int:
        return pool[pick(data, len(pool))]

    def draw_sig_type(
        mut self, mut data: ConjectureData, pool: List[Int], own: Int
    ) raises -> Int:
        """A parameter or result type: Int, the declaration's own type
        (`Self`, the struct, `T`), or any type in the pool, a third each,
        so that calls returning the type wanted are common."""
        var choice = data.draw(integers(0, 2))
        if choice == 0:
            return self.int_ty
        if choice == 1 and own >= 0:
            return own
        return self.draw_type(data, pool)

    def draw_declarations(mut self, mut data: ConjectureData) raises:
        # trait headers: parents, capability, K, make (FJ: classes in
        # order, so the refinement relation is acyclic)
        var n_traits = data.draw(integers(1, 4))
        for t in range(n_traits):
            var parents = List[Int]()
            if t > 0:
                for _ in range(data.draw(integers(0, 2))):
                    var p = pick(data, t)
                    if not has(parents, p):
                        parents.append(p)
            var cap = CAP_IC - data.draw(integers(0, 1))
            var strengthens = False
            if len(parents) > 0:
                var inherited = CAP_C
                for p in parents:
                    inherited = max(inherited, self.traits[p].cap)
                strengthens = cap > inherited
                cap = max(cap, inherited)
            var has_k = data.draw(booleans())
            var make = -1
            if data.draw(booleans()):
                make = len(self.methods)
                self.methods.append(
                    MethodDecl(
                        String("make", t),
                        t,
                        -1,
                        True,
                        CONV_READ,
                        [self.int_ty],
                        [CONV_READ],
                        self.p0_ty,
                        data.draw(integers(0, MAX_RANK)),
                        False,
                        -1,
                    )
                )
            var methods = List[Int]()
            if make >= 0:
                methods.append(make)
            self.traits.append(
                TraitDecl(parents^, methods^, has_k, make, cap, strengthens)
            )

        # struct headers: capability, fields over earlier structs only
        # (acyclic, like FJ's fields) that are at least as capable,
        # conformances, associated constants
        var n_structs = data.draw(integers(1, 5))
        for s in range(n_structs):
            var generic = data.draw(integers(0, 2)) == 0
            var bound = pick(data, n_traits) if generic else -1
            var bounds = [bound] if generic else List[Int]()
            var cap_max = self.traits[bound].cap if generic else CAP_IC
            var cap = cap_max - data.draw(integers(0, cap_max))
            var pool = self.type_pool(bounds, s)
            var fit = List[Int]()
            for t in pool:
                if self.cap_of(t, bounds) >= cap:
                    fit.append(t)
            var fields = List[Int]()
            if generic:
                fields.append(self.p0_ty)
            for _ in range(data.draw(integers(0 if generic else 1, 3))):
                fields.append(self.draw_type(data, fit))
            var traits = List[Int]()
            for t in range(n_traits):
                if (
                    data.draw(booleans())
                    and self.traits[t].cap <= cap
                    and (not generic or self.make_ok(t, bound))
                ):
                    traits.append(t)
            var k_traits = List[Int]()
            var k_values = List[Int]()
            var k_sources = List[Int]()
            for u in self.closure(traits):
                if not self.traits[u].has_k:
                    continue
                k_traits.append(u)
                k_values.append(data.draw(integers(-5, 20)))
                var source = -1
                if generic and data.draw(integers(0, 3)) > 0:
                    var sources = List[Int]()
                    for v in self.closure([bound]):
                        if self.traits[v].has_k:
                            sources.append(v)
                    if len(sources) > 0:
                        source = sources[pick(data, len(sources))]
                k_sources.append(source)
            self.structs.append(
                StructDecl(
                    String("B" if generic else "S", s),
                    generic,
                    bound,
                    cap,
                    fields^,
                    traits^,
                    [],
                    [],
                    [],
                    k_traits^,
                    k_values^,
                    k_sources^,
                )
            )

        # trait method signatures (they may mention any struct)
        for t in range(n_traits):
            var lo = 0 if (
                self.traits[t].has_k or self.traits[t].make >= 0
            ) else 1
            var pool = self.type_pool([t], n_structs)
            for _ in range(data.draw(integers(lo, 2))):
                var m = len(self.methods)
                var self_conv = (
                    CONV_MUT if data.draw(integers(0, 3)) == 3 else CONV_READ
                )
                var params = List[Int]()
                var convs = List[Int]()
                for _ in range(data.draw(integers(0, 2))):
                    params.append(self.draw_sig_type(data, pool, self.p0_ty))
                    convs.append(draw_conv(data))
                self.methods.append(
                    MethodDecl(
                        String("m", m),
                        t,
                        -1,
                        False,
                        self_conv,
                        params^,
                        convs^,
                        self.draw_sig_type(data, pool, self.p0_ty),
                        data.draw(integers(0, MAX_RANK)),
                        data.draw(booleans()),
                        -1,
                    )
                )
                self.traits[t].methods.append(m)

        # struct own methods
        for s in range(n_structs):
            var bounds = [self.structs[s].bound] if self.structs[
                s
            ].generic else List[Int]()
            var pool = self.type_pool(bounds, n_structs)
            var own_ty = self.self_type(s)
            for _ in range(data.draw(integers(0, 2))):
                var m = len(self.methods)
                var self_conv = (
                    CONV_MUT if data.draw(integers(0, 3)) == 3 else CONV_READ
                )
                var params = List[Int]()
                var convs = List[Int]()
                for _ in range(data.draw(integers(0, 2))):
                    params.append(self.draw_sig_type(data, pool, own_ty))
                    convs.append(draw_conv(data))
                self.methods.append(
                    MethodDecl(
                        String("m", m),
                        -1,
                        s,
                        False,
                        self_conv,
                        params^,
                        convs^,
                        self.draw_sig_type(data, pool, own_ty),
                        data.draw(integers(0, MAX_RANK)),
                        False,
                        -1,
                    )
                )
                self.structs[s].own.append(m)

        # free and generic functions; parameter i < #bounds has type PARAM i
        for f in range(data.draw(integers(0, 3))):
            var bounds = List[Int]()
            for _ in range(data.draw(integers(0, 2))):
                bounds.append(pick(data, n_traits))
            var pool = self.type_pool(bounds, n_structs)
            var own_ty = self.p0_ty if len(bounds) > 0 else -1
            var params = List[Int]()
            var convs = List[Int]()
            for i in range(len(bounds)):
                params.append(self.intern(PARAM, i, -1))
                convs.append(draw_conv(data))
            for _ in range(data.draw(integers(0, 2))):
                params.append(self.draw_sig_type(data, pool, own_ty))
                convs.append(draw_conv(data))
            self.fns.append(
                FnDecl(
                    String("g", f),
                    bounds^,
                    params^,
                    convs^,
                    self.draw_sig_type(data, pool, own_ty),
                    data.draw(integers(0, MAX_RANK)),
                    -1,
                )
            )

    # ---- mutants (stage 3)

    def wants(self, kind: Int) -> Bool:
        """Whether a mutation of this kind is still to be made."""
        return self.mutant == kind and not self.mutated

    def chance(mut self, mut data: ConjectureData, kind: Int) raises -> Bool:
        """Whether to make the mutation here. Call it only where the
        mutation is possible, so that every chance is a real one; the
        shrinker moves the mutation to the first chance."""
        if not self.wants(kind):
            return False
        return data.draw(integers(0, MU_ODDS - 1)) == 0

    def in_branch(self, ctx: Ctx) -> Bool:
        """Whether ctx is inside a ternary branch, where use_moved and
        implicit_copy mutants aren't made: Mojo drops the dead branch of
        a ternary with a constant condition before it checks uses of moved
        values (and implicit copies of a type parameter's values,
        modular/modular#7770), so the mutant could be accepted.
        DECL_FUZZ_NO_DEAD_BRANCH_WORKAROUND=1
        makes them there too."""
        return (
            ctx.no_move > 0
            and getenv("DECL_FUZZ_NO_DEAD_BRANCH_WORKAROUND") == ""
        )

    def mark(mut self, e: Int) -> Int:
        """Marks e as the mutation: the line holding it gets `# MUTANT`."""
        self.exprs[e].text = String(MARK, self.exprs[e].text)
        self.mutated = True
        return e

    def mutation_state(self) -> Int:
        """For backtracking: a mutation in a discarded attempt is undone."""
        return Int(self.mutated) + 2 * (self.loop_mark + 1)

    def restore_mutation(mut self, state: Int):
        self.mutated = state % 2 == 1
        self.loop_mark = state // 2 - 1

    def moved_vars(self, ctx: Ctx) -> List[Int]:
        """The dead variables, except Ints and those moved in the current
        statement. `^` on an Int (a trivial register type) has no effect
        in Mojo, and an argument `x^` is moved at the call, after the
        other arguments are evaluated: `f(x^, x.copy())` is fine."""
        var out = List[Int]()
        for v in range(len(ctx.names)):
            if (
                not ctx.live[v]
                and not ctx.touched[v]
                and ctx.types[v] != self.int_ty
            ):
                out.append(v)
        return out^

    def read_places(mut self, ctx: Ctx, ty: Int) -> List[Int]:
        """Places of type ty in live read variables (MU_MUT_READ)."""
        var out = List[Int]()
        for v in range(len(ctx.names)):
            if ctx.kinds[v] != V_READ or not ctx.live[v] or ctx.excl[v]:
                continue
            if ctx.types[v] == ty:
                out.append(v * 64)
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                if fs[f] == ty:
                    out.append(v * 64 + f + 1)
        return out^

    def alias_places(mut self, ctx: Ctx, ty: Int) -> List[Int]:
        """Places of type ty overlapping a place passed `mut` in this
        statement (MU_ALIAS). Disjoint fields of one variable don't."""
        var out = List[Int]()
        for q in ctx.taken:
            var v = q // 64
            if ctx.types[v] == ty and not has(out, v * 64):
                out.append(v * 64)
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                var p = v * 64 + f + 1
                if fs[f] == ty and (q % 64 == 0 or q == p) and not has(out, p):
                    out.append(p)
        return out^

    def gen_typed(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        size: Int,
        pos: Int,
        stmt_root: Bool = False,
    ) raises -> Int:
        """An expression for a position that expects type ty: for
        MU_TYPE, perhaps one of another type (no two types in the pool
        convert to each other)."""
        if self.wants(MU_TYPE) and self.chance(data, MU_TYPE):
            var others = List[Int]()
            for t in ctx.pool:
                if t != ty:
                    others.append(t)
            var saved = ctx.copy()
            self.mutated = True
            try:
                var t = others[pick(data, len(others))]
                return self.mark(
                    self.gen(data, ctx, t, size, pos, False, stmt_root)
                )
            except e:
                if String(e) != "STUCK":
                    raise e^
                ctx = saved^
                self.mutated = False
        return self.gen(data, ctx, ty, size, pos, False, stmt_root)

    def mutate_declarations(mut self, mut data: ConjectureData) raises:
        """The mutations of declarations, made after the bodies are drawn:
        MU_MISSING, MU_SIG and MU_CAP."""
        var kind = self.mutant
        if kind == MU_MISSING:
            # (struct, index, 0 for a method or 1 for a constant)
            var cands = List[Int]()
            for s in range(len(self.structs)):
                ref sd = self.structs[s]
                for i in range(len(sd.impl_methods)):
                    if not self.methods[sd.impl_methods[i]].has_default:
                        cands.append((s * 64 + i) * 2)
                for i in range(len(sd.k_traits)):
                    cands.append((s * 64 + i) * 2 + 1)
            if len(cands) == 0:
                return
            var c = cands[pick(data, len(cands))]
            var s = c // 128
            var i = (c // 2) % 64
            if c % 2 == 0:
                _ = self.structs[s].impl_methods.pop(i)
                _ = self.structs[s].impl_bodies.pop(i)
            else:
                _ = self.structs[s].k_traits.pop(i)
                _ = self.structs[s].k_values.pop(i)
                _ = self.structs[s].k_sources.pop(i)
            self.mark_struct = s
            self.mutated = True
            return
        if kind == MU_SIG:
            # (not an override: with a default, a method of another
            # signature is just an overload)
            var cands = List[Int]()
            for s in range(len(self.structs)):
                ref sd = self.structs[s]
                for i in range(len(sd.impl_methods)):
                    if not self.methods[sd.impl_methods[i]].has_default:
                        cands.append(s * 64 + i)
            if len(cands) == 0:
                return
            var c = cands[pick(data, len(cands))]
            var s = c // 64
            var i = c % 64
            var md = self.methods[self.structs[s].impl_methods[i]].copy()
            var self_ty = self.self_type(s)
            # concrete types, which substitution leaves alone
            var concrete: List[Int] = [self.int_ty, self.res_ty]
            for x in range(len(self.structs)):
                if not self.structs[x].generic:
                    concrete.append(self.intern(STRUCT, x, -1))
            # what to change: the result type, the convention of `self`,
            # or a parameter's type or convention
            var changes: List[Int] = [0]
            if not md.is_static:
                if md.self_conv == CONV_READ:
                    changes.append(1)
                if len(md.params) > 0:
                    changes += [2, 3]
            var change = changes[pick(data, len(changes))]
            if change == 0:
                var old = self.subst(md.ret, [self_ty])
                var others = List[Int]()
                for t in concrete:
                    if t != old:
                        others.append(t)
                md.ret = others[pick(data, len(others))]
            elif change == 1:
                md.self_conv = CONV_MUT
            else:
                var j = pick(data, len(md.params))
                if change == 2:
                    var old = self.subst(md.params[j], [self_ty])
                    var others = List[Int]()
                    for t in concrete:
                        if t != old:
                            others.append(t)
                    md.params[j] = others[pick(data, len(others))]
                else:
                    # an implementation may take read where its trait
                    # says `mut` or `var`, so the change is never to read
                    var old = md.convs[j]
                    if old == CONV_READ:
                        md.convs[j] = CONV_MUT if data.draw(
                            booleans()
                        ) else CONV_VAR
                    else:
                        md.convs[j] = CONV_VAR if old == CONV_MUT else CONV_MUT
            self.methods.append(md^)
            self.structs[s].impl_methods[i] = len(self.methods) - 1
            self.mark_struct = s
            self.mark_impl = i
            self.mutated = True
            return
        if kind == MU_CAP:
            # (struct, the least capability of its fields)
            var cands = List[Int]()
            for s in range(len(self.structs)):
                ref sd = self.structs[s]
                var bounds = [sd.bound] if sd.generic else List[Int]()
                var least = CAP_IC
                for t in sd.fields:
                    least = min(least, self.cap_of(t, bounds))
                if least < CAP_IC:
                    cands.append(s * 4 + least)
            if len(cands) == 0:
                return
            var c = cands[pick(data, len(cands))]
            var s = c // 4
            var least = c % 4
            # more than the least field allows: a copy (or implicit copy)
            # constructor can't be synthesized
            self.structs[s].cap = least + 1 + pick(data, CAP_IC - least)
            self.mark_struct = s
            self.mark_fields = True
            self.mutated = True

    # ---- bodies

    def push_params(
        self, mut ctx: Ctx, params: List[Int], convs: List[Int], prefix: String
    ):
        for i in range(len(params)):
            ctx.push(String(prefix, i), params[i], kind_of_conv(convs[i]))

    def trait_ctx(mut self, m: Int) -> Ctx:
        var t = self.methods[m].trait_id
        var rank = self.methods[m].rank
        var pool = self.type_pool([t], len(self.structs))
        var ctx = Ctx([t], ["Self"], rank, -1, pool^)
        ctx.push("self", self.p0_ty, kind_of_conv(self.methods[m].self_conv))
        self.push_params(
            ctx, self.methods[m].params, self.methods[m].convs, "p"
        )
        return ctx^

    def self_type(mut self, s: Int) -> Int:
        if self.structs[s].generic:
            return self.intern(STRUCT, s, self.p0_ty)
        return self.intern(STRUCT, s, -1)

    def struct_ctx(
        mut self, mut data: ConjectureData, s: Int, m: Int
    ) raises -> Ctx:
        """The context of struct s's body of method m (own or trait)."""
        var self_ty = self.self_type(s)
        var generic = self.structs[s].generic
        var bounds = [self.structs[s].bound] if generic else List[Int]()
        var rank = self.methods[m].rank
        var pool = self.type_pool(bounds, len(self.structs))
        var ctx = Ctx(
            bounds^,
            ["Self.T"] if generic else List[String](),
            rank,
            self_ty if data.draw(booleans()) else -1,
            pool^,
        )
        if not self.methods[m].is_static:
            ctx.push("self", self_ty, kind_of_conv(self.methods[m].self_conv))
        var params = self.methods[m].params.copy()
        if self.methods[m].trait_id >= 0:
            params = self.subst_all(params, [self_ty])
        self.push_params(
            ctx,
            params,
            self.methods[m].convs,
            "x" if self.methods[m].is_static else "p",
        )
        if self.methods[m].is_static:
            ctx.names[len(ctx.names) - 1] = "x"
        return ctx^

    def body_ret(mut self, s: Int, m: Int) -> Int:
        """Method m's result type in struct s."""
        if self.methods[m].trait_id < 0:
            return self.methods[m].ret
        var self_ty = self.self_type(s)
        return self.subst(self.methods[m].ret, [self_ty])

    def gen_body(
        mut self,
        mut data: ConjectureData,
        var ctx: Ctx,
        ret: Int,
        size: Int = BODY_SIZE,
        root: Bool = False,
    ) raises -> Int:
        # entry points (root) drive everything: give them more statements
        var stmts = self.gen_block(data, ctx, 5 if root else 3)
        ctx.new_statement()
        var r: Int
        if root:
            r = self.gen(data, ctx, ret, size, P_OWNED, True, True)
        else:
            r = self.gen_typed(data, ctx, ret, size, P_OWNED, True)
        if root:
            # A checksum, as in Csmith: the entry point keeps its result in
            # a variable, then returns it plus every Int reachable from its
            # live locals, so that what mutations did to them is printed.
            var name = String("v", ctx.counter)
            ctx.counter += 1
            stmts.append(
                self.add_stmt(Stmt(S_VAR, -1, r, -1, 0, [], [], name.copy()))
            )
            ctx.push(name^, self.int_ty, V_OWNED)
            r = self.checksum(ctx)
        self.bodies.append(Body(stmts^, r, ctx.self_print))
        return len(self.bodies) - 1

    def int_paths(mut self, ty: Int, depth: Int) -> List[List[Int]]:
        """Field paths from a value of type ty to its Ints."""
        var kind = self.tkind[ty]
        if kind == INT:
            return [List[Int]()]
        var out = List[List[Int]]()
        if depth == 0 or (kind != STRUCT and kind != RES):
            return out^
        var fs = self.fields_of(ty)
        for f in range(len(fs)):
            for p in self.int_paths(fs[f], depth - 1):
                var path: List[Int] = [f]
                path += p.copy()
                out.append(path^)
        return out^

    def checksum(mut self, ctx: Ctx) -> Int:
        """The sum of the Ints reachable from the live owned variables (the
        last one is the result), at most 8 per variable."""
        var sum = -1
        for v in range(len(ctx.names)):
            if ctx.kinds[v] != V_OWNED or not ctx.live[v]:
                continue
            var ty = ctx.types[v]
            var paths = self.int_paths(ty, 3)
            for i in range(min(len(paths), 8)):
                var e = self.add(E_VAR, v, ty, [], [], ctx.names[v])
                var cur = ty
                for f in paths[i]:
                    var fty = self.fields_of(cur)[f]
                    var text = String(
                        self.exprs[e].text, ".", self.field_name(cur, f)
                    )
                    e = self.add(E_FIELD, f, fty, [e], [], text^)
                    cur = fty
                if sum < 0:
                    sum = e
                else:
                    var text = String(
                        "(",
                        self.exprs[sum].text,
                        " + ",
                        self.exprs[e].text,
                        ")",
                    )
                    sum = self.add(E_BIN, 0, self.int_ty, [sum, e], [], text^)
        return sum

    def draw_bodies(mut self, mut data: ConjectureData) raises:
        # trait defaults
        for m in range(len(self.methods)):
            if self.methods[m].has_default:
                var ctx = self.trait_ctx(m)
                var ret = self.methods[m].ret
                self.methods[m].body = self.gen_body(data, ctx^, ret)
        # trait methods each struct implements: the required ones, and
        # defaults it overrides
        for s in range(len(self.structs)):
            for t in self.closure(self.structs[s].traits.copy()):
                for m in self.traits[t].methods.copy():
                    if self.methods[m].has_default and not data.draw(
                        booleans()
                    ):
                        continue
                    var ctx = self.struct_ctx(data, s, m)
                    var ret = self.body_ret(s, m)
                    var b = self.gen_body(data, ctx^, ret)
                    self.structs[s].impl_methods.append(m)
                    self.structs[s].impl_bodies.append(b)
        # own methods
        for s in range(len(self.structs)):
            for m in self.structs[s].own.copy():
                var ctx = self.struct_ctx(data, s, m)
                var ret = self.methods[m].ret
                self.methods[m].body = self.gen_body(data, ctx^, ret)
        # functions
        for f in range(len(self.fns)):
            var bounds = self.fns[f].bounds.copy()
            var rank = self.fns[f].rank
            var pool = self.type_pool(bounds, len(self.structs))
            var ctx = Ctx(bounds^, ["T", "U"], rank, -1, pool^)
            self.push_params(ctx, self.fns[f].params, self.fns[f].convs, "p")
            var ret = self.fns[f].ret
            self.fns[f].body = self.gen_body(data, ctx^, ret)
        # entry points
        for _ in range(data.draw(integers(1, 4))):
            var pool = self.type_pool([], len(self.structs))
            var ctx = Ctx([], [], MAX_RANK + 1, -1, pool^)
            for name in ["a", "b", "c"]:
                ctx.push(name, self.int_ty, V_READ)
            self.entries.append(
                self.gen_body(data, ctx^, self.int_ty, BODY_SIZE + 2, True)
            )

    # ---- statements

    def add_stmt(mut self, var s: Stmt) -> Int:
        self.stmts.append(s^)
        return len(self.stmts) - 1

    def gen_block(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        n_max: Int,
        loop: Bool = False,
    ) raises -> List[Int]:
        """Statements; in a nested block, variables live at its start are
        live at its end (moved ones are reinitialized), and its locals go
        out of scope."""
        var n_outer = len(ctx.names)
        var live_at_start = ctx.live.copy()
        var out = List[Int]()
        var moved = -1
        for _ in range(data.draw(integers(0, n_max))):
            if loop and self.wants(MU_LOOP_MOVE):
                # move an outer variable, and don't reinitialize it: the
                # next iteration uses it (the whole loop is marked)
                var outer = List[Int]()
                for v in range(n_outer):
                    if (
                        ctx.kinds[v] == V_OWNED
                        and ctx.live[v]
                        and ctx.types[v] != self.int_ty
                    ):
                        outer.append(v)
                if len(outer) > 0 and self.chance(data, MU_LOOP_MOVE):
                    moved = outer[pick(data, len(outer))]
                    ctx.new_statement()
                    var ty = ctx.types[moved]
                    var text = String(ctx.names[moved], "^")
                    var e = self.add(E_MOVE, moved, ty, [], [], text^)
                    var name = String("v", ctx.counter)
                    ctx.counter += 1
                    ctx.push(name.copy(), ty, V_OWNED)
                    out.append(
                        self.add_stmt(Stmt(S_VAR, -1, e, -1, 0, [], [], name^))
                    )
                    ctx.live[moved] = False
                    ctx.move_depth[moved] = -2  # not assignable either
                    self.mutated = True
                    self.loop_mark = ctx.depth
            if self.wants(MU_USE_MOVED):
                var dead = self.moved_vars(ctx)
                if len(dead) > 0 and self.chance(data, MU_USE_MOVED):
                    var v = dead[pick(data, len(dead))]
                    var e = self.mark(self.place_expr(ctx, v, -1))
                    out.append(
                        self.add_stmt(Stmt(S_USE, -1, e, -1, 0, [], [], ""))
                    )
            out.append(self.gen_stmt(data, ctx))
        if ctx.depth > 0:
            for v in range(n_outer):
                if live_at_start[v] and not ctx.live[v] and v != moved:
                    out.append(self.gen_reinit(data, ctx, v))
            ctx.truncate(n_outer)
        return out^

    def place_expr(mut self, ctx: Ctx, v: Int, f: Int) -> Int:
        """The place `v` or `v.f<f>`."""
        var var_e = self.add(E_VAR, v, ctx.types[v], [], [], ctx.names[v])
        if f < 0:
            return var_e
        var fty = self.fields_of(ctx.types[v])[f]
        var text = String(ctx.names[v], ".", self.field_name(ctx.types[v], f))
        return self.add(E_FIELD, f, fty, [var_e], [], text^)

    def gen_reinit(
        mut self, mut data: ConjectureData, mut ctx: Ctx, v: Int
    ) raises -> Int:
        ctx.new_statement()
        var e = self.gen_typed(data, ctx, ctx.types[v], BODY_SIZE - 2, P_OWNED)
        var target = self.place_expr(ctx, v, -1)
        ctx.live[v] = True
        ctx.move_depth[v] = -1
        return self.add_stmt(Stmt(S_ASSIGN, target, e, -1, 0, [], [], String()))

    def gen_stmt(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        """A statement; if it gets stuck, `var vN = <an Int>` instead."""
        var saved = ctx.copy()
        var state = self.mutation_state()
        try:
            return self.try_stmt(data, ctx)
        except e:
            if String(e) != "STUCK":
                raise e^
        ctx = saved^
        self.restore_mutation(state)
        ctx.new_statement()
        var x = self.gen(data, ctx, self.int_ty, 1, P_OWNED)
        var name = String("v", ctx.counter)
        ctx.counter += 1
        ctx.push(name, self.int_ty, V_OWNED)
        return self.add_stmt(Stmt(S_VAR, -1, x, -1, 0, [], [], name^))

    def try_stmt(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        ctx.new_statement()
        # assignment targets: whole variables that are assignable (and
        # live, or moved in this block), and fields of live mutable ones
        var t_var = List[Int]()
        var t_field = List[Int]()
        for v in range(len(ctx.names)):
            var k = ctx.kinds[v]
            if k == V_READ:
                continue
            if ctx.live[v] or (k == V_OWNED and ctx.move_depth[v] == ctx.depth):
                t_var.append(v)
                t_field.append(-1)
            if ctx.live[v]:
                var fs = self.fields_of(ctx.types[v])
                for f in range(len(fs)):
                    t_var.append(v)
                    t_field.append(f)
        if self.wants(MU_ASSIGN_READ):
            var places = List[Int]()
            for v in range(len(ctx.names)):
                if ctx.kinds[v] == V_READ and ctx.live[v]:
                    places.append(v * 64)
                    for f in range(len(self.fields_of(ctx.types[v]))):
                        places.append(v * 64 + f + 1)
            if len(places) > 0 and self.chance(data, MU_ASSIGN_READ):
                self.mutated = True
                var p = places[pick(data, len(places))]
                var v = p // 64
                var f = p % 64 - 1
                var ty = (
                    ctx.types[v] if f < 0 else self.fields_of(ctx.types[v])[f]
                )
                ctx.touched[v] = True
                var e = self.gen(
                    data, ctx, ty, BODY_SIZE - 1, P_OWNED, False, True
                )
                var target = self.mark(self.place_expr(ctx, v, f))
                return self.add_stmt(
                    Stmt(S_ASSIGN, target, e, -1, 0, [], [], String())
                )
        var mut_types = self.mut_call_types(ctx)
        var kinds: List[Int] = [S_VAR, S_EXPR]
        if len(mut_types) > 0:
            kinds += [S_EXPR, S_EXPR]
        if len(t_var) > 0:
            kinds += [S_ASSIGN, S_ASSIGN]
        if ctx.depth < MAX_DEPTH:
            kinds += [S_IF, S_FOR]
        var kind = kinds[pick(data, len(kinds))]

        if kind == S_VAR:
            # half the time a type with `mut` methods, to call them on
            var receivers = self.mut_receivers(ctx)
            var ty: Int
            if len(receivers) > 0 and data.draw(booleans()):
                ty = receivers[pick(data, len(receivers))]
            else:
                ty = self.draw_type(data, ctx.pool)
            var e = self.gen(data, ctx, ty, BODY_SIZE - 1, P_OWNED, False, True)
            var name = String("v", ctx.counter)
            ctx.counter += 1
            ctx.push(name, ty, V_OWNED)
            return self.add_stmt(Stmt(S_VAR, -1, e, -1, 0, [], [], name^))

        if kind == S_EXPR:
            # the result type of a call with `mut` arguments possible here,
            # if there is one (a random type would rarely match one)
            var ty = mut_types[pick(data, len(mut_types))] if len(
                mut_types
            ) > 0 else self.draw_type(data, ctx.pool)
            ctx.discard = True
            var e = self.gen(
                data, ctx, ty, BODY_SIZE - 1, P_OWNED, True, True, True
            )
            return self.add_stmt(Stmt(S_EXPR, -1, e, -1, 0, [], [], String()))

        if kind == S_ASSIGN:
            var i = pick(data, len(t_var))
            var v = t_var[i]
            var f = t_field[i]
            var ty = ctx.types[v] if f < 0 else self.fields_of(ctx.types[v])[f]
            if f >= 0:
                # the value may read `v` but not move or mut-borrow it
                ctx.touched[v] = True
            var e = self.gen_typed(data, ctx, ty, BODY_SIZE - 1, P_OWNED, True)
            var target = self.place_expr(ctx, v, f)
            if f < 0:
                ctx.live[v] = True
                ctx.move_depth[v] = -1
            if (
                f < 0
                and self.exprs[e].kind == E_VAR
                and self.exprs[e].a == v
                and MARK not in self.exprs[e].text  # (an implicit_copy)
                and getenv("DECL_FUZZ_NO_SELF_ASSIGN_WORKAROUND") == ""
            ):
                # `v = v` on an ImplicitlyCopyable struct gives garbage at
                # -O1+ (modular/modular#7760): a no-op read instead
                return self.add_stmt(
                    Stmt(S_USE, -1, target, -1, 0, [], [], String())
                )
            return self.add_stmt(
                Stmt(S_ASSIGN, target, e, -1, 0, [], [], String())
            )

        if kind == S_IF:
            var op = pick(data, comptime (len(CMP_OPS)))
            var x = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            var y = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            ctx.depth += 1
            var then = self.gen_block(data, ctx, 2)
            var orelse = self.gen_block(data, ctx, 2)
            ctx.depth -= 1
            return self.add_stmt(
                Stmt(S_IF, -1, x, y, op, then^, orelse^, String())
            )

        # S_FOR
        var count = data.draw(integers(0, 3))
        var name = String("i", ctx.counter)
        ctx.counter += 1
        var n = len(ctx.names)
        ctx.push(name.copy(), self.int_ty, V_READ)
        ctx.depth += 1
        var body = self.gen_block(data, ctx, 2, True)
        ctx.depth -= 1
        ctx.truncate(n)
        var loop = self.add_stmt(
            Stmt(S_FOR, -1, -1, -1, count, body^, [], name^)
        )
        if (
            self.loop_mark == ctx.depth + 1
        ):  # this loop's body, not a nested one
            self.marked_stmts.append(loop)
            self.loop_mark = -1
        if getenv("DECL_FUZZ_NO_LOOP_STORE_WORKAROUND") != "":
            return loop
        # A variable whose last use is a field assignment in a loop is
        # destroyed on every iteration (modular/modular#7759), so the loop
        # is followed by a read of each live owned variable. The loop and the reads form one S_USE group.
        var uses: List[Int] = [loop]
        for v in range(n):
            if ctx.kinds[v] == V_OWNED and ctx.live[v]:
                var place = self.place_expr(ctx, v, -1)
                uses.append(
                    self.add_stmt(
                        Stmt(S_USE, -1, place, -1, 0, [], [], String())
                    )
                )
        if len(uses) == 1:
            return loop
        return self.add_stmt(Stmt(S_USE, -1, -1, -1, 0, uses^, [], String()))

    # ---- expressions: the typing rules read backwards

    def add(
        mut self,
        kind: Int,
        a: Int,
        ty: Int,
        var kids: List[Int],
        var tys: List[Int],
        var text: String,
    ) -> Int:
        self.exprs.append(Expr(kind, a, ty, kids^, tys^, text^))
        return len(self.exprs) - 1

    def args_text(self, kids: List[Int], start: Int) -> String:
        var s = String()
        for i in range(start, len(kids)):
            if i > start:
                s += ", "
            s += self.exprs[kids[i]].text
        return s^

    def make_candidates(self, ctx: Ctx, ty: Int) -> List[Int]:
        var out = List[Int]()
        var kind = self.tkind[ty]
        if kind == INT or kind == RES:
            return out^
        for t in range(len(self.traits)):
            var mk = self.traits[t].make
            if (
                mk >= 0
                and self.methods[mk].rank < ctx.rank
                and self.conforms(ty, t, ctx.bounds)
            ):
                out.append(mk)
        return out^

    def mut_places(mut self, ctx: Ctx, ty: Int) -> List[Int]:
        """Places of type ty that can be passed as `mut` now: live mutable
        variables not used yet in this statement, or their fields. Encoded
        as v * 64 + f + 1 (f = -1 for the whole variable)."""
        var out = List[Int]()
        for v in range(len(ctx.names)):
            if (
                ctx.kinds[v] == V_READ
                or not ctx.live[v]
                or ctx.touched[v]
                or ctx.excl[v]
            ):
                continue
            if ctx.types[v] == ty:
                out.append(v * 64)
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                if fs[f] == ty:
                    out.append(v * 64 + f + 1)
        return out^

    def take_place(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        recv: Bool = False,
    ) raises -> Int:
        # mutants: a read place, one overlapping an earlier `mut` argument,
        # or one of another type (not for a receiver: another type may
        # have the same method)
        var bad = List[Int]()
        if self.wants(MU_MUT_READ):
            bad = self.read_places(ctx, ty)
        elif self.wants(MU_ALIAS):
            bad = self.alias_places(ctx, ty)
        elif self.wants(MU_TYPE) and not recv:
            for t in ctx.pool.copy():
                if t != ty:
                    bad += self.mut_places(ctx, t)
        if len(bad) > 0 and self.chance(data, self.mutant):
            var p = bad[pick(data, len(bad))]
            ctx.touched[p // 64] = True
            return self.mark(self.place_expr(ctx, p // 64, p % 64 - 1))
        var places = self.mut_places(ctx, ty)
        if len(places) == 0:
            raise Error("STUCK")
        var p = places[pick(data, len(places))]
        var v = p // 64
        ctx.excl[v] = True
        ctx.touched[v] = True
        ctx.taken.append(p)
        return self.place_expr(ctx, v, p % 64 - 1)

    def callable_here(
        mut self, ctx: Ctx, m: Int, recv: Int, stmt_root: Bool
    ) -> Bool:
        """Whether the `mut` arguments m needs have places now."""
        if not self.has_mut(m):
            return True
        if not stmt_root:
            return False
        var needed = List[Int]()
        if self.methods[m].self_conv == CONV_MUT:
            needed.append(recv)
        var params = self.method_params(m, recv)
        for j in range(len(params)):
            if self.methods[m].convs[j] == CONV_MUT:
                needed.append(params[j])
        return self.places_for(ctx, needed)

    def places_for(mut self, ctx: Ctx, needed: List[Int]) -> Bool:
        """Whether each type in `needed` has a `mut` place, all with
        different root variables (greedily)."""
        var used = List[Int]()
        for ty in needed:
            var found = False
            for p in self.mut_places(ctx, ty):
                if not has(used, p // 64):
                    used.append(p // 64)
                    found = True
                    break
            if not found:
                return False
        return True

    def mut_receivers(self, ctx: Ctx) -> List[Int]:
        """Types in the pool with a `mut self` method callable here."""
        var out = List[Int]()
        for r in ctx.pool:
            var rk = self.tkind[r]
            if rk == INT or rk == RES:
                continue
            for m in self.methods_on(r, ctx.bounds):
                if (
                    self.methods[m].self_conv == CONV_MUT
                    and self.methods[m].rank < ctx.rank
                ):
                    out.append(r)
                    break
        return out^

    def mut_call_types(mut self, ctx: Ctx) -> List[Int]:
        """Result types of the methods and non-generic functions with `mut`
        arguments that can be called now."""
        var out = List[Int]()
        for r in ctx.pool.copy():
            var rk = self.tkind[r]
            if rk == INT or rk == RES:
                continue
            for m in self.methods_on(r, ctx.bounds):
                if (
                    self.has_mut(m)
                    and self.methods[m].rank < ctx.rank
                    and self.callable_here(ctx, m, r, True)
                ):
                    var ret = self.method_ret(m, r)
                    if not has(out, ret):
                        out.append(ret)
        for f in range(len(self.fns)):
            if (
                len(self.fns[f].bounds) > 0
                or self.fns[f].rank >= ctx.rank
                or not has(self.fns[f].convs, CONV_MUT)
            ):
                continue
            var needed = List[Int]()
            for j in range(len(self.fns[f].params)):
                if self.fns[f].convs[j] == CONV_MUT:
                    needed.append(self.fns[f].params[j])
            if self.places_for(ctx, needed) and not has(out, self.fns[f].ret):
                out.append(self.fns[f].ret)
        return out^

    def gen_arg(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        conv: Int,
        size: Int,
        mut_call: Bool = False,
    ) raises -> Int:
        """An argument; mut_call says the call has `mut` arguments."""
        if conv == CONV_MUT:
            return self.take_place(data, ctx, ty)
        if (
            conv == CONV_READ
            and mut_call
            and ty != self.int_ty
            and self.wants(MU_ALIAS)
        ):
            # a read argument overlapping a `mut` one (an Int is passed by
            # value, so it may)
            var bad = self.alias_places(ctx, ty)
            if len(bad) > 0 and self.chance(data, MU_ALIAS):
                var p = bad[pick(data, len(bad))]
                return self.mark(self.place_expr(ctx, p // 64, p % 64 - 1))
        return self.gen_typed(
            data, ctx, ty, size, P_OWNED if conv == CONV_VAR else P_READ
        )

    def gen(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        size: Int,
        pos: Int,
        root: Bool = False,
        stmt_root: Bool = False,
        prefer_mut: Bool = False,
    ) raises -> Int:
        """An expression of type ty in ctx (Γ ⊢ ? : ty), for position pos.
        At the root of an entry point, only calls and associated constants,
        if there are any. Calls with `mut` arguments only at the root of a
        statement; with prefer_mut, only those if there are any."""
        var kind = self.tkind[ty]
        var cap = self.cap_of(ty, ctx.bounds)
        var discard = ctx.discard
        ctx.discard = False

        if self.wants(MU_USE_MOVED):
            var dead = List[Int]()
            for v in self.moved_vars(ctx):
                if ctx.types[v] == ty:
                    dead.append(v)
            if (
                len(dead) > 0
                and not self.in_branch(ctx)
                and self.chance(data, MU_USE_MOVED)
            ):
                var v = dead[pick(data, len(dead))]
                var e = self.place_expr(ctx, v, -1)
                if pos == P_OWNED and cap == CAP_C:
                    var text = String(self.exprs[e].text, ".copy()")
                    e = self.add(E_COPY, 0, ty, [e], [], text^)
                elif pos == P_OWNED and cap == CAP_M:
                    var text = String(ctx.names[v], "^")
                    e = self.add(E_MOVE, v, ty, [], [], text^)
                return self.mark(e)
        if self.wants(MU_MOVE_READ) and pos == P_OWNED and kind != INT:
            # (a read Int is passed by value, so it may be moved)
            var reads = List[Int]()
            for v in range(len(ctx.names)):
                if (
                    ctx.kinds[v] == V_READ
                    and ctx.live[v]
                    and not ctx.excl[v]
                    and ctx.types[v] == ty
                ):
                    reads.append(v)
            if len(reads) > 0 and self.chance(data, MU_MOVE_READ):
                var v = reads[pick(data, len(reads))]
                ctx.touched[v] = True
                var text = String(ctx.names[v], "^")
                return self.mark(self.add(E_MOVE, v, ty, [], [], text^))

        # T-Var, and fields of variables (so that `self.f0` is a ground
        # term for `Self.T`), each used as the position allows
        var atom_vars = List[Int]()
        var atom_fields = List[Int]()
        var atom_modes = List[Int]()
        for v in range(len(ctx.types)):
            if not ctx.live[v] or ctx.excl[v]:
                continue
            if ctx.types[v] == ty:
                if pos == P_READ or cap == CAP_IC:
                    atom_vars.append(v)
                    atom_fields.append(-1)
                    atom_modes.append(A_PLAIN)
                if pos == P_OWNED and cap == CAP_C:
                    atom_vars.append(v)
                    atom_fields.append(-1)
                    atom_modes.append(A_COPY)
                # `_ = x^` doesn't move x in Mojo (it keeps x alive, like
                # `_ = x`), so mutants have no moves there; stage 2 keeps
                # them, as treating x as moved is only stricter
                if (
                    pos == P_OWNED
                    and ctx.kinds[v] == V_OWNED
                    and not ctx.touched[v]
                    and ctx.no_move == 0
                    and not (discard and self.mutant >= 0)
                ):
                    atom_vars.append(v)
                    atom_fields.append(-1)
                    atom_modes.append(A_MOVE)
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                if fs[f] != ty:
                    continue
                if pos == P_READ or cap == CAP_IC:
                    atom_vars.append(v)
                    atom_fields.append(f)
                    atom_modes.append(A_PLAIN)
                elif cap == CAP_C:
                    atom_vars.append(v)
                    atom_fields.append(f)
                    atom_modes.append(A_COPY)
        var makes = self.make_candidates(ctx, ty)

        # candidates for each rule; FJ: one rule among the possible ones
        var field_recv = List[Int]()
        var field_idx = List[Int]()
        var meth_recv = List[Int]()
        var meth_id = List[Int]()
        var k_recv = List[Int]()
        var k_trait = List[Int]()
        var call_fn = List[Int]()
        if size > 0:
            for i in range(len(ctx.pool)):
                var r = ctx.pool[i]
                var rk = self.tkind[r]
                if rk == INT:
                    continue
                if pos == P_READ or cap >= CAP_C:
                    var fs = self.fields_of(r)
                    for f in range(len(fs)):
                        if fs[f] == ty:
                            field_recv.append(r)
                            field_idx.append(f)
                if rk == RES:
                    continue
                for m in self.methods_on(r, ctx.bounds):
                    if (
                        self.methods[m].rank < ctx.rank
                        and self.method_ret(m, r) == ty
                        and self.callable_here(ctx, m, r, stmt_root)
                    ):
                        meth_recv.append(r)
                        meth_id.append(m)
                if kind == INT:
                    for t in range(len(self.traits)):
                        if self.traits[t].has_k and self.conforms(
                            r, t, ctx.bounds
                        ):
                            k_recv.append(r)
                            k_trait.append(t)
            for f in range(len(self.fns)):
                if self.fns[f].rank >= ctx.rank:
                    continue
                if has(self.fns[f].convs, CONV_MUT):
                    if not stmt_root:
                        continue
                    if len(self.fns[f].bounds) == 0:
                        var needed = List[Int]()
                        for j in range(len(self.fns[f].params)):
                            if self.fns[f].convs[j] == CONV_MUT:
                                needed.append(self.fns[f].params[j])
                        if not self.places_for(ctx, needed):
                            continue
                if len(self.call_assignment(f, ty, ctx)) > 0 or (
                    len(self.fns[f].bounds) == 0 and self.fns[f].ret == ty
                ):
                    call_fn.append(f)

        # Unlike fj-qc, the rules aren't equally likely: a rule appears
        # in the list as many times as its weight, so that dispatch, calls
        # and associated constants are reached often. The simplest rules
        # still come first, where shrinking leads.
        var rules = List[Int]()
        if kind == INT or len(atom_vars) > 0:
            rules.append(R_ATOM)
        if kind == STRUCT or kind == RES:
            rules.append(R_NEW)
        if len(makes) > 0:
            rules += [R_MAKE, R_MAKE]
        if size > 0:
            if kind == INT:
                rules.append(R_BIN)
            rules.append(R_TERN)
            if len(field_recv) > 0:
                rules.append(R_FIELD)
            if len(meth_recv) > 0:
                rules += [R_METHOD, R_METHOD, R_METHOD, R_METHOD]
            if len(k_recv) > 0:
                rules += [R_K, R_K]
            if len(call_fn) > 0:
                rules += [R_CALL, R_CALL, R_CALL]
        if prefer_mut:
            var mr = List[Int]()
            var mm = List[Int]()
            for i in range(len(meth_id)):
                if self.has_mut(meth_id[i]):
                    mr.append(meth_recv[i])
                    mm.append(meth_id[i])
            var mf = List[Int]()
            for f in call_fn:
                if has(self.fns[f].convs, CONV_MUT):
                    mf.append(f)
            if len(mm) > 0 or len(mf) > 0:
                meth_recv = mr^
                meth_id = mm^
                call_fn = mf^
                rules = List[Int]()
                if len(meth_id) > 0:
                    rules.append(R_METHOD)
                if len(call_fn) > 0:
                    rules.append(R_CALL)
        if root:
            var calls = List[Int]()
            for r in rules:
                if r == R_METHOD or r == R_CALL or r == R_K:
                    calls.append(r)
            if len(calls) > 0:
                rules = calls^
        if len(rules) == 0:
            raise Error("STUCK")
        # Try a rule; if it gets stuck (a `mut` place or the only variable
        # of a type parameter's type was taken earlier in the statement),
        # restore Γ and try another: bounded backtracking, which fj-qc
        # avoids and Pałka et al. use.
        var c = Cands(
            atom_vars^,
            atom_fields^,
            atom_modes^,
            makes^,
            field_recv^,
            field_idx^,
            meth_recv^,
            meth_id^,
            k_recv^,
            k_trait^,
            call_fn^,
        )
        while len(rules) > 0:
            var rule = rules[pick(data, len(rules))]
            var saved = ctx.copy()
            var state = self.mutation_state()
            try:
                return self.apply_rule(
                    data, ctx, rule, ty, size, pos, c, discard
                )
            except e:
                if String(e) != "STUCK":
                    raise e^
                ctx = saved^
                self.restore_mutation(state)
                var rest = List[Int]()
                for r in rules:
                    if r != rule:
                        rest.append(r)
                rules = rest^
        raise Error("STUCK")

    def apply_rule(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        rule: Int,
        ty: Int,
        size: Int,
        pos: Int,
        c: Cands,
        discard: Bool = False,
    ) raises -> Int:
        var kind = self.tkind[ty]
        var cap = self.cap_of(ty, ctx.bounds)
        var sub = size - 1 if size > 0 else 0
        var half = size // 2

        if rule == R_ATOM:
            var n = len(c.atom_vars)
            var i = pick(data, n + 1 if kind == INT else n)
            if kind == INT and i == n:
                var l = data.draw(integers(0, len(self.literals) - 1))
                return self.add(
                    E_LIT,
                    self.literal_values[l],
                    ty,
                    [],
                    [],
                    self.literals[l],
                )
            var v = c.atom_vars[i]
            var mode = c.atom_modes[i]
            if (
                not discard
                and not self.in_branch(ctx)
                and (mode == A_COPY or (mode == A_MOVE and cap < CAP_IC))
                and self.chance(data, MU_IMPLICIT_COPY)
            ):
                ctx.touched[v] = True
                return self.mark(self.place_expr(ctx, v, c.atom_fields[i]))
            if mode == A_MOVE:
                ctx.live[v] = False
                ctx.move_depth[v] = ctx.depth
                ctx.touched[v] = True
                return self.add(
                    E_MOVE, v, ty, [], [], String(ctx.names[v], "^")
                )
            ctx.touched[v] = True
            var place = self.place_expr(ctx, v, c.atom_fields[i])
            if mode == A_COPY:
                var text = String(self.exprs[place].text, ".copy()")
                return self.add(E_COPY, 0, ty, [place], [], text^)
            return place

        if rule == R_NEW:  # T-New: the fields are consumed
            var bad = self.bad_type_text(data, ctx, ty)
            var kids = List[Int]()
            for ft in self.fields_of(ty):
                kids.append(self.gen_typed(data, ctx, ft, sub, P_OWNED))
            var text = String(
                self.cty(ty, ctx) if bad == "" else bad,
                "(",
                self.args_text(kids, 0),
                ")",
            )
            var e = self.add(E_NEW, 0, ty, kids^, [], text^)
            return self.mark(e) if bad != "" else e

        if rule == R_MAKE:  # static call: τ.make<t>(e)
            var m = c.makes[pick(data, len(c.makes))]
            var bad = self.bad_type_text(data, ctx, ty)
            var arg = self.gen_typed(data, ctx, self.int_ty, sub, P_READ)
            var text = String(
                self.cty(ty, ctx) if bad == "" else bad,
                ".",
                self.methods[m].name,
                "(",
                self.exprs[arg].text,
                ")",
            )
            var e = self.add(E_STATIC, m, ty, [arg], [ty], text^)
            return self.mark(e) if bad != "" else e

        if rule == R_BIN:
            var op = pick(data, comptime (len(BIN_OPS)))
            var l = self.gen_typed(data, ctx, ty, half, P_READ)
            var r = self.gen_typed(data, ctx, ty, half, P_READ)
            var ops = materialize[BIN_OPS]()
            var text = String(
                "(",
                self.exprs[l].text,
                " ",
                ops[op],
                " ",
                self.exprs[r].text,
                ")",
            )
            return self.add(E_BIN, op, ty, [l, r], [], text^)

        if rule == R_TERN:  # the branches are owned values, never moves
            var op = pick(data, comptime (len(CMP_OPS)))
            var x = self.gen_typed(data, ctx, self.int_ty, half, P_READ)
            var y = self.gen_typed(data, ctx, self.int_ty, half, P_READ)
            ctx.no_move += 1
            var t = self.gen_typed(data, ctx, ty, half, P_OWNED)
            var e = self.gen_typed(data, ctx, ty, half, P_OWNED)
            ctx.no_move -= 1
            var ops = materialize[CMP_OPS]()
            var text = String(
                "(",
                self.exprs[t].text,
                " if ",
                self.exprs[x].text,
                " ",
                ops[op],
                " ",
                self.exprs[y].text,
                " else ",
                self.exprs[e].text,
                ")",
            )
            return self.add(E_TERN, op, ty, [x, y, t, e], [], text^)

        if rule == R_FIELD:  # T-Field, copied when consumed
            var i = pick(data, len(c.field_recv))
            var recv = self.gen(data, ctx, c.field_recv[i], sub, P_READ)
            var text = String(
                self.exprs[recv].text,
                ".",
                self.field_name(c.field_recv[i], c.field_idx[i]),
            )
            var fe = self.add(E_FIELD, c.field_idx[i], ty, [recv], [], text^)
            if (
                pos == P_OWNED
                and cap == CAP_C
                and not discard
                and not self.in_branch(ctx)
                and self.chance(data, MU_IMPLICIT_COPY)
            ):
                return self.mark(fe)
            if pos == P_OWNED and cap == CAP_C:
                var ctext = String(self.exprs[fe].text, ".copy()")
                return self.add(E_COPY, 0, ty, [fe], [], ctext^)
            return fe

        if rule == R_METHOD:  # T-Invk
            var i = pick(data, len(c.meth_recv))
            var r = c.meth_recv[i]
            var m = c.meth_id[i]
            var name = self.methods[m].name
            var wrong = False
            if self.wants(MU_NO_METHOD):
                # the name of a method r doesn't have
                var avail = self.methods_on(r, ctx.bounds)
                var others = List[Int]()
                for m2 in range(len(self.methods)):
                    if not self.methods[m2].is_static and not has(avail, m2):
                        others.append(m2)
                if len(others) > 0 and self.chance(data, MU_NO_METHOD):
                    name = self.methods[others[pick(data, len(others))]].name
                    self.mutated = True
                    wrong = True
            var kids = List[Int]()
            if self.methods[m].self_conv == CONV_MUT:
                kids.append(self.take_place(data, ctx, r, True))
            else:
                kids.append(self.gen(data, ctx, r, sub, P_READ))
            var params = self.method_params(m, r)
            var convs = self.methods[m].convs.copy()
            var mut_call = self.has_mut(m)
            for j in range(len(params)):
                kids.append(
                    self.gen_arg(data, ctx, params[j], convs[j], half, mut_call)
                )
            var text = String(
                self.exprs[kids[0]].text,
                ".",
                name,
                "(",
                self.args_text(kids, 1),
                ")",
            )
            var e = self.add(E_METHOD, m, ty, kids^, [], text^)
            return self.mark(e) if wrong else e

        if rule == R_K:  # an associated constant: τ.K<t>
            var i = pick(data, len(c.k_recv))
            var text = String(self.cty(c.k_recv[i], ctx), ".K", c.k_trait[i])
            return self.add(E_K, c.k_trait[i], ty, [], [c.k_recv[i]], text^)

        # R_CALL: a free or generic function; T-UCast's counterpart is
        # passing a conforming type for a bounded parameter
        var f = c.call_fn[pick(data, len(c.call_fn))]
        var targs = List[Int]()
        var n_tp = len(self.fns[f].bounds)
        if n_tp > 0:
            targs = self.call_assignment(f, ty, ctx)
            for i in range(n_tp):
                if targs[i] < 0:
                    var ok = self.conforming(ctx, self.fns[f].bounds[i])
                    targs[i] = ok[pick(data, len(ok))]
        # MU_BOUND: a type argument that doesn't conform, (i, type)
        var bad_i = -1
        var bad_t = -1
        if n_tp > 0 and self.wants(MU_BOUND):
            var cands = List[Int]()
            for i in range(n_tp):
                for t in ctx.pool:
                    if not self.conforms(t, self.fns[f].bounds[i], ctx.bounds):
                        cands.append(i * 1024 + t)
            if len(cands) > 0 and self.chance(data, MU_BOUND):
                var x = cands[pick(data, len(cands))]
                bad_i = x // 1024
                bad_t = x % 1024
                self.mutated = True
        var params = self.fns[f].params.copy()
        if n_tp > 0:
            params = self.subst_all(params, targs)
        var convs = self.fns[f].convs.copy()
        var mut_call = has(convs, CONV_MUT)
        var mutated_before = self.mutated
        var kids = List[Int]()
        for j in range(len(params)):
            kids.append(
                self.gen_arg(data, ctx, params[j], convs[j], half, mut_call)
            )
        # an argument of another type might change what the type
        # arguments are inferred to be, so they're explicit then
        var forced = bad_i >= 0 or (self.mutated and not mutated_before)
        var text = self.fns[f].name
        if n_tp > 0 and (data.draw(booleans()) or forced):
            text += "["
            for i in range(n_tp):
                if i > 0:
                    text += ", "
                text += self.cty(bad_t if i == bad_i else targs[i], ctx)
            text += "]"
        text += String("(", self.args_text(kids, 0), ")")
        var e = self.add(E_CALL, f, ty, kids^, targs^, text^)
        return self.mark(e) if bad_i >= 0 else e

    def bad_type_text(
        mut self, mut data: ConjectureData, ctx: Ctx, ty: Int
    ) raises -> String:
        """For MU_BOUND, ty (a generic struct type) written with a type
        argument that doesn't conform to its bound; otherwise ""."""
        if (
            not self.wants(MU_BOUND)
            or self.tkind[ty] != STRUCT
            or self.targ[ty] < 0
        ):
            return ""
        var s = self.tid[ty]
        var cands = List[Int]()
        for t in ctx.pool:
            if not self.conforms(t, self.structs[s].bound, ctx.bounds):
                cands.append(t)
        if len(cands) == 0 or not self.chance(data, MU_BOUND):
            return ""
        self.mutated = True
        var t = cands[pick(data, len(cands))]
        return String(self.structs[s].name, "[", self.cty(t, ctx), "]")

    def conforming(self, ctx: Ctx, t: Int) -> List[Int]:
        var out = List[Int]()
        for r in ctx.pool:
            if self.conforms(r, t, ctx.bounds):
                out.append(r)
        return out^

    def call_assignment(self, f: Int, ty: Int, ctx: Ctx) -> List[Int]:
        """Type arguments making generic function f return ty (-1 where
        free), or [] if there are none."""
        var n_tp = len(self.fns[f].bounds)
        if n_tp == 0:
            return []
        var assign = List[Int]()
        for _ in range(n_tp):
            assign.append(-1)
        if not self.unify(self.fns[f].ret, ty, assign):
            return []
        for i in range(n_tp):
            var b = self.fns[f].bounds[i]
            if assign[i] >= 0:
                if not self.conforms(assign[i], b, ctx.bounds):
                    return []
            elif len(self.conforming(ctx, b)) == 0:
                return []
        return assign^

    # ---- the reference semantics: big-step, call by value, with a store
    # of variable slots; `mut` arguments are copied in and written back
    # (Mojo's exclusivity rules make that the same as by reference)

    def new_value(mut self, tag: Int, x: Int, var kids: List[Int]) -> Int:
        self.vtag.append(tag)
        self.vint.append(x)
        self.vkids.append(kids^)
        return len(self.vtag) - 1

    def new_int(mut self, x: Int) -> Int:
        return self.new_value(-1, x, [])

    def read_place(self, e: Int, frame: List[Int]) raises -> Int:
        if self.exprs[e].kind == E_VAR:
            var v = frame[self.exprs[e].a]
            if v < 0:
                raise Error("evaluator: read of a moved variable")
            return v
        var base = self.read_place(self.exprs[e].kids[0], frame)
        return self.vkids[base][self.exprs[e].a]

    def write_place(mut self, e: Int, v: Int, mut frame: List[Int]) raises:
        if self.exprs[e].kind == E_VAR:
            frame[self.exprs[e].a] = v
            return
        var kid = self.exprs[e].kids[0]
        var base = self.read_place(kid, frame)
        var kids = self.vkids[base].copy()
        kids[self.exprs[e].a] = v
        var updated = self.new_value(self.vtag[base], self.vint[base], kids^)
        self.write_place(kid, updated, frame)

    def eval(
        mut self, e: Int, mut frame: List[Int], targs: List[Int]
    ) raises -> Int:
        self.steps += 1
        if self.steps > STEP_LIMIT:
            raise Error("STEP_LIMIT")
        var kind = self.exprs[e].kind
        var a = self.exprs[e].a
        var kids = self.exprs[e].kids.copy()
        if kind == E_LIT:
            return self.new_int(a)
        if kind == E_VAR:
            return self.read_place(e, frame)
        if kind == E_MOVE:
            self.stats[STAT_MOVE] += 1
            var v = frame[a]
            if v < 0:
                raise Error("evaluator: move of a moved variable")
            frame[a] = -1
            return v
        if kind == E_COPY:
            self.stats[STAT_COPY] += 1
            return self.eval(kids[0], frame, targs)
        if kind == E_BIN:
            var x = self.vint[self.eval(kids[0], frame, targs)]
            var y = self.vint[self.eval(kids[1], frame, targs)]
            var r: Int
            if a == 0:
                r = x + y
            elif a == 1:
                r = x - y
            elif a == 2:
                r = x * y
            elif a == 3:
                r = x & y
            elif a == 4:
                r = x | y
            else:
                r = x ^ y
            return self.new_int(r)
        if kind == E_TERN:
            var x = self.vint[self.eval(kids[0], frame, targs)]
            var y = self.vint[self.eval(kids[1], frame, targs)]
            if self.compare(a, x, y):
                return self.eval(kids[2], frame, targs)
            return self.eval(kids[3], frame, targs)
        if kind == E_FIELD:
            var v = self.eval(kids[0], frame, targs)
            return self.vkids[v][a]
        if kind == E_NEW:
            var ty = self.subst(self.exprs[e].ty, targs)
            var vals = List[Int]()
            for k in kids:
                vals.append(self.eval(k, frame, targs))
            if self.tkind[ty] == RES:
                self.stats[STAT_RES] += 1
                return self.new_value(-2, 0, vals^)
            return self.new_value(self.tid[ty], 0, vals^)
        if kind == E_METHOD:
            var recv_ty = self.subst(self.exprs[kids[0]].ty, targs)
            var convs: List[Int] = [self.methods[a].self_conv]
            convs += self.methods[a].convs.copy()
            return self.call(a, -1, recv_ty, kids, convs, frame, targs, [])
        if kind == E_STATIC:
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return self.call(a, -1, ty, kids, [CONV_READ], frame, targs, [])
        if kind == E_K:
            self.stats[STAT_K] += 1
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return self.new_int(self.k_value(ty, a))
        # E_CALL
        if len(self.fns[a].bounds) > 0:
            self.stats[STAT_GENERIC] += 1
        var f_targs = self.subst_all(self.exprs[e].tys.copy(), targs)
        var convs = self.fns[a].convs.copy()
        return self.call(-1, a, -1, kids, convs, frame, targs, f_targs)

    def compare(self, op: Int, x: Int, y: Int) -> Bool:
        if op == 0:
            return x < y
        return x == y if op == 1 else x != y

    def call(
        mut self,
        m: Int,
        f: Int,
        recv_ty: Int,
        args: List[Int],
        convs: List[Int],
        mut frame: List[Int],
        targs: List[Int],
        f_targs: List[Int],
    ) raises -> Int:
        """Calls method m (receiver type recv_ty) or function f (type
        arguments f_targs): evaluates the arguments in order (in the
        caller's targs), runs the body, then writes the `mut` ones back."""
        var callee = List[Int]()
        var has_mut = False
        for i in range(len(args)):
            if convs[i] == CONV_MUT:
                callee.append(self.read_place(args[i], frame))
                has_mut = True
            else:
                callee.append(self.eval(args[i], frame, targs))
        var result: Int
        if f >= 0:
            result = self.run_body(self.fns[f].body, callee, f_targs)
        else:
            result = self.call_method(m, recv_ty, callee)
        if has_mut:
            self.stats[STAT_MUT_CALL] += 1
            for i in range(len(args)):
                if convs[i] == CONV_MUT:
                    self.write_place(args[i], callee[i], frame)
        return result

    def run_body(
        mut self, b: Int, mut frame: List[Int], targs: List[Int]
    ) raises -> Int:
        # the body's own locals stay in scope for its result
        for s in self.bodies[b].stmts.copy():
            self.exec(s, frame, targs)
        return self.eval(self.bodies[b].ret, frame, targs)

    def exec_block(
        mut self, stmts: List[Int], mut frame: List[Int], targs: List[Int]
    ) raises:
        var n = len(frame)
        for s in stmts:
            self.exec(s, frame, targs)
        while len(frame) > n:
            _ = frame.pop()

    def exec(mut self, s: Int, mut frame: List[Int], targs: List[Int]) raises:
        self.steps += 1
        if self.steps > STEP_LIMIT:
            raise Error("STEP_LIMIT")
        var kind = self.stmts[s].kind
        var e = self.stmts[s].e
        if kind == S_VAR:
            frame.append(self.eval(e, frame, targs))
        elif kind == S_ASSIGN:
            self.stats[STAT_ASSIGN] += 1
            var v = self.eval(e, frame, targs)
            self.write_place(self.stmts[s].target, v, frame)
        elif kind == S_EXPR:
            _ = self.eval(e, frame, targs)
        elif kind == S_USE:
            for st in self.stmts[s].body.copy():
                self.exec(st, frame, targs)
        elif kind == S_IF:
            var x = self.vint[self.eval(e, frame, targs)]
            var y = self.vint[self.eval(self.stmts[s].e2, frame, targs)]
            if self.compare(self.stmts[s].a, x, y):
                self.exec_block(self.stmts[s].body.copy(), frame, targs)
            else:
                self.exec_block(self.stmts[s].orelse.copy(), frame, targs)
        else:
            var body = self.stmts[s].body.copy()
            for i in range(self.stmts[s].a):
                self.stats[STAT_LOOP] += 1
                frame.append(self.new_int(i))
                self.exec_block(body, frame, targs)
                _ = frame.pop()

    def call_method(
        mut self, m: Int, recv_ty: Int, mut frame: List[Int]
    ) raises -> Int:
        """Static dispatch on the receiver's type, resolved: the struct's
        own body, its implementation, or the trait's default."""
        if self.tkind[recv_ty] != STRUCT:
            raise Error("evaluator: receiver type not resolved")
        var s = self.tid[recv_ty]
        var targs = List[Int]()
        if self.structs[s].generic:
            targs.append(self.targ[recv_ty])
        if self.methods[m].struct_id >= 0:
            self.stats[STAT_OWN] += 1
            return self.run_body(self.methods[m].body, frame, targs)
        if self.methods[m].is_static:
            self.stats[STAT_STATIC] += 1
        var i = index_of(self.structs[s].impl_methods, m)
        if i >= 0:
            self.stats[
                STAT_OVERRIDE if self.methods[m].has_default else STAT_REQUIRED
            ] += 1
            return self.run_body(self.structs[s].impl_bodies[i], frame, targs)
        self.stats[STAT_DEFAULT] += 1
        return self.run_body(self.methods[m].body, frame, [recv_ty])

    def k_value(mut self, ty: Int, t: Int) raises -> Int:
        var s = self.tid[ty]
        var i = index_of(self.structs[s].k_traits, t)
        if i < 0:
            raise Error("evaluator: missing K")
        var v = self.structs[s].k_values[i]
        var source = self.structs[s].k_sources[i]
        if source >= 0:
            self.stats[STAT_K_SOURCE] += 1
            v += self.k_value(self.targ[ty], source)
        return v

    # ---- printing

    def block_text(self, stmts: List[Int], indent: String) -> String:
        if len(stmts) == 0:
            return String(indent, "pass\n")
        var s = String()
        for st in stmts:
            s += self.stmt_text(st, indent)
        return s^

    def stmt_text(self, st: Int, indent: String) -> String:
        var text = self.stmt_lines(st, indent)
        if has(self.marked_stmts, st):
            return text.replace("\n", String(MARK, "\n"))
        return text^

    def stmt_lines(self, st: Int, indent: String) -> String:
        ref s = self.stmts[st]
        if s.kind == S_VAR:
            return String(
                indent, "var ", s.name, " = ", self.exprs[s.e].text, "\n"
            )
        if s.kind == S_ASSIGN:
            return String(
                indent,
                self.exprs[s.target].text,
                " = ",
                self.exprs[s.e].text,
                "\n",
            )
        if s.kind == S_EXPR:
            return String(indent, "_ = ", self.exprs[s.e].text, "\n")
        if s.kind == S_USE:
            if s.e >= 0:
                return String(indent, "_use(", self.exprs[s.e].text, ")\n")
            var group = String()
            for st in s.body:
                group += self.stmt_text(st, indent)
            return group^
        var inner = String(indent, "    ")
        if s.kind == S_IF:
            var ops = materialize[CMP_OPS]()
            var text = String(
                indent,
                "if ",
                self.exprs[s.e].text,
                " ",
                ops[s.a],
                " ",
                self.exprs[s.e2].text,
                ":\n",
            )
            text += self.block_text(s.body, inner)
            text += String(indent, "else:\n")
            text += self.block_text(s.orelse, inner)
            return text^
        var text = String(indent, "for ", s.name, " in range(", s.a, "):\n")
        text += self.block_text(s.body, inner)
        return text^

    def body_text(self, b: Int, indent: String) -> String:
        ref body = self.bodies[b]
        var s = String()
        for st in body.stmts:
            s += self.stmt_text(st, indent)
        s += String(indent, "return ", self.exprs[body.ret].text, "\n")
        return s^

    def sig_text(
        self,
        m: Int,
        params: List[Int],
        ret: Int,
        names: List[String],
        self_print: Int,
    ) -> String:
        if self.methods[m].is_static:
            return String(
                "    @staticmethod\n    def ",
                self.methods[m].name,
                "(x: Int) -> ",
                self.ty_str(ret, names, self_print),
                ":\n",
            )
        var prefixes = materialize[CONV_PREFIX]()
        var s = String(
            "    def ",
            self.methods[m].name,
            "(",
            prefixes[self.methods[m].self_conv],
            "self",
        )
        for i in range(len(params)):
            s += String(
                ", ",
                prefixes[self.methods[m].convs[i]],
                "p",
                i,
                ": ",
                self.ty_str(params[i], names, self_print),
            )
        s += String(") -> ", self.ty_str(ret, names, self_print), ":\n")
        return s^

    def declarations_text(mut self) -> String:
        var s = String()
        var self_names: List[String] = ["Self"]
        var cap_names = materialize[CAP_NAMES]()
        for t in range(len(self.traits)):
            s += String("trait Tr", t, "(")
            ref parents = self.traits[t].parents
            if len(parents) == 0:
                s += String(cap_names[self.traits[t].cap], ", Deinitable")
            for i in range(len(parents)):
                if i > 0:
                    s += ", "
                s += String("Tr", parents[i])
            if self.traits[t].strengthens:
                s += ", ImplicitlyCopyable"
            s += "):\n"
            if self.traits[t].has_k:
                s += String("    comptime K", t, ": Int\n")
            for m in self.traits[t].methods:
                s += "\n"
                s += self.sig_text(
                    m,
                    self.methods[m].params,
                    self.methods[m].ret,
                    self_names,
                    -1,
                )
                if self.methods[m].body >= 0:
                    s += self.body_text(self.methods[m].body, "        ")
                else:
                    s += "        ...\n"
            s += "\n\n"
        for st in range(len(self.structs)):
            var generic = self.structs[st].generic
            var names = ["Self.T"] if generic else List[String]()
            var self_ty = self.self_type(st)
            var marked = st == self.mark_struct
            s += String("@fieldwise_init\nstruct ", self.structs[st].name)
            if generic:
                s += String("[T: Tr", self.structs[st].bound, "]")
            s += String("(", cap_names[self.structs[st].cap])
            for t in self.structs[st].traits:
                s += String(", Tr", t)
            s += String("):", MARK if marked else "", "\n")
            for f in range(len(self.structs[st].fields)):
                s += String(
                    "    var f",
                    f,
                    ": ",
                    self.ty_str(self.structs[st].fields[f], names, -1),
                    MARK if marked and self.mark_fields else "",
                    "\n",
                )
            for i in range(len(self.structs[st].k_traits)):
                s += String(
                    "    comptime K",
                    self.structs[st].k_traits[i],
                    " = ",
                )
                if self.structs[st].k_sources[i] >= 0:
                    s += String(
                        "Self.T.K", self.structs[st].k_sources[i], " + "
                    )
                s += String("(", self.structs[st].k_values[i], ")\n")
            for i in range(len(self.structs[st].impl_methods)):
                var m = self.structs[st].impl_methods[i]
                var b = self.structs[st].impl_bodies[i]
                var params = self.subst_all(
                    self.methods[m].params.copy(), [self_ty]
                )
                var ret = self.subst(self.methods[m].ret, [self_ty])
                s += "\n"
                var sig = self.sig_text(
                    m, params, ret, names, self.bodies[b].self_print
                )
                if marked and i == self.mark_impl:
                    sig = sig.replace("\n", String(MARK, "\n"))
                s += sig
                s += self.body_text(b, "        ")
            for m in self.structs[st].own:
                var b = self.methods[m].body
                s += "\n"
                s += self.sig_text(
                    m,
                    self.methods[m].params,
                    self.methods[m].ret,
                    names,
                    self.bodies[b].self_print,
                )
                s += self.body_text(b, "        ")
            s += "\n\n"
        var fn_names: List[String] = ["T", "U"]
        var prefixes = materialize[CONV_PREFIX]()
        for f in range(len(self.fns)):
            ref fd = self.fns[f]
            s += String("def ", fd.name)
            if len(fd.bounds) > 0:
                s += "["
                for i in range(len(fd.bounds)):
                    if i > 0:
                        s += ", "
                    s += String(fn_names[i], ": Tr", fd.bounds[i])
                s += "]"
            s += "("
            for i in range(len(fd.params)):
                if i > 0:
                    s += ", "
                s += String(
                    prefixes[fd.convs[i]],
                    "p",
                    i,
                    ": ",
                    self.ty_str(fd.params[i], fn_names, -1),
                )
            s += String(") -> ", self.ty_str(fd.ret, fn_names, -1), ":\n")
            s += self.body_text(fd.body, "    ")
            s += "\n\n"
        for i in range(len(self.entries)):
            s += String("def run_f", i, "(a: Int, b: Int, c: Int) -> Int:\n")
            s += self.body_text(self.entries[i], "    ")
            s += "\n\n"
        return s^


def resolve_marks(text: String) -> String:
    """Moves each line's marks to a `# MUTANT` comment at its end."""
    var out = String()
    var lines = text.split("\n")
    for i in range(len(lines)):
        var line = String(lines[i])
        if i > 0:
            out += "\n"
        if MARK in line:
            out += String(line.replace(MARK, ""), "  # MUTANT")
        else:
            out += line
    return out^


def mutant_kinds() raises -> List[Int]:
    """The mutation kinds DECL_FUZZ_MUTANTS asks for: none if it's unset,
    every kind for 1 or `all`, else the kinds named (comma-separated)."""
    var spec = getenv("DECL_FUZZ_MUTANTS")
    var out = List[Int]()
    if spec == "":
        return out^
    if spec == "1" or spec == "all":
        for k in range(N_MU):
            out.append(k)
        return out^
    var names = materialize[MU_NAMES]()
    for part in spec.split(","):
        var found = False
        for k in range(N_MU):
            if names[k] == String(part):
                out.append(k)
                found = True
        if not found:
            raise Error(String("unknown mutation kind: ", part))
    return out^


def draw_program(
    mut data: ConjectureData, kinds: List[Int]
) raises -> Tuple[String, String, String]:
    """The program, its compile-time twin, and the expected output; with
    mutation kinds, an ill-typed mutant (and no twin or output)."""
    var p = Program()
    if len(kinds) > 0:
        p.mutant = kinds[pick(data, len(kinds))]
    try:
        p.draw_declarations(data)
        p.draw_bodies(data)
        if p.mutant >= MU_MISSING:
            p.mutate_declarations(data)
    except e:
        # an expression whose `mut` places were taken by earlier arguments
        if String(e) == "STUCK":
            if getenv("DECL_FUZZ_STATS") != "":
                print("stuck")
            assume(False)
        raise e^
    if p.mutant >= 0:
        if getenv("DECL_FUZZ_STATS") != "":
            var names = materialize[MU_NAMES]()
            print(
                "mutant" if p.mutated else "unmutated",
                names[p.mutant],
            )
        if not p.mutated:  # no chance was taken
            assume(False)
    var arg_lists = List[List[Int]]()
    for _ in range(data.draw(integers(1, 3))):
        var args = List[Int]()
        for _ in range(3):
            if data.draw(booleans()):
                args.append(p.literal_values[pick(data, len(p.literal_values))])
            else:
                args.append(data.draw(integers(-20, 20)))
        arg_lists.append(args^)

    var decls = p.declarations_text()
    var program = String(PRELUDE_HEAD, RUN_TIME_RES, decls, "def main():\n")
    program += "    _ledger_init()\n"
    var comptime_program = String(
        PRELUDE_HEAD, COMPILE_TIME_RES, decls, "def main():\n"
    )
    var expected = String()
    for i in range(len(p.entries)):
        for j in range(len(arg_lists)):
            var args = String(
                "(",
                arg_lists[j][0],
                "), (",
                arg_lists[j][1],
                "), (",
                arg_lists[j][2],
                ")",
            )
            var hidden = args.replace("), (", ")), black_box((")
            program += String(
                '    print("c", ', i, ", run_f", i, "(", args, "))\n"
            )
            program += String("    _check(", i, ")\n")
            program += String(
                '    print("b", ',
                i,
                ", run_f",
                i,
                "(black_box(",
                hidden,
                ")))\n",
            )
            program += String("    _check(", i, ")\n")
            var name = String("k", i, "_", j)
            comptime_program += String(
                "    comptime ", name, " = run_f", i, "(", args, ")\n"
            )
            comptime_program += String('    print("c", ', i, ", ", name, ")\n")
            if p.mutant >= 0:
                continue  # not evaluated: it doesn't have a meaning
            var frame = List[Int]()
            for k in range(3):
                frame.append(p.new_int(arg_lists[j][k]))
            var v: Int
            try:
                v = p.vint[p.run_body(p.entries[i], frame, [])]
            except e:
                if String(e) == "STEP_LIMIT":
                    assume(False)
                raise e^
            expected += String("c ", i, " ", v, "\n")
            expected += String("b ", i, " ", v, "\n")
    if p.mutant >= 0:
        var names = materialize[MU_NAMES]()
        var text = String("# FM mutant: ", names[p.mutant], "\n", program)
        return (resolve_marks(text), String(), String())
    if getenv("DECL_FUZZ_STATS") != "":
        var line = String("stats")
        var names = materialize[STAT_NAMES]()
        for i in range(N_STATS):
            line += String(" ", names[i], "=", p.stats[i])
        print(line)
    return (program^, comptime_program^, expected^)


def process_dir(work_dir: String) raises -> String:
    """A directory of this process's own in `work_dir` (worker processes)."""
    var dir = String(work_dir, "/p", external_call["getpid", Int32]())
    _ = run(String("mkdir -p ", dir))
    return dir^


def main() raises:
    var work_dir = (
        String(argv()[1]) if len(argv()) > 1 else "build/decl_fuzz_work"
    )
    var kinds = mutant_kinds()
    var script = String(
        "examples/decl_fuzz/check_rejected.sh" if len(kinds)
        > 0 else "examples/decl_fuzz/build_and_compare.sh"
    )
    if len(argv()) > 2:
        script = String(argv()[2])
    _ = run(String("mkdir -p ", work_dir))

    def differential(
        mut data: ConjectureData,
    ) raises {imm work_dir, imm script, imm kinds}:
        var programs = draw_program(data, kinds)
        var dir = process_dir(work_dir)
        with open(String(dir, "/program.mojo"), "w") as f:
            f.write(programs[0])
        with open(String(dir, "/comptime.mojo"), "w") as f:
            f.write(programs[1])
        with open(String(dir, "/expected.txt"), "w") as f:
            f.write(programs[2])
        var verdict = run(String("bash ", script, " ", dir, " 2>&1"))
        if not verdict.startswith("OK"):
            data.note(programs[0])
            data.note(verdict)
            for name in ["program.mojo", "comptime.mojo", "expected.txt"]:
                _ = run(
                    String(
                        "cp ", dir, "/", name, " ", work_dir, "/failing_", name
                    )
                )
            # BUILD_FAIL: the generator wrote ill-typed Mojo, or the
            # compiler rejected a well-typed program; ACCEPTED: the
            # compiler accepted a mutant
            fail(String(verdict.split("\n")[0]))

    var settings = Settings(
        database=None,
        deadline=None,
        max_examples=env_int("PROPTEST_MAX_EXAMPLES", 200),
        print_blob=True,
        workers=env_int("PROPTEST_WORKERS", WORKERS),
    )
    settings.phases = Phases(explain=False)
    if getenv("DECL_FUZZ_NO_SHRINK") != "":
        settings.phases = Phases(shrink=False, explain=False)
    given_data(differential, settings)
    print("no differences")
