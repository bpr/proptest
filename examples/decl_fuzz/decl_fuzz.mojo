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
# FM is pure and every program terminates: each method and function has a
# rank, and a body calls only methods and functions of lower rank.
# The generator also evaluates the program itself (`Program.eval`, the
# reference semantics in the rules doc). The script then compares four
# results: -O0, -O3, `comptime` and the generator's. -O0 and -O3 agreeing
# on a wrong answer (a front-end bug in dispatch, substitution or
# associated constants) shows up as DIFF_EXPECTED.
#
# Build and run from the repository root:
#
#   pixi run mojo build -I . -o build/decl_fuzz \
#       examples/decl_fuzz/decl_fuzz.mojo
#   pixi run build/decl_fuzz build/decl_fuzz_work
#
# The compiler under test is $MOJO (default `mojo`); see
# build_and_compare.sh. DECL_FUZZ_NO_SHRINK=1 skips shrinking;
# PROPTEST_SEED, PROPTEST_MAX_EXAMPLES and PROPTEST_WORKERS set the seed,
# the number of programs, and the worker processes (0: one per physical
# core). The failing program is kept as failing_program.mojo in the work
# directory. A second argument replaces build_and_compare.sh (for example
# with a script that just echoes OK, to check the generator alone).

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

# type kinds
comptime INT = 0
comptime STRUCT = 1
"""A struct; generic ones carry their type argument."""
comptime PARAM = 2
"""A type parameter of the context: `T`, `U`, `Self.T` or a trait's `Self`."""

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

# what evaluation reached, for tuning the generator
comptime STAT_OWN = 0
comptime STAT_REQUIRED = 1
comptime STAT_OVERRIDE = 2
comptime STAT_DEFAULT = 3
comptime STAT_STATIC = 4
comptime STAT_GENERIC = 5
comptime STAT_K = 6
comptime STAT_K_SOURCE = 7
comptime N_STATS = 8
comptime STAT_NAMES: List[String] = [
    "own",
    "required",
    "override",
    "default",
    "static",
    "generic",
    "K",
    "K_source",
]

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


@fieldwise_init
struct TraitDecl(Copyable):
    var parents: List[Int]
    var methods: List[Int]
    """Methods declared in this trait (not its parents), static make too."""
    var has_k: Bool
    """Whether it declares `comptime K<t>: Int`."""
    var make: Int
    """Its `@staticmethod def make<t>(x: Int) -> Self`, or -1."""


@fieldwise_init
struct MethodDecl(Copyable):
    var name: String
    var trait_id: Int
    """The declaring trait, or -1 for a struct's own method."""
    var struct_id: Int
    """The struct of an own method, or -1."""
    var is_static: Bool
    var params: List[Int]
    """Parameter types, without `self`. In a trait, PARAM 0 is `Self`; in a
    generic struct, the struct's `T`."""
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
    var ret: Int
    var rank: Int
    var body: Int


@fieldwise_init
struct Body(Copyable):
    var lets: List[Int]
    """`var vK = e` bindings before the result, in order."""
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
struct Ctx(Copyable):
    """Γ, the type parameters in scope, and the rank of the body."""

    var names: List[String]
    var types: List[Int]
    var bounds: List[Int]
    var param_names: List[String]
    var rank: Int
    var self_print: Int
    var pool: List[Int]
    """The types this context draws from."""


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
    var entries: List[Int]
    """Bodies of run_f0, run_f1, ..."""
    var vtag: List[Int]
    """Values: -1 for an Int, else the struct."""
    var vint: List[Int]
    var vkids: List[List[Int]]
    var steps: Int
    var stats: List[Int]
    """Dynamic counts per STAT_* kind (DECL_FUZZ_STATS=1 prints them)."""
    var literals: List[String]
    var literal_values: List[Int]
    var int_ty: Int
    var p0_ty: Int

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
        self.entries = []
        self.vtag = []
        self.vint = []
        self.vkids = []
        self.steps = 0
        self.stats = List[Int](length=N_STATS, fill=0)
        self.literals = materialize[LITERALS]()
        self.literal_values = materialize[LITERAL_VALUES]()
        self.int_ty = 0
        self.p0_ty = 0
        self.int_ty = self.intern(INT, -1, -1)
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
        if kind == INT:
            return False
        if kind == PARAM:
            return self.refines(bounds[self.tid[ty]], t)
        for x in self.structs[self.tid[ty]].traits:
            if self.refines(x, t):
                return True
        return False

    def fields_of(mut self, ty: Int) -> List[Int]:
        if self.tkind[ty] != STRUCT:
            return []
        var s = self.tid[ty]
        var fields = self.structs[s].fields.copy()
        if self.structs[s].generic:
            return self.subst_all(fields, [self.targ[ty]])
        return fields^

    def type_pool(mut self, bounds: List[Int], n_structs: Int) -> List[Int]:
        """Int, the concrete structs, the parameters in scope, and generic
        structs over them (two levels deep)."""
        var pool: List[Int] = [self.int_ty]
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

    def unify(self, pat: Int, ty: Int, mut assign: List[Int]) -> Bool:
        var kind = self.tkind[pat]
        if kind == PARAM:
            var i = self.tid[pat]
            if assign[i] < 0:
                assign[i] = ty
                return True
            return assign[i] == ty
        if kind == INT:
            return self.tkind[ty] == INT
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
        # trait headers: parents, K, make (FJ: classes in order, so the
        # refinement relation is acyclic)
        var n_traits = data.draw(integers(1, 4))
        for t in range(n_traits):
            var parents = List[Int]()
            if t > 0:
                for _ in range(data.draw(integers(0, 2))):
                    var p = pick(data, t)
                    if not has(parents, p):
                        parents.append(p)
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
                        [self.int_ty],
                        self.p0_ty,
                        data.draw(integers(0, MAX_RANK)),
                        False,
                        -1,
                    )
                )
            var methods = List[Int]()
            if make >= 0:
                methods.append(make)
            self.traits.append(TraitDecl(parents^, methods^, has_k, make))

        # struct headers: fields over earlier structs only (acyclic, like
        # FJ's fields), conformances, associated constants
        var n_structs = data.draw(integers(1, 5))
        for s in range(n_structs):
            var generic = data.draw(integers(0, 2)) == 0
            var bound = pick(data, n_traits) if generic else -1
            var bounds = [bound] if generic else List[Int]()
            var pool = self.type_pool(bounds, s)
            var fields = List[Int]()
            if generic:
                fields.append(self.p0_ty)
            for _ in range(data.draw(integers(0 if generic else 1, 3))):
                fields.append(self.draw_type(data, pool))
            var traits = List[Int]()
            for t in range(n_traits):
                if data.draw(booleans()) and (
                    not generic or self.make_ok(t, bound)
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
                var params = List[Int]()
                for _ in range(data.draw(integers(0, 2))):
                    params.append(self.draw_sig_type(data, pool, self.p0_ty))
                self.methods.append(
                    MethodDecl(
                        String("m", m),
                        t,
                        -1,
                        False,
                        params^,
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
                var params = List[Int]()
                for _ in range(data.draw(integers(0, 2))):
                    params.append(self.draw_sig_type(data, pool, own_ty))
                self.methods.append(
                    MethodDecl(
                        String("m", m),
                        -1,
                        s,
                        False,
                        params^,
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
            for i in range(len(bounds)):
                params.append(self.intern(PARAM, i, -1))
            for _ in range(data.draw(integers(0, 2))):
                params.append(self.draw_sig_type(data, pool, own_ty))
            self.fns.append(
                FnDecl(
                    String("g", f),
                    bounds^,
                    params^,
                    self.draw_sig_type(data, pool, own_ty),
                    data.draw(integers(0, MAX_RANK)),
                    -1,
                )
            )

    # ---- bodies

    def trait_ctx(mut self, m: Int) -> Ctx:
        var t = self.methods[m].trait_id
        var rank = self.methods[m].rank
        var pool = self.type_pool([t], len(self.structs))
        var ctx = Ctx(["self"], [self.p0_ty], [t], ["Self"], rank, -1, pool^)
        for i in range(len(self.methods[m].params)):
            ctx.names.append(String("p", i))
            ctx.types.append(self.methods[m].params[i])
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
            [],
            [],
            bounds.copy(),
            ["Self.T"] if generic else List[String](),
            rank,
            self_ty if data.draw(booleans()) else -1,
            pool^,
        )
        if not self.methods[m].is_static:
            ctx.names.append("self")
            ctx.types.append(self_ty)
        var params = self.methods[m].params.copy()
        if self.methods[m].trait_id >= 0:
            params = self.subst_all(params, [self_ty])
        for i in range(len(params)):
            ctx.names.append(
                "x" if self.methods[m].is_static else String("p", i)
            )
            ctx.types.append(params[i])
        return ctx^

    def body_ret(mut self, s: Int, m: Int) -> Int:
        """Method m's result type in struct s (-1: a trait default)."""
        if s < 0 or self.methods[m].trait_id < 0:
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
        var lets = List[Int]()
        for k in range(data.draw(integers(0, 2))):
            var ty = self.draw_type(data, ctx.pool)
            lets.append(self.gen(data, ctx, ty, size - 1))
            ctx.names.append(String("v", k))
            ctx.types.append(ty)
        var r = self.gen(data, ctx, ret, size, root)
        self.bodies.append(Body(lets^, r, ctx.self_print))
        return len(self.bodies) - 1

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
            var ctx = Ctx([], [], bounds.copy(), ["T", "U"], rank, -1, pool^)
            for i in range(len(self.fns[f].params)):
                ctx.names.append(String("p", i))
                ctx.types.append(self.fns[f].params[i])
            var ret = self.fns[f].ret
            self.fns[f].body = self.gen_body(data, ctx^, ret)
        # entry points
        for _ in range(data.draw(integers(1, 4))):
            var ctx = Ctx(
                ["a", "b", "c"],
                [self.int_ty, self.int_ty, self.int_ty],
                [],
                [],
                MAX_RANK + 1,
                -1,
                self.type_pool([], len(self.structs)),
            )
            self.entries.append(
                self.gen_body(data, ctx^, self.int_ty, BODY_SIZE + 2, True)
            )

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
        if self.tkind[ty] == INT:
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

    def gen(
        mut self,
        mut data: ConjectureData,
        ctx: Ctx,
        ty: Int,
        size: Int,
        root: Bool = False,
    ) raises -> Int:
        """An expression of type ty in ctx (Γ ⊢ ? : ty). At the root of an
        entry point, only calls and associated constants, if there are any.
        """
        var kind = self.tkind[ty]
        var sub = size - 1 if size > 0 else 0
        var half = size // 2

        # T-Var, and fields of variables (so that `self.f0` is a ground
        # term for `Self.T`)
        var atom_vars = List[Int]()
        var atom_fields = List[Int]()
        for v in range(len(ctx.types)):
            if ctx.types[v] == ty:
                atom_vars.append(v)
                atom_fields.append(-1)
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                if fs[f] == ty:
                    atom_vars.append(v)
                    atom_fields.append(f)
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
                if self.tkind[r] == INT:
                    continue
                var fs = self.fields_of(r)
                for f in range(len(fs)):
                    if fs[f] == ty:
                        field_recv.append(r)
                        field_idx.append(f)
                for m in self.methods_on(r, ctx.bounds):
                    if (
                        self.methods[m].rank < ctx.rank
                        and self.method_ret(m, r) == ty
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
                if (
                    len(self.call_assignment(f, ty, ctx)) > 0
                    or len(self.fns[f].bounds) == 0
                    and self.fns[f].ret == ty
                ):
                    call_fn.append(f)

        # Unlike fj-qc, the rules aren't equally likely: a rule appears
        # in the list as many times as its weight, so that dispatch, calls
        # and associated constants are reached often. The simplest rules
        # still come first, where shrinking leads.
        var rules = List[Int]()
        if kind == INT or len(atom_vars) > 0:
            rules.append(R_ATOM)
        if kind == STRUCT:
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
        if root:
            var calls = List[Int]()
            for r in rules:
                if r == R_METHOD or r == R_CALL or r == R_K:
                    calls.append(r)
            if len(calls) > 0:
                rules = calls^
        if len(rules) == 0:
            raise Error(String("generator: no rule for ", self.cty(ty, ctx)))
        var rule = rules[pick(data, len(rules))]

        if rule == R_ATOM:
            var n = len(atom_vars)
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
            var v = atom_vars[i]
            var var_e = self.add(E_VAR, v, ctx.types[v], [], [], ctx.names[v])
            if atom_fields[i] < 0:
                return var_e
            return self.add(
                E_FIELD,
                atom_fields[i],
                ty,
                [var_e],
                [],
                String(ctx.names[v], ".f", atom_fields[i]),
            )

        if rule == R_NEW:  # T-New
            var kids = List[Int]()
            for ft in self.fields_of(ty):
                kids.append(self.gen(data, ctx, ft, sub))
            var text = String(
                self.cty(ty, ctx), "(", self.args_text(kids, 0), ")"
            )
            return self.add(E_NEW, 0, ty, kids^, [], text^)

        if rule == R_MAKE:  # static call: τ.make<t>(e)
            var m = makes[pick(data, len(makes))]
            var arg = self.gen(data, ctx, self.int_ty, sub)
            var text = String(
                self.cty(ty, ctx),
                ".",
                self.methods[m].name,
                "(",
                self.exprs[arg].text,
                ")",
            )
            return self.add(E_STATIC, m, ty, [arg], [ty], text^)

        if rule == R_BIN:
            var op = pick(data, comptime (len(BIN_OPS)))
            var l = self.gen(data, ctx, ty, half)
            var r = self.gen(data, ctx, ty, half)
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

        if rule == R_TERN:
            var op = pick(data, comptime (len(CMP_OPS)))
            var x = self.gen(data, ctx, self.int_ty, half)
            var y = self.gen(data, ctx, self.int_ty, half)
            var t = self.gen(data, ctx, ty, half)
            var e = self.gen(data, ctx, ty, half)
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

        if rule == R_FIELD:  # T-Field
            var i = pick(data, len(field_recv))
            var recv = self.gen(data, ctx, field_recv[i], sub)
            var text = String(self.exprs[recv].text, ".f", field_idx[i])
            return self.add(E_FIELD, field_idx[i], ty, [recv], [], text^)

        if rule == R_METHOD:  # T-Invk
            var i = pick(data, len(meth_recv))
            var r = meth_recv[i]
            var m = meth_id[i]
            var kids: List[Int] = [self.gen(data, ctx, r, sub)]
            for pt in self.method_params(m, r):
                kids.append(self.gen(data, ctx, pt, half))
            var text = String(
                self.exprs[kids[0]].text,
                ".",
                self.methods[m].name,
                "(",
                self.args_text(kids, 1),
                ")",
            )
            return self.add(E_METHOD, m, ty, kids^, [], text^)

        if rule == R_K:  # an associated constant: τ.K<t>
            var i = pick(data, len(k_recv))
            var text = String(self.cty(k_recv[i], ctx), ".K", k_trait[i])
            return self.add(E_K, k_trait[i], ty, [], [k_recv[i]], text^)

        # R_CALL: a free or generic function; T-UCast's counterpart is
        # passing a conforming type for a bounded parameter
        var f = call_fn[pick(data, len(call_fn))]
        var targs = List[Int]()
        var n_tp = len(self.fns[f].bounds)
        if n_tp > 0:
            targs = self.call_assignment(f, ty, ctx)
            for i in range(n_tp):
                if targs[i] < 0:
                    var ok = self.conforming(ctx, self.fns[f].bounds[i])
                    targs[i] = ok[pick(data, len(ok))]
        var params = self.fns[f].params.copy()
        if n_tp > 0:
            params = self.subst_all(params, targs)
        var kids = List[Int]()
        for pt in params:
            kids.append(self.gen(data, ctx, pt, half))
        var text = self.fns[f].name
        if n_tp > 0 and data.draw(booleans()):  # explicit type arguments
            text += "["
            for i in range(n_tp):
                if i > 0:
                    text += ", "
                text += self.cty(targs[i], ctx)
            text += "]"
        text += String("(", self.args_text(kids, 0), ")")
        return self.add(E_CALL, f, ty, kids^, targs^, text^)

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

    # ---- the reference semantics: big-step, call by value

    def new_int(mut self, x: Int) -> Int:
        self.vtag.append(-1)
        self.vint.append(x)
        self.vkids.append([])
        return len(self.vtag) - 1

    def eval(mut self, e: Int, vars: List[Int], targs: List[Int]) raises -> Int:
        self.steps += 1
        if self.steps > STEP_LIMIT:
            raise Error("STEP_LIMIT")
        var kind = self.exprs[e].kind
        var a = self.exprs[e].a
        var kids = self.exprs[e].kids.copy()
        if kind == E_LIT:
            return self.new_int(a)
        if kind == E_VAR:
            return vars[a]
        if kind == E_BIN:
            var x = self.vint[self.eval(kids[0], vars, targs)]
            var y = self.vint[self.eval(kids[1], vars, targs)]
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
            var x = self.vint[self.eval(kids[0], vars, targs)]
            var y = self.vint[self.eval(kids[1], vars, targs)]
            var c = x < y if a == 0 else (x == y if a == 1 else x != y)
            return self.eval(kids[2] if c else kids[3], vars, targs)
        if kind == E_FIELD:
            var v = self.eval(kids[0], vars, targs)
            return self.vkids[v][a]
        if kind == E_NEW:
            var ty = self.subst(self.exprs[e].ty, targs)
            var vals = List[Int]()
            for k in kids:
                vals.append(self.eval(k, vars, targs))
            self.vtag.append(self.tid[ty])
            self.vint.append(0)
            self.vkids.append(vals^)
            return len(self.vtag) - 1
        if kind == E_METHOD:
            var recv_ty = self.subst(self.exprs[kids[0]].ty, targs)
            var vals = List[Int]()
            for k in kids:
                vals.append(self.eval(k, vars, targs))
            return self.call_method(a, recv_ty, vals^)
        if kind == E_STATIC:
            var ty = self.subst(self.exprs[e].tys[0], targs)
            var vals: List[Int] = [self.eval(kids[0], vars, targs)]
            return self.call_method(a, ty, vals^)
        if kind == E_K:
            self.stats[STAT_K] += 1
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return self.new_int(self.k_value(ty, a))
        # E_CALL
        if len(self.fns[a].bounds) > 0:
            self.stats[STAT_GENERIC] += 1
        var f_targs = self.subst_all(self.exprs[e].tys.copy(), targs)
        var vals = List[Int]()
        for k in kids:
            vals.append(self.eval(k, vars, targs))
        return self.run_body(self.fns[a].body, vals^, f_targs)

    def run_body(
        mut self, b: Int, var vars: List[Int], targs: List[Int]
    ) raises -> Int:
        var lets = self.bodies[b].lets.copy()
        for l in lets:
            vars.append(self.eval(l, vars, targs))
        return self.eval(self.bodies[b].ret, vars, targs)

    def call_method(
        mut self, m: Int, recv_ty: Int, var vals: List[Int]
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
            return self.run_body(self.methods[m].body, vals^, targs)
        if self.methods[m].is_static:
            self.stats[STAT_STATIC] += 1
        var i = index_of(self.structs[s].impl_methods, m)
        if i >= 0:
            self.stats[
                STAT_OVERRIDE if self.methods[m].has_default else STAT_REQUIRED
            ] += 1
            return self.run_body(self.structs[s].impl_bodies[i], vals^, targs)
        self.stats[STAT_DEFAULT] += 1
        return self.run_body(self.methods[m].body, vals^, [recv_ty])

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

    def body_text(self, b: Int, indent: String) -> String:
        var s = String()
        ref body = self.bodies[b]
        for k in range(len(body.lets)):
            s += String(
                indent, "var v", k, " = ", self.exprs[body.lets[k]].text, "\n"
            )
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
        var s = String("    def ", self.methods[m].name, "(self")
        for i in range(len(params)):
            s += String(
                ", p", i, ": ", self.ty_str(params[i], names, self_print)
            )
        s += String(") -> ", self.ty_str(ret, names, self_print), ":\n")
        return s^

    def declarations_text(mut self) -> String:
        var s = String("from std.benchmark import black_box\n\n\n")
        var self_names: List[String] = ["Self"]
        for t in range(len(self.traits)):
            s += String("trait Tr", t, "(")
            ref parents = self.traits[t].parents
            if len(parents) == 0:
                s += "ImplicitlyCopyable, Deinitable"
            for i in range(len(parents)):
                if i > 0:
                    s += ", "
                s += String("Tr", parents[i])
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
            s += String("@fieldwise_init\nstruct ", self.structs[st].name)
            if generic:
                s += String("[T: Tr", self.structs[st].bound, "]")
            s += "("
            ref traits = self.structs[st].traits
            if len(traits) == 0:
                s += "ImplicitlyCopyable"
            for i in range(len(traits)):
                if i > 0:
                    s += ", "
                s += String("Tr", traits[i])
            s += "):\n"
            for f in range(len(self.structs[st].fields)):
                s += String(
                    "    var f",
                    f,
                    ": ",
                    self.ty_str(self.structs[st].fields[f], names, -1),
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
                s += self.sig_text(
                    m, params, ret, names, self.bodies[b].self_print
                )
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
                    "p", i, ": ", self.ty_str(fd.params[i], fn_names, -1)
                )
            s += String(") -> ", self.ty_str(fd.ret, fn_names, -1), ":\n")
            s += self.body_text(fd.body, "    ")
            s += "\n\n"
        for i in range(len(self.entries)):
            s += String("def run_f", i, "(a: Int, b: Int, c: Int) -> Int:\n")
            s += self.body_text(self.entries[i], "    ")
            s += "\n\n"
        return s^


def draw_program(
    mut data: ConjectureData,
) raises -> Tuple[String, String, String]:
    """The program, its compile-time twin, and the expected output."""
    var p = Program()
    p.draw_declarations(data)
    p.draw_bodies(data)
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
    var program = String(decls, "def main():\n")
    var comptime_program = String(decls, "def main():\n")
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
            var vals = List[Int]()
            for k in range(3):
                vals.append(p.new_int(arg_lists[j][k]))
            var v: Int
            try:
                v = p.vint[p.run_body(p.entries[i], vals^, [])]
            except e:
                if String(e) == "STEP_LIMIT":
                    assume(False)
                raise e^
            expected += String("c ", i, " ", v, "\n")
            expected += String("b ", i, " ", v, "\n")
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
    var script = (
        String(argv()[2]) if len(argv())
        > 2 else "examples/decl_fuzz/build_and_compare.sh"
    )
    _ = run(String("mkdir -p ", work_dir))

    def differential(
        mut data: ConjectureData,
    ) raises {imm work_dir, imm script}:
        var programs = draw_program(data)
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
            # compiler rejected a well-typed program
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
