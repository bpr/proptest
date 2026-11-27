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
# Near misses (DECL_FUZZ_NEAR=1, or =kind,kind) are the converse: valid
# programs, each with one construct close to an error (NR_*: disjoint `mut`
# fields, aliased read arguments, a move then a reinitialization, `f(x^,
# x.copy())`, `_ = x^` then a use of x), marked `# NEAR`. They are checked
# like well-typed programs, so a BUILD_FAIL is a false rejection.
#
# The path kinds of both (maybe_moved and mut_uninit mutants; maybe_moved,
# reinit_paths and mut_reinit near misses) leave a variable initialized on
# some paths only after an `if`: a plan the `if` draws for it moves or
# reinitializes it in some of its branches (`draw_plan`). The deferred
# kinds (the uninit mutant, the deferred near miss) declare a variable
# without a value (`var x: T`) and assign it in some branches of an `if`,
# or in a loop's body. An `if` may end one of its branches with an early
# `return` (more often for the ret_uninit mutant and the early_return near
# miss, which a plan makes as for the path kinds). Inside a loop the exit
# can also be `break` or `continue` (the break_moved mutant and loop_exit
# near miss move a variable from outside the loop before one), and a third
# of the loops are `while` loops with a counter. The partial kinds move one
# field out of a variable (`var v = x.f^`): the near miss reassigns the
# field before x is used again, the mutant uses x first. Half
# of the `Movable` and `Copyable` structs are counted: they have their
# own `__init__`, copy constructor and `__deinit__`, which keep the same
# ledger as `Res`. Some methods take `deinit self` (called on `x^`, a
# copy or a new value); a counted struct's call `_died()` before each
# return, since `__deinit__` doesn't run. The deinit near misses move a
# field out of self, or self itself, at the end of one and leave it moved.
# Half of the fields have an accessor `def fK_ref(ref self) ->
# ref[self.fK] T`, and blocks declare `ref rN = <place>` bindings: both
# are other spellings of a place the generator tracks (`spell`), used
# only where the place itself would be, and never moved; the evaluator
# ignores the difference. The ref mutants declare an accessor with the
# wrong origin, move through a ref, or assign through a temporary's
# accessor; the ref_reinit near miss uses a binding after its origin is
# moved and reinitialized. A quarter of the other structs have a value
# parameter (`struct V[n: Int]`), used with one or two values (`V[3]`,
# each occurrence spelled as some expression equal to it, `V[(1 + 2)]`,
# which Mojo folds) and read as `V[3].n` or `Self.n`, also in constants
# (`comptime K0 = Self.n + (5)`). A third of the functions have a value
# parameter too, `def gN[n: Int](p0: V[n], ...)`, which Mojo infers from
# the first argument; their signatures and bodies, and the methods of V,
# also use `V[n + 1]` and `V[n - 1]` (spelled `1 + n`, `(n + 2) + (-1)`,
# ...), so a call `g(x)` with x: V[n - 1] in another function has
# `V[(n - 1) + 1]` for `V[n]`. The value mutant writes another value
# where one is expected (in a type, or explicitly in a call,
# `g0[4](V[3](...))`); the value_expr near miss writes Self as
# `V[Self.n + 0]`, or any `V[n]` as `V[n * 1]` or another equal
# expression.
#
# A quarter of the methods, in traits and in structs, are generic, `def
# m[U: TrN](self, p0: U, ...)`: U is inferred from the first argument,
# or written (`x.m[S1](...)`), and a struct's implementation repeats the
# bound. The bound mutant writes a U that doesn't conform; the sig mutant
# may give an implementation another bound; the rename near miss calls
# an implementation's parameter W.
#
# A third of the generic structs conform to one more trait conditionally,
# `B[T: Tr0](Tr1 where conforms_to(T, Tr2))`, and gate the methods only
# that conformance needs with the same `where conforms_to(Self.T, Tr2)`
# (half the time); a quarter of a function's type parameters need a
# `where conforms_to(T, TrN)`. `conforms` checks the condition, through
# a type parameter's bound too. The where mutant breaks a condition (a
# gated call on `B[X]`, `B[X]` for a bound only the conditional
# conformance gives, a function's `where`); where_impl gates an
# implementation by a stricter condition; the where near miss is a gated
# call whose condition holds.
#
# A third of the traits declare an associated type, `comptime E0: Tr1`,
# which their signatures use as `Self.E0`; a conforming struct binds it
# (`comptime E0 = S2`, `Self.T` or Self), and generic code uses `T.E0`,
# `Self.T.E0` (also as field types) with Tr1's methods, static methods
# and constants. A type `X.E0` is normalized to the binding as soon as X
# is a struct. The assoc mutant binds a type that doesn't conform to the
# bound (and the missing mutant may leave a binding out); the assoc near
# miss writes one struct's binding as `Self.E0` throughout its
# declarations. The bound's own associated types give `T.E0.E1` (and
# `Self.T.E0.E1`, `Self.E0.E1`), and substitution deeper ones. Methods
# can also take a value parameter, `def m[k: Int](self, p0: V[k], ...)`,
# or both, `def m[U: TrN, k: Int](self, p0: U, p1: V[k], ...)`, which
# calls write positionally, U alone, `k=` alone or both by keyword; the
# own2 mutant writes them in the wrong order, `x.m[3, S1]`, the near
# miss by keyword with k first, `x.m[k=3, U=S1]`.
#
# Half of the functions with a value parameter constrain it, `where n + 1
# > 2 and n <= 4` (with perhaps a `comptime assert n - 1 >= 0` the
# `where` implies at the start of the body). Mojo checks a call with a
# value; for a symbolic one (`V[n + 1]` in a function over n) it needs
# evidence, a known proposition equal to the one needed once both are in
# a canonical form (`1 + n > 2` is `n + 1 >= 3`, but `n >= 3` doesn't give
# `n >= 1`), which `vw_holds` models; half of the propositions are ones
# other functions need, so that such calls are possible. The vwhere
# mutant breaks one (a value that fails it, or a symbolic one without
# evidence); the near miss is a call only an assert gives evidence for.
# A quarter of the value parameters can't be inferred, `def g0[n:
# Int](p0: V[n + 1])`: calls write the value, `g0[2](V[3](...))`, and the
# infer mutant leaves it out. A sixth of the functions also take a type
# parameter no parameter mentions, `def g0[T: Tr0, W: Tr1](p0: T) -> W`
# (its values come from W's make), which calls write, all of them or
# `g0[W=S1](x)`; the infer mutant leaves it out too. The body of a
# function over n can test a proposition, `comptime if n + 1 >= 3:`
# (outer variables are read-only in its branches), which the first
# branch knows; and a quarter of a valued struct's own methods have a
# `where` on `Self.n` too, which its receivers have to meet.
#
# Exceptions: half of the functions raise, `raises` (Error) or `raises
# Xk` (X0, X1 are counted error types with a `code`), with `if c: raise
# Xk(e)` in their bodies. A call of a raising function goes only where
# its error is caught or propagates: a `try` body, or a function raising
# Error or the same Xk. `try` statements (with `raise` in their bodies
# too) get handlers for exactly the types their bodies raise: typed
# `except Xk __as eN:` (reading `eN.code`) and perhaps a last `except:`
# for the rest (always for Error, which an error leaving a `raises`
# function becomes). Outer variables are read-only in a `try`. The
# unhandled mutant leaves a handler out; raise_ctx calls a raising
# function where nothing catches it; raise_type raises another type than
# declared; the unreachable near miss adds a handler that can't run.
#
# A third of the methods raise too, in traits and structs; a struct's
# implementation of a raising trait method may raise nothing instead, and
# calls on the struct then needn't handle anything (raise_impl: one
# raising what the trait doesn't allow). Half the programs have X2, an
# error carrying a struct value `val`. Half the bare handlers bind the
# error, `except eN:` (an Error), and a third of the handlers with a
# binding re-raise it, `raise eN^`. `try` statements get `else:` and
# `finally:` clauses a quarter of the time each (try_scope uses a body's
# variable in them; try_move moves an outer one in `else` and uses it in
# `finally`, and the near miss reinitializes it first).
#
# Patterns: bodies have `match` statements (on a variable, a temporary
# struct or an Int, with guards, perhaps ending with `case _:`), `if`
# statements whose semicolon-separated clauses mix comparisons and `case
# <pattern> = <subject>` (each clause seeing the bindings of those
# before it), `guard <clauses> else:` with an `else` that exits, and
# `var (bA, bB) = (e1, e2)`. A struct pattern names some of the fields
# (`S1(f0=b3, f2=(-1) | 7)`); a field's pattern is `_`, a name, `var
# name` (an ImplicitlyCopyable copy), a literal, `l1 | l2`, `== e`, or a
# struct pattern. A tuple pattern (on a tuple of temporaries) moves its
# elements into `var` names. A name in a variable subject's pattern is
# another spelling of the field's place, read-only (Mojo binds a
# reference: a later assignment to the variable shows through it), so it
# goes with the `ref` bindings (`Ctx.ref_ro`); on a temporary it's a read
# local. The pattern mutants name a field the struct doesn't have
# (pat_field), match another struct type (pat_type), use a binding out
# of its scope (pat_scope), let a `guard`'s `else` fall through
# (guard_fall), or bind a field that isn't ImplicitlyCopyable with `var`
# (pat_var).
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
# DECL_FUZZ_REPRODUCE=<blob> replays a failure from the `reproduce=` blob
# it printed (with the same DECL_FUZZ_MUTANTS or DECL_FUZZ_NEAR);
# DECL_FUZZ_FORK=1 runs each test case in a child process, so that a crash
# of the generator itself is shrunk like a failure; DECL_FUZZ_STATS=1
# prints what evaluation reached in each program (for
# mutants, its kind, whether it got the mutation, and its chances);
# PROPTEST_SEED, PROPTEST_MAX_EXAMPLES and PROPTEST_WORKERS set the seed,
# the number of programs, and the worker processes (0: one per physical
# core). The failing program is kept as failing_program.mojo in the work
# directory. Known crashes (known_crashes.txt) give a KNOWN verdict,
# which isn't a failure.
#
# A campaign (DECL_FUZZ_LOG=<file>) goes on past failures: each program's
# verdict's first line is appended to the file (GEN_ERROR for an error in
# the generator), and each case that isn't OK is kept in <file>.bad/ (or
# <file>.known/), with its verdict; campaign.sh runs rounds of them.
#
# A second argument replaces build_and_compare.sh or
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
comptime MAX_NEST = 24
"""How deep argument lists nest in an expression (deeper is STUCK)."""

# type kinds
comptime INT = 0
comptime STRUCT = 1
"""A struct; generic ones carry their type argument."""
comptime PARAM = 2
"""A type parameter of the context: `T`, `U`, `Self.T` or a trait's `Self`."""
comptime RES = 3
"""`Res`, the prelude's counted resource (Copyable, one Int field `val`)."""
comptime VAL = 4
"""A comptime Int, the argument of a struct with a value parameter
(`struct V[n: Int]`): tid is the value. Not a type of values."""
comptime OFF = 5
"""A value parameter plus a constant, `n + c` (as the argument of a
struct with a value parameter): tid is c (never 0), targ the PARAM n."""
comptime HOLE = 6
"""A generic method's own type parameter `U` not chosen yet, in its
signature instantiated for a receiver: a pattern for `match_hole`."""
comptime ERR = 8
"""An error type `X<tid>` (a counted struct with a field `code`, and X2
also `val`, of a struct type: Program.carry_ty), the type of a typed
`except Xk __as e:` handler's binding; tid -2 is Error, a bare `except
e:` handler's. Not in any pool: its values are only raised and caught."""
comptime N_ERR = 2
"""How many error types a program declares at least (X0, X1; X2 when
Program.carry_ty is set, Program.n_err)."""
comptime ASSOC = 7
"""An associated type `X.E<t>` (trait t declares `comptime E<t>: TrU`):
tid is t, targ the owner X, a type parameter or another ASSOC (with a
struct owner it's normalized to the struct's binding, `assoc`)."""

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
comptime CONV_DEINIT = 3
"""`deinit self`: a consuming method (only for `self`)."""
comptime CONV_PREFIX: List[String] = ["", "mut ", "var ", "deinit "]

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
comptime E_FMOVE = 12
"""`x.f^`, a field moved out (kids: the place)."""
comptime E_VALN = 13
"""`V[k].n` or `Self.n`: a value parameter (tys[0] is the struct type)."""

# statement kinds
comptime S_VAR = 0
comptime S_ASSIGN = 1
comptime S_EXPR = 2
comptime S_IF = 3
comptime S_FOR = 4
comptime S_USE = 5
"""`_use(v)`: a read with no effect (the workaround in `gen_stmt`)."""
comptime S_RETURN = 6
"""An early `return e`, the last statement of a branch of an `if`."""
comptime S_BREAK = 7
"""`break`, the last statement of a branch of an `if` in a loop."""
comptime S_CONTINUE = 8
"""`continue`, likewise."""
comptime S_REF = 9
"""`ref rN = <place>`: a binding that is another spelling of the place
(the evaluator ignores it)."""
comptime S_RAISE = 10
"""`raise Xk(e)`: a = k (the error type), e = the code, e2 = X2's value
(else -1); or a re-raise `raise eN^` (name eN) of the handler binding in
slot target (else -1), a = its type (-2 for Error)."""
comptime S_TRY = 11
"""`try:` body, then handlers (orelse, S_HANDLER statements); a = 1 if
its line is marked (an unhandled mutant)."""
comptime S_HANDLER = 12
"""`except Xk __as eN:` (target k, name eN), `except:` (target -1), or
`except eN:` (target -1, e2 = 1: an Error binding); a = 1 for an
unreachable handler (marked: the near miss). Also a `try`'s `else` and
`finally` clauses, last (target H_ELSE, H_FINALLY)."""
comptime H_ELSE = -3
comptime H_FINALLY = -4
comptime S_CIF = 13
"""`comptime if <prop>:` over the function's value parameter (a = its
prop_key, name = its text), with body and orelse; outer variables are
read-only in both."""
comptime S_MATCH = 14
"""`match <subject>:`, the subject a variable (target: its slot; name: its
name) or an expression (e), with its cases in body (S_CASE)."""
comptime S_CASE = 15
"""A case of a `match` (a = its clause set: the pattern, perhaps then a
guard), with its body."""
comptime S_IFC = 16
"""`if <clauses>:` with semicolon-separated clauses, Boolean ones and
`case <pattern> = <subject>` (a = the clause set), body and orelse."""
comptime S_GUARD = 17
"""`guard <clauses> else:` (a = the clause set), with orelse, which exits;
the bindings stay in scope after it."""
comptime S_DESTR = 18
"""`var (bA, bB) = (e1, e2)` (a = the clause set: a tuple of `var`
bindings)."""

# patterns (PatNode.kind)
comptime PK_WILD = 0
comptime PK_BIND = 1
"""A name: a read-only `ref` binding to a field of a variable subject
(push False), or a read local holding the value (push True)."""
comptime PK_VAR = 2
"""`var name`: an owned local (a copy, or moved out of a tuple)."""
comptime PK_LIT = 3
"""An Int literal (a: its index in LITERALS)."""
comptime PK_OR = 4
"""`l1 | l2`: literals a and b."""
comptime PK_EQ = 5
"""`== e` (a: the expression)."""
comptime PK_STRUCT = 6
"""`Head(f=p, ...)` (name: the head): fields and their patterns, kids."""
comptime PK_TUPLE = 7
"""`(p, ...)`: the elements' patterns, kids."""

# clauses of an `if`, `guard` or `case`
comptime CL_BOOL = 0
comptime CL_CASE = 1

# what executing a statement did, for the evaluator
comptime SIG_NONE = 0
comptime SIG_RETURN = 1
comptime SIG_BREAK = 2
comptime SIG_CONTINUE = 3

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
comptime R_VALN = 9

# what an `if` does to one variable, for the path-dependent mutants and
# near misses: its branches move it (it was live), or reinitialize it (it
# was moved), in the then branch, the else branch, or both
comptime PLAN_MOVE = 0
comptime PLAN_REINIT = 1
comptime BR_THEN = 0
comptime BR_ELSE = 1
comptime BR_BOTH = 2
comptime PRE_NONE = 0
comptime PRE_MOVE = 1
"""The plan's variable is moved just before the `if`."""
comptime PRE_DECL = 2
"""The plan's variable is declared without a value just before the `if`."""

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
comptime STAT_RETURN = 14
comptime STAT_BREAK = 15
"""`break` and `continue`."""
comptime STAT_DEINIT = 16
"""Calls of `deinit self` methods."""
comptime STAT_REF = 17
"""Places evaluated that are spelled through a `ref`: a binding or an
accessor."""
comptime STAT_VALUE = 18
"""Value parameters read (`Self.n`, `V[k].n`, `Self.n` in a constant)."""
comptime STAT_VALUE_CALL = 19
"""Calls of functions with a value parameter (`def gN[n: Int](p0:
V[n])`)."""
comptime STAT_GENERIC_METHOD = 20
"""Calls of generic methods (`def m[U: Tr0](self, p0: U)`)."""
comptime STAT_WHERE = 21
"""Calls of methods gated by a struct's condition, and of functions with
a `where` clause."""
comptime STAT_ASSOC = 22
"""Methods, static methods and constants used through an associated type
(`T.E0.m1()`, `Self.E0.make1(x)`, `T.E0.K1`)."""
comptime STAT_RAISE = 23
"""`raise` statements executed."""
comptime STAT_CATCH = 24
"""Handlers run."""
comptime STAT_VWHERE = 25
"""Calls of functions with a `where` on their value parameter."""
comptime STAT_NESTED = 26
"""Values of nested associated types (`T.E0.E1`) made or read."""
comptime STAT_OWN2 = 27
"""Calls of methods with two parameters of their own."""
comptime STAT_CIF = 28
"""`comptime if` statements executed."""
comptime STAT_FINALLY = 29
"""`finally` clauses run."""
comptime STAT_ELSE = 30
"""`try` statements' `else` clauses run."""
comptime STAT_RERAISE = 31
"""Errors re-raised (`raise e^`)."""
comptime STAT_RAISING_METHOD = 32
"""Errors raised out of a method."""
comptime STAT_CARRY = 33
"""X2 errors (carrying a struct) raised."""
comptime STAT_MATCH = 34
"""`match`, `if` with a `case` clause, and `guard` statements executed."""
comptime STAT_PATTERN = 35
"""Patterns that matched (a `case` run, a clause that held)."""
comptime STAT_GUARD = 36
"""`guard` statements whose `else` ran."""
comptime N_STATS = 37
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
    "return",
    "break",
    "deinit",
    "ref",
    "value",
    "value_call",
    "generic_method",
    "where",
    "assoc",
    "raise",
    "catch",
    "vwhere",
    "nested",
    "own2",
    "cif",
    "finally",
    "else",
    "reraise",
    "raising_method",
    "carry",
    "match",
    "pattern",
    "guard_exit",
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
comptime MU_MAYBE_MOVED = 13
"""A use, after an `if`, of a variable moved (or reinitialized) in only
some of its branches."""
comptime MU_MUT_UNINIT = 14
"""A `mut` argument moved out and not reinitialized on some path to the
return."""
comptime MU_UNINIT = 15
"""A use of a variable declared without a value (`var x: T`) and assigned
in only some branches of an `if`, or in a loop's body."""
comptime MU_RET_UNINIT = 16
"""An early `return` with a `mut` argument moved out."""
comptime MU_BREAK_MOVED = 17
"""A variable from outside a loop moved before a `break`, then used after
the loop."""
comptime MU_PARTIAL_USE = 18
"""A field moved out (`var v = x.f^`), then a use of x or x.f before the
field is reassigned."""
comptime MU_REF_ORIGIN = 19
"""A field accessor declared with another origin (`ref[self]`, or another
field's) than the field it returns."""
comptime MU_REF_MOVE = 20
"""`^` on a place spelled through a `ref` (`rN^`, `x.f0_ref()^`)."""
comptime MU_REF_RVALUE = 21
"""An assignment through an accessor of a temporary (`T(...).f0_ref() =
e`), which is immutable."""
comptime MU_VALUE = 22
"""A value of a struct with a value parameter, with another value
(`V[4](...)` or `V[Self.n + 1](...)`), where `V[3]` or `Self` is
expected, or a call of a function with a value parameter with another
value given explicitly (`g0[4](V[3](...))`)."""
comptime MU_WHERE = 23
"""A condition that doesn't hold: a call of a gated method (`def m(self)
where conforms_to(Self.T, TrN)`) on `B[X]` with X not conforming to
TrN; `B[X]` as a type argument whose bound only its conditional
conformance would give; or a type argument that fails a function's
`where`."""
comptime MU_WHERE_IMPL = 24
"""A struct's implementation of a method its conditional conformance
needs, gated by a stricter condition than the conformance's."""
comptime MU_ASSOC = 25
"""A struct binding an associated type to a type that doesn't conform to
its bound (`comptime E0 = S2` for `comptime E0: Tr1`)."""
comptime MU_UNHANDLED = 26
"""A `try` without a handler for one of the error types its body raises
(it has typed handlers only): "unhandled error types in try body"."""
comptime MU_RAISE_CTX = 27
"""A call of a raising function where nothing catches its error (a
function that doesn't raise, or raises another typed error)."""
comptime MU_RAISE_TYPE = 28
"""In a function that `raises Xk`, `raise Xj(...)` with j != k."""
comptime MU_VWHERE = 29
"""A call of a function with a `where` on its value parameter (`where n
>= 2`) that breaks it: with a value that fails it ("violated
constraint"), or with a symbolic one (`V[n + 1]`) for which the caller
knows no equal proposition ("lacking evidence"), even one implying it
(`n >= 3` doesn't give `n >= 1`)."""
comptime MU_INFER = 30
"""A call that leaves out the value of a parameter Mojo can't infer
(`g0(x)` for `def g0[n: Int](p0: V[n + 1])`): "it depends on an
unresolved parameter"; or the type of one no parameter mentions (`def
g0[T: Tr0, W: Tr1](p0: T) -> W`): "failed to infer parameter 'W'"."""
comptime MU_OWN2 = 31
"""A call of a method with two parameters of its own, `[U: TrN, k: Int]`,
that writes them in the wrong order, `x.m[3, S1](...)`: "parameter 'U'
has 'TrN' type, but value has type 'IntLiteral[3]'"."""
comptime MU_RAISE_IMPL = 32
"""A struct's implementation of a trait method that raises other than the
trait's declaration allows (it may raise the same, or nothing): `raises
X1` for `raises X0`, `raises X0` for `raises`, or raising for a method
that doesn't: "does not implement all requirements"."""
comptime MU_TRY_SCOPE = 33
"""A use, in a `try` statement's `else` or `finally` clause, of a
variable the `try` body declared: "use of unknown declaration"."""
comptime MU_TRY_MOVE = 34
"""An outer variable moved in a `try` statement's `else` clause, then
used in its `finally`: "use of uninitialized value"."""
comptime MU_PAT_FIELD = 35
"""A struct pattern naming a field its struct doesn't have: "'z' is not a
field of 'S1'"."""
comptime MU_PAT_TYPE = 36
"""A struct pattern for another type than its subject's: "cannot match
value of type 'S1' against pattern type 'S2'"."""
comptime MU_PAT_SCOPE = 37
"""A pattern's binding used out of its scope: in the `else` of an `if`
whose clause binds it, or of a `guard`: "use of unknown declaration"."""
comptime MU_GUARD_FALL = 38
"""A `guard` whose `else` falls through: "guard 'else' block must not
fall through"."""
comptime MU_PAT_VAR = 39
"""A `var` binding of a struct's field that isn't `ImplicitlyCopyable`
(it would be a copy): "cannot be implicitly copied"."""
comptime N_MU = 40
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
    "maybe_moved",
    "mut_uninit",
    "uninit",
    "ret_uninit",
    "break_moved",
    "partial_use",
    "ref_origin",
    "ref_move",
    "ref_rvalue",
    "value",
    "where",
    "where_impl",
    "assoc",
    "unhandled",
    "raise_ctx",
    "raise_type",
    "vwhere",
    "infer",
    "own2",
    "raise_impl",
    "try_scope",
    "try_move",
    "pat_field",
    "pat_type",
    "pat_scope",
    "guard_fall",
    "pat_var",
]
comptime MU_ODDS = 6
"""Each chance to apply the mutation is taken 1 time in MU_ODDS."""
comptime MARK = "@@M@@"
"""In generated text, marks the line of the mutation."""

# Near misses (DECL_FUZZ_NEAR=1): well-typed programs, each with one
# construct of a kind drawn first that is valid but close to an error; the
# compiler must accept them and agree with the evaluator. Marked `# NEAR`.
comptime NR_DISJOINT = 0
"""`mut` (or read) arguments that are disjoint fields of one variable."""
comptime NR_READ_ALIAS = 1
"""Read arguments overlapping each other, or a read receiver."""
comptime NR_REINIT = 2
"""A variable moved, then reinitialized (in a loop: in one iteration)."""
comptime NR_MOVE_COPY = 3
"""`f(x^, x.copy())`: later arguments use x, which moves at the call."""
comptime NR_DISCARD_MOVE = 4
"""`_ = x^`, which keeps x alive, then a use of x."""
comptime NR_MAYBE_MOVED = 5
"""A variable moved in some branches of an `if`, then reinitialized, or
not used again (destroyed on the other paths)."""
comptime NR_REINIT_PATHS = 6
"""A moved variable reinitialized in both branches of an `if` (or in one,
then after the `if`), then used."""
comptime NR_MUT_REINIT = 7
"""A `mut` argument moved out and reinitialized on every path to the
return."""
comptime NR_DEFERRED = 8
"""A variable declared without a value (`var x: T`), assigned in both
branches of an `if` (or in one, then after it; or in a loop's body), then
used; or assigned in one branch and not used again."""
comptime NR_EARLY_RETURN = 9
"""An `if` whose returning branch is the one that leaves a variable moved
(or unassigned), then a use of it after the `if`."""
comptime NR_LOOP_EXIT = 10
"""A variable from outside a loop moved before a `break` (then assigned
after the loop and used, or not used again), or moved and reinitialized
before a `continue`."""
comptime NR_PARTIAL_MOVE = 11
"""A field moved out (`var v = x.f^`), perhaps other statements, then the
field reassigned (perhaps in both branches of an `if`) and x used."""
comptime NR_DEINIT_DROP = 12
"""At the end of a `deinit self` method, a field moved out of self and not
reassigned (an error in any other method)."""
comptime NR_DEINIT_MOVE = 13
"""At the end of a `deinit self` method, self moved out whole (`var v =
self^`) and not reassigned (an error for a `mut` argument)."""
comptime NR_REF_REINIT = 14
"""`ref rN = x` (or a field of x), x moved and reinitialized, then a use
of rN: the binding is to the place, not to the value."""
comptime NR_VALUE_EXPR = 15
"""In a struct with a value parameter, a value of Self written with an
equal expression (`V[Self.n + 0](...)`, `V[0 + Self.n]`, ...); and
anywhere, a type with a value parameter as its argument written so
(`V[n * 1]`, in a signature too)."""
comptime NR_RENAME = 16
"""A struct's implementation of a generic trait method names its type
parameter `W` where the trait says `U`."""
comptime NR_WHERE = 17
"""A call of a gated method on `B[X]` with X conforming to the condition
(often through a refinement, or a type parameter's bound)."""
comptime NR_ASSOC = 18
"""In a struct's declarations and bodies, a type its associated type is
bound to written `Self.E<t>`."""
comptime NR_UNREACHABLE = 19
"""A handler that can't be reached (a type caught before, or not raised,
or after `except:`), which Mojo only warns about; its body doesn't use
its binding (DECL_FUZZ_NO_UNREACHABLE_WORKAROUND=1 lets it)."""
comptime NR_VWHERE = 20
"""A call whose `where` on a value parameter only a `comptime assert`
gives evidence for: the assert, at the start of the caller's body, is
implied by the caller's own `where` but isn't equal to any of it (`where
n >= 3` and `comptime assert n - 1 >= 0`)."""
comptime NR_OWN2 = 21
"""The same call with both by keyword, k first: `x.m[k=3, U=S1](...)`."""
comptime NR_TRY_MOVE = 22
"""The try_move mutant's `else` reinitializes the variable after moving
it, so that the `finally` can use it."""
comptime N_NR = 23
comptime NR_NAMES: List[String] = [
    "disjoint",
    "read_alias",
    "reinit",
    "move_copy",
    "discard_move",
    "maybe_moved",
    "reinit_paths",
    "mut_reinit",
    "deferred",
    "early_return",
    "loop_exit",
    "partial_move",
    "deinit_drop",
    "deinit_move",
    "ref_reinit",
    "value_expr",
    "rename",
    "where",
    "assoc",
    "unreachable",
    "vwhere",
    "own2",
    "try_move",
]
comptime MARK_NEAR = "@@N@@"
"""In generated text, marks the line of the near miss."""

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


def raises_text(r: Int) -> String:
    """A signature's ` raises` clause for FnDecl.raise_ty r."""
    if r == -2:
        return " raises"
    if r >= 0:
        return String(" raises X", r)
    return ""


comptime PRELUDE_HEAD = """from std.benchmark import black_box
from std.ffi import external_call


def _use[T: AnyType](x: T):
    pass


"""

comptime RUN_TIME_RES = """comptime _LEDGER = 0x100000000000


def _live() -> Pointer[Int, MutUntrackedOrigin]:
    \"\"\"The number of live `Res` values, at a fixed address (no globals).\"\"\"
    return Pointer[Int, MutUntrackedOrigin](unsafe_from_address=_LEDGER)


def _ledger_init():
    # PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE
    # (an address mmap doesn't hand out: one taken would make the counts
    # land in other memory)
    var at = external_call["mmap", Int](_LEDGER, 4096, 3, 0x100022, -1, 0)
    if at != _LEDGER:
        print("LEDGER_MAP_FAILED")
        external_call["exit", NoneType](3)


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


def _born():
    _live()[] += 1


def _died():
    _live()[] -= 1


"""

comptime COMPILE_TIME_RES = """def _born():
    pass


def _died():
    pass


struct Res(Copyable):
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


def draw_conv(mut data: ConjectureData, mut_often: Bool = False) raises -> Int:
    """Read 1/2, `var` 1/3, `mut` 1/6 of the time.

    A call with a `mut` argument goes only at the root of a statement, so
    `mut` arguments would otherwise rule out most calls. With mut_often
    (for mutants that need `mut` arguments), read 1/3, `var` 1/6, `mut`
    1/2."""
    var c = data.draw(integers(0, 5))
    if mut_often:
        return CONV_READ if c <= 1 else (CONV_VAR if c == 2 else CONV_MUT)
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
    var assoc: Int
    """The bound of its associated type `comptime E<t>: TrU` (U), or -1."""


@fieldwise_init
struct Prop(Copyable):
    """A proposition about a value parameter n: `n + c >= k` (ge) or `n + c
    <= k`. Mojo compares them symbolically, as this canonical form: `n >
    k - 1` is `n >= k`, and `1 + n` is `n + 1`, but `n - 1 >= 0` isn't
    `n >= 1`."""

    var c: Int
    var ge: Bool
    var k: Int
    var form: Int
    """How it's written (prop_text)."""


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
    var mbound: Int
    """For a generic method, the bound of its own type parameter `U`
    (PARAM 1; its first parameter has type U), else -1."""
    var mvalue: Int
    """For a method with a value parameter `k` instead (PARAM 1, `[k:
    Int]`; its first parameter has type `V[k]`), the struct V, else -1.
    With both, the method has two parameters of its own, `[U: TrN, k:
    Int]` (PARAM 1 and 2), and its first two parameters are U and
    `V[k]`."""
    var vwhere: List[Prop]
    """For an own method of a struct with a value parameter, the
    propositions about `Self.n` (PARAM 0) in its `where`."""
    var raise_ty: Int
    """What it raises (as FnDecl.raise_ty). A struct's implementation of a
    trait's may raise nothing instead (StructDecl.impl_raises)."""


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
    var counted: Bool
    """Whether its constructors and `__deinit__` are its own, counting
    its values in the ledger (only when `Movable` or `Copyable`)."""
    var refs: List[Bool]
    """Per field, whether it has an accessor `def fK_ref(ref self) ->
    ref[self.fK] T`."""
    var valued: Bool
    """Whether it has a value parameter, `[n: Int]` (never with `T`)..."""
    var values: List[Int]
    """...and the values it's used with outside its own bodies."""
    var cond: Int
    """A generic struct's conditional conformance, `TrX where
    conforms_to(T, TrY)`: X, or -1..."""
    var cond_req: Int
    """...Y..."""
    var cond_where: Bool
    """...and whether its implementations of the methods only X needs are
    gated by the same condition (they needn't be)."""
    var a_traits: List[Int]
    """The traits whose associated types it binds..."""
    var a_types: List[Int]
    """...to these types (in its own terms: `Self.T`, Self, ...)."""
    var impl_plan: List[Int]
    """The trait methods it will implement (drawn before the bodies, so
    that calls know what each raises)..."""
    var impl_raises: List[Int]
    """...and what each implementation raises: the trait's, or nothing."""


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
    var wheres: List[Int]
    """Per type parameter, a trait it must also conform to (`where
    conforms_to(T, TrN)`; its body doesn't use it), or -1."""
    var raise_ty: Int
    """What it raises: -1 nothing, -2 Error (`raises`), k for `raises
    Xk`."""
    var vwhere: List[Prop]
    """Propositions about its value parameter in its `where` (joined by
    `and`)..."""
    var asserts: List[Prop]
    """...and in `comptime assert`s at the start of its body (implied by
    them)."""
    var wparam: Int
    """Its type parameter that no parameter's type mentions (the last one,
    which calls write), or -1."""


@fieldwise_init
struct Body(Copyable):
    var stmts: List[Int]
    var ret: Int
    var self_print: Int
    """The type written `Self` in this body and its signature, or -1."""
    var died: Bool
    """Whether its final return calls `_died()` first (a counted struct's
    `deinit self` method, with self not moved out whole)."""
    var names: List[String]
    """The names of the parameters in scope (a generic method's `U` may be
    renamed)."""


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
    """The place assigned (S_ASSIGN); 1 for a `while` loop (S_FOR); or
    -1."""
    var e: Int
    """The value (S_VAR, S_ASSIGN, S_EXPR) or the left operand (S_IF); -1
    for `var x: T` (S_VAR with no value)."""
    var e2: Int
    """The right operand of the condition (S_IF), or -1."""
    var a: Int
    """The comparison (S_IF), the trip count (S_FOR), or 1 for a `return`
    that calls `_died()` first (S_RETURN)."""
    var body: List[Int]
    var orelse: List[Int]
    var name: String
    """The variable declared (S_VAR; with its type, `vN: T`, when it has no
    value) or the loop variable (S_FOR)."""


@fieldwise_init
struct PatNode(Copyable):
    """A pattern (PK_*)."""

    var kind: Int
    var ty: Int
    """The type it matches."""
    var a: Int
    var b: Int
    var push: Bool
    """Whether it adds a variable (a PK_BIND or PK_VAR)."""
    var name: String
    """A binding's name, or a struct pattern's head."""
    var fields: List[Int]
    var kids: List[Int]


@fieldwise_init
struct Clause(Copyable):
    """A clause: CL_BOOL `l op r`, or CL_CASE `case <pattern l> =
    <subject>`, the subject a variable (subj: its slot, text: its name),
    an expression or a tuple's elements (sexprs), or a `match`'s (neither)."""

    var kind: Int
    var op: Int
    var l: Int
    var r: Int
    var subj: Int
    var sexprs: List[Int]
    var text: String


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
    var loop_base: Int
    """The first variable declared in the innermost loop body (0 outside
    loops): the ones before it are used again by the next iteration."""
    var no_move: Int
    """Inside a ternary branch, where moves would be conditional."""
    var const_if: Int
    """Inside a branch of an `if` whose condition is a constant."""
    var discard: Bool
    """The next expression drawn is the root of `_ = e`, which Mojo
    evaluates without copying (`_ = x.f` of a `Copyable` field is fine)."""
    var counter: Int
    """For fresh local names."""
    var ret: Int
    """The body's result type (for early returns), or -1."""
    var in_loop: Int
    """How many loops the context is in."""
    var in_finally: Int
    """How many `finally` clauses it's in."""
    var loop_live: List[Bool]
    """Which variables were live at the start of the innermost loop's body
    (`break` and `continue` reinitialize those moved since)."""
    var parent_base: Int
    """The loop_base of the loop around the innermost one (0 if none)."""
    var break_var: Int
    """A variable moved before a `break` (break_moved, loop_exit), dead
    after the loop, or -1."""
    var no_exit: Int
    """Inside statements drawn while a field is moved out (no early exit
    there: it would reassign the variable whole)."""
    var region_loops: Int
    """`in_loop` where those statements start, or -1: a loop there gets no
    loop inside it (the workaround in `partial_stmts`)."""
    var ref_names: List[String]
    """The `ref` bindings in scope: each one's name..."""
    var ref_var: List[Int]
    """...the variable it's a place in..."""
    var ref_field: List[Int]
    """...the field of it (-1 for the whole variable)..."""
    var ref_depth: List[Int]
    """...the block depth of its declaration (it goes out of scope at the
    end of that block)..."""
    var ref_ro: List[Bool]
    """...and whether it's read-only (a pattern's binding)."""
    var from_tuple: List[Bool]
    """Per variable: bound out of a temporary tuple by a pattern, which no
    `ref` binds: one is checked against the tuple's last element, so a
    move of that is "use of uninitialized value '(tuple element)'" at the
    `ref`'s use (modular/modular#7767); none is passed `mut`: two of
    one tuple share its origin ("aliasing values passed mutably"); and
    none is moved: a move of one can make the others uninitialized."""
    var self_ty: Int
    """In a struct's body, its type (with `Self.T` or `Self.n`), or -1."""
    var raise_ty: Int
    """What the body's function raises (FnDecl.raise_ty), -1 if nothing."""
    var catching: Int
    """How many `try` bodies the context is in: in one, a raising call's
    error is caught (the try's handlers cover every type it raises)..."""
    var raised: List[Int]
    """...and the error types raised in the innermost one so far (-2 for
    Error)."""
    var exit_catch: Int
    """While a field is moved out (no_exit), how many `try` bodies the
    context was in where that began: a raise there is caught in time only
    by a `try` begun inside the region."""
    var fin_type: Int
    """In a `finally` clause, the one error type that may leave it (Mojo
    unifies them, else "cannot find a unified error type", or makes them
    an Error, when a handler can raise too), or -9..."""
    var fin_catch: Int
    """...and how many `try` bodies the context was in at its start."""
    var nest: Int
    """How many argument lists the expression being drawn is in."""
    var freeze_base: Int
    """In a `try` statement, the variables from outside it (before this)
    are read-only: a raise can come at any point, so a move there would
    leave them maybe moved. The mutants about read variables skip
    them."""

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
        self.loop_base = 0
        self.no_move = 0
        self.const_if = 0
        self.discard = False
        self.counter = 0
        self.ret = -1
        self.in_loop = 0
        self.in_finally = 0
        self.loop_live = []
        self.parent_base = 0
        self.break_var = -1
        self.no_exit = 0
        self.region_loops = -1
        self.ref_names = []
        self.ref_var = []
        self.ref_field = []
        self.ref_depth = []
        self.ref_ro = []
        self.from_tuple = []
        self.self_ty = -1
        self.raise_ty = -1
        self.catching = 0
        self.raised = []
        self.freeze_base = 0
        self.exit_catch = 0
        self.fin_type = -9
        self.fin_catch = 0
        self.nest = 0

    def push(mut self, var name: String, ty: Int, kind: Int):
        self.names.append(name^)
        self.types.append(ty)
        self.kinds.append(kind)
        self.live.append(True)
        self.move_depth.append(-1)
        self.touched.append(False)
        self.excl.append(False)
        self.from_tuple.append(False)

    def drop_refs(mut self, depth: Int, n: Int):
        """Ends the scope of the bindings declared at depth or deeper, or
        to a variable from n on."""
        var i = 0
        while i < len(self.ref_names):
            if self.ref_depth[i] >= depth or self.ref_var[i] >= n:
                _ = self.ref_names.pop(i)
                _ = self.ref_var.pop(i)
                _ = self.ref_field.pop(i)
                _ = self.ref_depth.pop(i)
                _ = self.ref_ro.pop(i)
            else:
                i += 1

    def truncate(mut self, n: Int):
        self.drop_refs(Int.MAX, n)
        while len(self.names) > n:
            _ = self.names.pop()
            _ = self.types.pop()
            _ = self.kinds.pop()
            _ = self.live.pop()
            _ = self.move_depth.pop()
            _ = self.touched.pop()
            _ = self.excl.pop()
            _ = self.from_tuple.pop()

    def new_statement(mut self):
        for i in range(len(self.names)):
            self.touched[i] = False
            self.excl[i] = False
        self.taken = []


def kind_of_conv(conv: Int) -> Int:
    # (in a `deinit self` method, self can be assigned, mut-borrowed and
    # moved, like a `mut` argument; unlike one, it needn't be live at the
    # return, but the generator keeps it live except for the deinit near
    # misses)
    if conv == CONV_MUT or conv == CONV_DEINIT:
        return V_MUT
    return V_OWNED if conv == CONV_VAR else V_READ


comptime C_FN = 0
comptime C_METHOD = 1
comptime C_CTOR = 2


@fieldwise_init
struct Callee(Copyable):
    """A function, method or constructor a near miss's call can be."""

    var kind: Int
    """C_FN, C_METHOD (argument 0 is the receiver) or C_CTOR."""
    var id: Int
    """The function, the method, or the struct type."""
    var ret: Int
    var params: List[Int]
    var convs: List[Int]
    var tys: List[Int]
    """The type arguments of a generic function (C_FN), else empty."""


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
    var valn: List[Int]


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
    var pats: List[PatNode]
    var clauses: List[Clause]
    var csets: List[List[Int]]
    """Clause sets: the clauses of an `if`, `guard` or `case`."""
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
    var chances: Int
    """How many chances to make it there were (DECL_FUZZ_STATS=1)."""
    var near: Int
    """The kind of near miss to make (NR_*), or -1."""
    var near_made: Bool
    var loop_mark: Int
    """The depth of the loop body where MU_LOOP_MOVE moved an outer
    variable, until its loop is made (and marked); else -1."""
    var marked_stmts: List[Int]
    """Statements whose every line is marked."""
    var deinit_body: Bool
    """Whether the body being generated is a `deinit self` method's (self
    is variable 0)..."""
    var died: Bool
    """...and a counted struct's: its returns call `_died()`, since the
    struct's `__deinit__` doesn't run."""
    var bad_ref: Int
    """For MU_REF_ORIGIN, the accessor with the wrong origin (struct * 64 +
    field), or -1..."""
    var bad_origin: String
    """...and the origin it's declared with."""
    var keep_dead: Int
    """The `mut` argument a mut_uninit mutant left moved (blocks don't
    reinitialize it, and the body's return is marked), or -1."""
    var ret_value: Int
    """The value of the early `return` being executed."""
    var mark_struct: Int
    """The struct whose header line is marked, or -1..."""
    var mark_fields: Bool
    """...and its field lines..."""
    var mark_impl: Int
    """...and the signature of this one of its impl_methods, or -1."""
    var alias_ty: Int
    """For NR_ASSOC, while a struct's bodies are drawn and its
    declarations printed, a type one of its associated types is bound to,
    written..."""
    var alias_text: String
    """...this way (`Self.E0`)."""
    var alias_struct: Int
    """...the struct (-1 if none), and the alias, for printing it..."""
    var alias_saved: Int
    var alias_saved_text: String
    var pend_p: List[Int]
    """Associated types in a function's result that unification left for
    later (`call_assignment`): the type parameter..."""
    var pend_t: List[Int]
    """...the associated type (in terms of it)..."""
    var pend_ty: List[Int]
    """...and the type `T.E<t>` must be."""
    var err_value: Int
    """The error being raised (the evaluator's `raise` is an Error
    "RAISE")..."""
    var err_type: Int
    """...and its type (k for Xk)."""
    var exceptions: Bool
    """Whether functions may raise (not for the kinds that move `mut`
    arguments, which a raise would leave uninitialized)."""
    var facts: List[Int]
    """While a body with a `where` is drawn (a gated method's, or a
    function's), what it gives: PARAM p conforms to trait t (p * 64 +
    t)."""
    var vfacts: List[Int]
    """While a function's body is drawn, the propositions about its value
    parameter it knows (prop_key): its `where`'s..."""
    var vfacts_assert: List[Int]
    """...and those only its `comptime assert`s (or the `comptime if`s it's
    in) give."""
    var cif_fn: Int
    """While a function with a value parameter has its body drawn, the
    function (for `comptime if`), else -1."""
    var bad_where: Int
    """For MU_WHERE_IMPL, the implementation (struct * 64 + index) gated
    by a stricter condition, or -1..."""
    var bad_where_req: Int
    """...the trait of that condition."""
    var n_err: Int
    """How many error types the program declares (N_ERR, or 3 with X2)..."""
    var carry_ty: Int
    """...and the type of X2's field `val` (a concrete Copyable struct), or
    -1."""

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
        self.pats = []
        self.clauses = []
        self.csets = []
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
        self.chances = 0
        self.near = -1
        self.near_made = False
        self.loop_mark = -1
        self.marked_stmts = []
        self.deinit_body = False
        self.died = False
        self.keep_dead = -1
        self.bad_ref = -1
        self.bad_origin = String()
        self.ret_value = -1
        self.mark_struct = -1
        self.mark_fields = False
        self.mark_impl = -1
        self.bad_where = -1
        self.bad_where_req = -1
        self.err_value = -1
        self.err_type = -1
        self.exceptions = False
        self.n_err = N_ERR
        self.carry_ty = -1
        self.facts = []
        self.vfacts = []
        self.vfacts_assert = []
        self.cif_fn = -1
        self.alias_ty = -1
        self.alias_text = String()
        self.alias_struct = -1
        self.alias_saved = -1
        self.alias_saved_text = String()
        self.pend_p = []
        self.pend_t = []
        self.pend_ty = []
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

    def assoc(mut self, t: Int, owner: Int) -> Int:
        """`owner.E<t>`: a struct's binding, or an ASSOC type."""
        if self.tkind[owner] == STRUCT:
            var s = self.tid[owner]
            var i = index_of(self.structs[s].a_traits, t)
            if i >= 0:
                var b = self.structs[s].a_types[i]
                if self.structs[s].generic or self.structs[s].valued:
                    return self.subst(b, [self.targ[owner]])
                return b
        return self.intern(ASSOC, t, owner)

    def offset_ro(self, arg: Int, c: Int) -> Int:
        """Like offset, for a type already interned (-1 if it isn't)."""
        var kind = self.tkind[arg]
        if kind == OFF:
            return self.offset_ro(self.targ[arg], self.tid[arg] + c)
        if kind != VAL and c == 0:
            return arg
        var want_kind = kind
        var want_id = self.tid[arg] + c
        var want_arg = -1
        if kind != VAL:
            want_kind = OFF
            want_id = c
            want_arg = arg
        for i in range(len(self.tkind)):
            if (
                self.tkind[i] == want_kind
                and self.tid[i] == want_id
                and self.targ[i] == want_arg
            ):
                return i
        return -1

    def offset(mut self, arg: Int, c: Int) -> Int:
        """The value argument arg plus c: `k + c` folded, `n + c`."""
        var kind = self.tkind[arg]
        if kind == VAL:
            return self.intern(VAL, self.tid[arg] + c, -1)
        if kind == OFF:
            return self.offset(self.targ[arg], self.tid[arg] + c)
        if c == 0:
            return arg
        return self.intern(OFF, c, arg)

    def subst(mut self, ty: Int, args: List[Int]) -> Int:
        """Replaces PARAM i by args[i]."""
        var kind = self.tkind[ty]
        if kind == PARAM:
            return args[self.tid[ty]]
        if kind == OFF:
            var n = self.subst(self.targ[ty], args)
            return self.offset(n, self.tid[ty])
        if kind == ASSOC:
            var owner = self.subst(self.targ[ty], args)
            return self.assoc(self.tid[ty], owner)
        if kind == STRUCT and self.targ[ty] >= 0:
            var arg = self.subst(self.targ[ty], args)
            return self.intern(STRUCT, self.tid[ty], arg)
        return ty

    def subst_one(mut self, ty: Int, p: Int, arg: Int) -> Int:
        """Replaces PARAM p (the only one in ty) by arg."""
        var args = List[Int]()
        for _ in range(p):
            args.append(self.int_ty)
        args.append(arg)
        return self.subst(ty, args)

    def subst_all(mut self, tys: List[Int], args: List[Int]) -> List[Int]:
        var out = List[Int]()
        for t in tys:
            out.append(self.subst(t, args))
        return out^

    def ty_str(self, ty: Int, names: List[String], self_print: Int) -> String:
        if ty == self.alias_ty:  # (the assoc near miss)
            return String(MARK_NEAR, self.alias_text)
        if ty == self_print:
            return "Self"
        var kind = self.tkind[ty]
        if kind == VAL or kind == OFF:
            return self.val_str(ty, names)
        if kind == INT:
            return "Int"
        if kind == RES:
            return "Res"
        if kind == PARAM:
            return names[self.tid[ty]]
        if kind == ERR:
            if self.tid[ty] < 0:
                return "Error"
            return String("X", self.tid[ty])
        if kind == ASSOC:
            return String(
                self.ty_str(self.targ[ty], names, self_print),
                ".E",
                self.tid[ty],
            )
        var s = self.structs[self.tid[ty]].name
        if self.targ[ty] >= 0 and self.structs[self.tid[ty]].valued:
            return String(s, "[", self.val_str(self.targ[ty], names), "]")
        if self.targ[ty] >= 0:
            return String(
                s, "[", self.ty_str(self.targ[ty], names, self_print), "]"
            )
        return s

    def val_str(self, arg: Int, names: List[String]) -> String:
        """A value argument, spelled by resolve_values: `@@=k@@` for k,
        `@@=n;c@@` for `n + c`. A bare n is spelled `n`, except for the
        value_expr near miss (`@@=n;0@@`)."""
        var kind = self.tkind[arg]
        if kind == VAL:
            return String("@@=", self.tid[arg], "@@")
        if kind == OFF:
            return String(
                "@@=", names[self.tid[self.targ[arg]]], ";", self.tid[arg], "@@"
            )
        if self.near == NR_VALUE_EXPR:
            return String("@@=", names[self.tid[arg]], ";0@@")
        return names[self.tid[arg]]

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
        if kind == INT or kind == RES or kind == ERR:
            return False
        if kind == ASSOC:
            return self.refines(self.traits[self.tid[ty]].assoc, t)
        if kind == PARAM:
            var p = self.tid[ty]
            for x in self.facts:
                if x // 64 == p and self.refines(x % 64, t):
                    return True
            return self.refines(bounds[p], t)
        ref sd = self.structs[self.tid[ty]]
        for x in sd.traits:
            if self.refines(x, t):
                return True
        # B[X] with `TrC where conforms_to(T, TrR)`, when X conforms to TrR
        # (Mojo proves it from a type parameter's bound too)
        return (
            sd.cond >= 0
            and self.refines(sd.cond, t)
            and self.conforms(self.targ[ty], sd.cond_req, bounds)
        )

    def sig_needs_where(mut self, s: Int, m: Int) -> Bool:
        """Whether struct s's implementation of trait method m has Self as
        a type argument in its signature."""
        var args = self.impl_args(s, m)
        var self_ty = args[0]
        var tys = self.subst_all(self.methods[m].params.copy(), args)
        tys.append(self.subst(self.methods[m].ret, args))
        for t in tys:
            if self.has_arg(t, self_ty):
                return True
        return False

    def mentions_param(self, ty: Int) -> Bool:
        var kind = self.tkind[ty]
        if kind == PARAM:
            return True
        if (kind == STRUCT or kind == ASSOC) and self.targ[ty] >= 0:
            return self.mentions_param(self.targ[ty])
        return False

    def cap_of_any(self, ty: Int) -> Int:
        """A type's capability where the bounds aren't at hand: a type
        parameter's (its argument here) counts as Copyable."""
        var kind = self.tkind[ty]
        if kind == PARAM or kind == ASSOC:
            return CAP_C
        if kind == STRUCT:
            return self.structs[self.tid[ty]].cap
        return CAP_IC if kind == INT else CAP_C

    def has_arg(self, ty: Int, arg: Int) -> Bool:
        """Whether arg is a type argument somewhere in ty."""
        if self.tkind[ty] != STRUCT or self.targ[ty] < 0:
            return False
        return self.targ[ty] == arg or self.has_arg(self.targ[ty], arg)

    def cond_only(self, ty: Int, t: Int, bounds: List[Int]) -> Bool:
        """Whether ty (some `B[X]`) would conform to t through its
        conditional conformance, but X fails the condition."""
        if self.tkind[ty] != STRUCT:
            return False
        ref sd = self.structs[self.tid[ty]]
        return (
            sd.cond >= 0
            and self.refines(sd.cond, t)
            and not self.conforms(ty, t, bounds)
        )

    def is_gated(self, s: Int, m: Int) -> Bool:
        """Whether struct s's implementation of trait method m is only
        needed by its conditional conformance (and so may be gated)."""
        ref sd = self.structs[s]
        if sd.cond < 0 or self.methods[m].trait_id < 0:
            return False
        var t = self.methods[m].trait_id
        for x in sd.traits:
            if self.refines(x, t):
                return False
        return self.refines(sd.cond, t)

    def where_text(mut self, s: Int, m: Int) -> String:
        """The `where` clause of struct s's implementation of m, if any:
        drawn so, or needed by its signature (which has Self as a type
        argument, `B2[Self]`, valid only when Self conforms to B2's bound,
        which may be the conditional trait)."""
        if not self.is_gated(s, m):
            return ""
        if not self.structs[s].cond_where and not self.sig_needs_where(s, m):
            return ""
        return String(
            " where conforms_to(Self.T, Tr", self.structs[s].cond_req, ")"
        )

    def cap_of(self, ty: Int, bounds: List[Int]) -> Int:
        var kind = self.tkind[ty]
        if kind == INT:
            return CAP_IC
        if kind == RES or kind == ERR:
            return CAP_C
        if kind == ASSOC:
            return self.traits[self.traits[self.tid[ty]].assoc].cap
        if kind == PARAM:
            # (a `where` may give more: `ImplicitlyCopyable` for a
            # `Copyable` bound)
            var p = self.tid[ty]
            var cap = self.traits[bounds[p]].cap
            for x in self.facts:
                if x // 64 == p:
                    cap = max(cap, self.traits[x % 64].cap)
            return cap
        return self.structs[self.tid[ty]].cap

    def fields_of(mut self, ty: Int) -> List[Int]:
        if self.tkind[ty] == ERR:
            # (an Error binding has none; X2 carries `val`)
            if self.tid[ty] < 0:
                return []
            if self.tid[ty] == N_ERR:
                return [self.int_ty, self.carry_ty]
            return [self.int_ty]
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
        if self.tkind[ty] == ERR:
            return "code" if f == 0 else "val"
        return String("f", f)

    def type_pool(mut self, bounds: List[Int], n_structs: Int) -> List[Int]:
        """Int, Res, the concrete structs, the parameters in scope, and
        generic structs over them (two levels deep)."""
        var pool: List[Int] = [self.int_ty, self.res_ty]
        for s in range(n_structs):
            pool += self.concrete_types(s)
        for p in range(len(bounds)):
            if bounds[p] >= 0:  # (-1: a value parameter)
                pool.append(self.intern(PARAM, p, -1))
        # their associated types, `T.E0` (`Self.E0` in a trait), and
        # theirs, `T.E0.E1`
        for p in range(len(bounds)):
            if bounds[p] >= 0:
                var n = self.intern(PARAM, p, -1)
                for x in self.closure([bounds[p]]):
                    var u = self.traits[x].assoc
                    if u < 0:
                        continue
                    var a = self.intern(ASSOC, x, n)
                    pool.append(a)
                    for y in self.closure([u]):
                        if self.traits[y].assoc >= 0:
                            pool.append(self.intern(ASSOC, y, a))
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

    def concrete_types(mut self, s: Int) -> List[Int]:
        """Struct s's types outside its bodies, unless it's generic: S, or
        V[k] for each of its values."""
        if self.structs[s].generic:
            return []
        if not self.structs[s].valued:
            return [self.intern(STRUCT, s, -1)]
        var out = List[Int]()
        for k in self.structs[s].values.copy():
            out.append(self.intern(STRUCT, s, self.intern(VAL, k, -1)))
        return out^

    def is_valued(self, ty: Int) -> Bool:
        return self.tkind[ty] == STRUCT and self.structs[self.tid[ty]].valued

    def value_family(mut self, s: Int, p: Int) -> List[Int]:
        """V[n], V[n + 1] and V[n - 1], for struct s (V) with the value
        parameter n (PARAM p) in scope."""
        var n = self.intern(PARAM, p, -1)
        var out = List[Int]()
        for c in [0, 1, -1]:
            out.append(self.intern(STRUCT, s, self.offset(n, c)))
        return out^

    def fn_pool(mut self, f: Int) -> List[Int]:
        """The types function f's signature and body draw from."""
        var bounds = self.fns[f].bounds.copy()
        var pool = self.type_pool(bounds, len(self.structs))
        for i in range(len(bounds)):
            if bounds[i] < 0:
                pool += self.value_family(self.tid[self.fns[f].params[i]], i)
        return pool^

    def fn_names(self, f: Int) -> List[String]:
        """The names of function f's parameters: `T` and `U` for types, `n`
        for a value."""
        var out = List[String]()
        var bounds = self.fns[f].bounds.copy()
        var types = 0
        for i in range(len(bounds)):
            if bounds[i] < 0:
                out.append("n")
            else:
                var tnames: List[String] = ["T", "U", "W"]
                out.append(tnames[types])
                types += 1
        return out^

    def value_args(self, ctx: Ctx, s: Int) -> List[Int]:
        """The arguments of struct s (with a value parameter) in the pool:
        a free value parameter of a call is drawn from them."""
        var out = List[Int]()
        for t in ctx.pool:
            if self.tkind[t] == STRUCT and self.tid[t] == s:
                if not has(out, self.targ[t]):
                    out.append(self.targ[t])
        return out^

    def targ_choices(self, ctx: Ctx, f: Int, i: Int) -> List[Int]:
        """What parameter i of function f can be, where nothing fixes it."""
        var b = self.fns[f].bounds[i]
        if b < 0:
            # (for `V[n + c]`, n = the argument - c)
            var p = self.fns[f].params[i]
            var c = 0
            if self.tkind[self.targ[p]] == OFF:
                c = self.tid[self.targ[p]]
            var out = List[Int]()
            for a in self.value_args(ctx, self.tid[p]):
                var v = self.offset_ro(a, -c)
                if v >= 0 and self.vw_holds(f, v) and not has(out, v):
                    out.append(v)
            return out^
        var w = self.fns[f].wheres[i]
        var out = List[Int]()
        for t in self.conforming(ctx, b):
            if w < 0 or self.conforms(t, w, ctx.bounds):
                out.append(t)
        return out^

    # ---- `where` on value parameters

    @staticmethod
    def prop_key(p: Int, c: Int, ge: Bool, k: Int) -> Int:
        """A proposition `n + c >= k` (or `<=`) about PARAM p, as an Int."""
        return ((p * 2 + Int(ge)) * 4096 + c + 2048) * 4096 + k + 2048

    @staticmethod
    def prop_holds(v: Int, pr: Prop) -> Bool:
        return v + pr.c >= pr.k if pr.ge else v + pr.c <= pr.k

    @staticmethod
    def implies(a: Prop, b: Prop) -> Bool:
        """Whether a implies b arithmetically (which Mojo doesn't see)."""
        if a.ge != b.ge:
            return False
        if a.ge:
            return b.k - b.c <= a.k - a.c
        return b.k - b.c >= a.k - a.c

    def noninfer(self, f: Int) -> Bool:
        """Whether function f's value parameter n can't be inferred: its
        parameter is `V[n + c]`."""
        var vi = self.vw_fn_index(f)
        return vi >= 0 and self.tkind[self.targ[self.fns[f].params[vi]]] == OFF

    def vw_fn_index(self, f: Int) -> Int:
        """Function f's value parameter, or -1."""
        return index_of(self.fns[f].bounds, -1)

    def vw_holds(self, f: Int, arg: Int) -> Bool:
        """Whether a call of function f with arg for its value parameter
        meets its `where`: a value must make it true; `n + d` (n a value
        parameter in scope) needs each proposition, with n + d for n, among
        the known ones (vfacts), as Mojo needs evidence for it."""
        return self.props_hold(self.fns[f].vwhere, arg)

    def props_hold(self, props: List[Prop], arg: Int) -> Bool:
        """Like vw_holds, for these propositions."""
        if len(props) == 0:
            return True
        var kind = self.tkind[arg]
        if kind == VAL:
            for pr in props:
                if not Self.prop_holds(self.tid[arg], pr):
                    return False
            return True
        var base = arg
        var d = 0
        if kind == OFF:
            base = self.targ[arg]
            d = self.tid[arg]
        if self.tkind[base] != PARAM:
            return False
        for pr in props:
            var key = Self.prop_key(self.tid[base], d + pr.c, pr.ge, pr.k)
            if not has(self.vfacts, key) and not has(self.vfacts_assert, key):
                return False
        return True

    def vw_by_assert(self, f: Int, arg: Int) -> Bool:
        """Whether a call meeting f's `where` (vw_holds) with a symbolic
        arg needs evidence only a `comptime assert` gives."""
        return self.props_by_assert(self.fns[f].vwhere, arg)

    def props_by_assert(self, props: List[Prop], arg: Int) -> Bool:
        if len(props) == 0 or arg < 0:
            return False
        var kind = self.tkind[arg]
        if kind != PARAM and kind != OFF:
            return False
        var base = arg if kind == PARAM else self.targ[arg]
        var d = 0 if kind == PARAM else self.tid[arg]
        if self.tkind[base] != PARAM:
            return False
        for pr in props:
            var key = Self.prop_key(self.tid[base], d + pr.c, pr.ge, pr.k)
            if not has(self.vfacts, key) and has(self.vfacts_assert, key):
                return True
        return False

    def mw_holds(self, m: Int, recv: Int) -> Bool:
        """Whether own method m's `where` holds for a receiver of type recv
        (V[x]: for x)."""
        if len(self.methods[m].vwhere) == 0:
            return True
        return self.props_hold(self.methods[m].vwhere, self.targ[recv])

    def reqs_on(self, s: Int, skip: Int) -> List[Prop]:
        """What a function with a value parameter of struct s (V[n]) would
        need to know to call the other functions on V with V[n + d] (d in
        0, 1, -1): each of their propositions, with n + d for n."""
        var out = List[Prop]()
        for g in range(len(self.fns)):
            var vi = self.vw_fn_index(g)
            if g == skip or vi < 0:
                continue
            if self.tid[self.fns[g].params[vi]] != s:
                continue
            for pr in self.fns[g].vwhere:
                for d in [0, 1, -1]:
                    out.append(Prop(d + pr.c, pr.ge, pr.k, 0))
        return out^

    def draw_prop(
        mut self, mut data: ConjectureData, s: Int, f: Int
    ) raises -> Prop:
        """A proposition for function f's `where` about its V[n] (struct s):
        half the time one another function on V needs (so that f can call
        it with `V[n + d]`), else one true of some value V is used with."""
        var reqs = self.reqs_on(s, f)
        var form = data.draw(integers(0, 3))
        if len(reqs) > 0 and data.draw(booleans()):
            var r = reqs[pick(data, len(reqs))].copy()
            r.form = form
            # for the vwhere kinds, half the time a stronger one, which
            # implies it but isn't evidence for it (an assert can be)
            if (
                self.mutant == MU_VWHERE or self.near == NR_VWHERE
            ) and data.draw(booleans()):
                var bound = r.k - r.c
                bound += data.draw(integers(1, 2)) * (1 if r.ge else -1)
                r.c = data.draw(integers(-1, 1))
                r.k = bound + r.c
            return r^
        var values = self.structs[s].values.copy()
        var v = values[pick(data, len(values))]
        var c = data.draw(integers(-1, 1))
        var ge = data.draw(booleans())
        var j = data.draw(integers(0, 2))
        return Prop(c, ge, v + c - j if ge else v + c + j, form)

    def draw_assert(
        mut self, mut data: ConjectureData, vwhere: List[Prop], s: Int, f: Int
    ) raises -> Prop:
        """A `comptime assert` implied by the `where` propositions but not
        equal to any (it never fails, since every call meets the `where`):
        one another function on V needs, if one is implied, else a weaker
        form of a `where` proposition (`n >= 3` gives `n - 1 >= 1`)."""
        var cands = List[Prop]()
        for r in self.reqs_on(s, f):
            var equal = False
            var implied = False
            for a in vwhere:
                if a.ge == r.ge and a.c == r.c and a.k == r.k:
                    equal = True
                if Self.implies(a, r):
                    implied = True
            if implied and not equal:
                cands.append(r.copy())
        var form = data.draw(integers(0, 3))
        if len(cands) > 0 and data.draw(integers(0, 3)) > 0:
            var r = cands[pick(data, len(cands))].copy()
            r.form = form
            return r^
        ref a = vwhere[pick(data, len(vwhere))]
        var c = data.draw(integers(-1, 1))
        while c == a.c:
            c = data.draw(integers(-1, 1))
        var j = data.draw(integers(0, 2))
        var bound = a.k - a.c
        return Prop(c, a.ge, bound + c - j if a.ge else bound + c + j, form)

    def prop_text(mut self, pr: Prop, vi: Int, names: List[String]) -> String:
        """`n + c >= k` in one of four forms, `n + c > k - 1`, `k <= n +
        c`, ..., each side spelled as resolve_values draws."""
        var lhs = self.val_str(
            self.offset(self.intern(PARAM, vi, -1), pr.c), names
        )
        var k = pr.k
        if pr.form == 1 or pr.form == 3:
            k += -1 if pr.ge else 1
        var rhs = String("@@=", k, "@@")
        var op: String
        if pr.form < 2:
            if pr.ge:
                op = " >= " if pr.form == 0 else " > "
            else:
                op = " <= " if pr.form == 0 else " < "
            return String(lhs, op, rhs)
        if pr.ge:
            op = " <= " if pr.form == 2 else " < "
        else:
            op = " >= " if pr.form == 2 else " > "
        return String(rhs, op, lhs)

    def methods_on(self, ty: Int, bounds: List[Int]) -> List[Int]:
        """Non-static methods callable on a value of type ty."""
        var out = List[Int]()
        if self.tkind[ty] == STRUCT:
            for m in self.structs[self.tid[ty]].own:
                if self.mw_holds(m, ty):
                    out.append(m)
        for t in range(len(self.traits)):
            if self.conforms(ty, t, bounds):
                for m in self.traits[t].methods:
                    if not self.methods[m].is_static:
                        out.append(m)
        return out^

    def method_args(
        mut self, m: Int, recv: Int, us: List[Int] = []
    ) -> List[Int]:
        """What to substitute into m's signature for receiver type recv;
        for a generic method, with us for its own parameters (HOLE i for
        each one missing)."""
        var out = List[Int]()
        if self.methods[m].trait_id >= 0:
            out.append(recv)
        else:
            ref sd = self.structs[self.methods[m].struct_id]
            if sd.generic or sd.valued:
                out.append(self.targ[recv])
        if self.is_generic_method(m):
            if len(out) == 0:
                out.append(self.int_ty)  # (PARAM 0 isn't used)
            for i in range(self.n_own(m)):
                out.append(
                    us[i] if i < len(us)
                    and us[i] >= 0 else self.intern(HOLE, i, -1)
                )
        return out^

    def method_ret(mut self, m: Int, recv: Int, us: List[Int] = []) -> Int:
        var args = self.method_args(m, recv, us)
        if len(args) == 0:
            return self.methods[m].ret
        return self.subst(self.methods[m].ret, args)

    def is_generic_method(self, m: Int) -> Bool:
        """Whether m has a parameter of its own: a type or a value."""
        return self.methods[m].mbound >= 0 or self.methods[m].mvalue >= 0

    def is_both(self, m: Int) -> Bool:
        """Whether m has two parameters of its own, `[U: TrN, k: Int]`."""
        return self.methods[m].mbound >= 0 and self.methods[m].mvalue >= 0

    def n_own(self, m: Int) -> Int:
        if self.is_both(m):
            return 2
        return 1 if self.is_generic_method(m) else 0

    def own_bounds(self, m: Int) -> List[Int]:
        """The bounds of m's own parameters (-1 for a value)."""
        if self.is_both(m):
            return [self.methods[m].mbound, -1]
        if self.methods[m].mbound >= 0:
            return [self.methods[m].mbound]
        return [-1] if self.methods[m].mvalue >= 0 else List[Int]()

    def own_names(self, m: Int, u: String = "U") -> List[String]:
        """The names of m's own parameters: U (or u) for a type, k for a
        value."""
        if self.is_both(m):
            return [u, "k"]
        if self.methods[m].mbound >= 0:
            return [u]
        return ["k"] if self.methods[m].mvalue >= 0 else List[String]()

    def trait_names(self, m: Int) -> List[String]:
        """The names in trait method m's signature: Self, then its own."""
        var out: List[String] = ["Self"]
        out += self.own_names(m)
        return out^

    def k_index(self, m: Int) -> Int:
        """The PARAM index of m's own value parameter k, or -1."""
        if self.methods[m].mvalue < 0:
            return -1
        return 2 if self.is_both(m) else 1

    def match_hole(mut self, pat: Int, ty: Int, mut assign: List[Int]) -> Bool:
        """Whether pat, with HOLE i for a generic method's own parameter i
        (`U` or `k`), is ty for some assignment (assign[i]); everything else
        in pat is fixed."""
        if self.tkind[pat] == HOLE:
            var i = self.tid[pat]
            if assign[i] < 0:
                assign[i] = ty
                return True
            return assign[i] == ty
        if self.tkind[pat] == OFF and self.tkind[self.targ[pat]] == HOLE:
            # k + c = ty: k = ty - c
            var tk = self.tkind[ty]
            if tk != VAL and tk != PARAM and tk != OFF:
                return False
            var solved = self.offset(ty, -self.tid[pat])
            return self.match_hole(self.targ[pat], solved, assign)
        if pat == ty:
            return True
        if (
            self.tkind[pat] == STRUCT
            and self.tkind[ty] == STRUCT
            and self.tid[pat] == self.tid[ty]
            and self.targ[pat] >= 0
            and self.targ[ty] >= 0
        ):
            return self.match_hole(self.targ[pat], self.targ[ty], assign)
        return False

    def method_fit(mut self, m: Int, r: Int, ty: Int, ctx: Ctx) -> Int:
        """Whether m on a receiver of type r can return ty: -2 if not."""
        if len(self.method_assign(m, r, ty, ctx)) == 0:
            return -2
        return 0

    def method_assign(mut self, m: Int, r: Int, ty: Int, ctx: Ctx) -> List[Int]:
        """What m's own parameters must be for m on a receiver of type r
        to return ty (-1 where any allowed one does; [-1] if m isn't
        generic), or [] if nothing makes it."""
        var ret = self.method_ret(m, r)
        if not self.is_generic_method(m):
            return [-1] if ret == ty else List[Int]()
        var bounds = self.own_bounds(m)
        var assign = List[Int](length=len(bounds), fill=-1)
        if not self.match_hole(ret, ty, assign):
            return []
        for i in range(len(bounds)):
            if assign[i] >= 0:
                if bounds[i] >= 0 and not self.conforms(
                    assign[i], bounds[i], ctx.bounds
                ):
                    return []
            elif len(self.own_choices(m, i, ctx)) == 0:
                return []
        return assign^

    def own_choices(self, m: Int, i: Int, ctx: Ctx) -> List[Int]:
        """What generic method m's own parameter i can be where nothing
        fixes it: a conforming type, or V's arguments in the pool."""
        if self.own_bounds(m)[i] < 0:
            return self.value_args(ctx, self.methods[m].mvalue)
        return self.conforming(ctx, self.methods[m].mbound)

    def method_params(
        mut self, m: Int, recv: Int, us: List[Int] = []
    ) -> List[Int]:
        var args = self.method_args(m, recv, us)
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

    def unify(mut self, pat: Int, ty: Int, mut assign: List[Int]) -> Bool:
        var kind = self.tkind[pat]
        if kind == VAL:
            return ty == pat
        if kind == ASSOC:
            # T.E<t> = ty (or T.E<u>.E<t>): checked once T is known
            # (call_assignment)
            var o = self.targ[pat]
            while self.tkind[o] == ASSOC:
                o = self.targ[o]
            if self.tkind[o] != PARAM:
                return pat == ty
            self.pend_p.append(self.tid[o])
            self.pend_t.append(pat)
            self.pend_ty.append(ty)
            return True
        if kind == OFF:
            # n + c = ty, so n = ty - c (Mojo doesn't infer through the
            # arithmetic, but the generator solves for the arguments it
            # picks, and a value parameter's first argument is V[n])
            var tk = self.tkind[ty]
            if tk != VAL and tk != PARAM and tk != OFF:
                return False
            var n = self.targ[pat]
            var solved = self.offset(ty, -self.tid[pat])
            return self.unify(n, solved, assign)
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

    def binding_cands(mut self, s: Int, u: Int) -> List[Int]:
        """What struct s can bind an associated type with bound u to: types
        of its pool conforming to u (in its own terms), Self too."""
        ref sd = self.structs[s]
        var bounds = [sd.bound] if sd.generic else List[Int]()
        var pool = self.type_pool(bounds, len(self.structs))
        pool.append(self.self_type(s))
        var out = List[Int]()
        for t in pool:
            if not self.conforms(t, u, bounds) or has(out, t):
                continue
            # (not `B[Self.T.E0.E0]`: with S binding E0 to `B[S]`, B[S].E0
            # would be B[B[S].E0], an infinite type; one level, `B[Self.T.E0]`,
            # recurses on a smaller argument)
            if self.has_nested(t):
                continue
            # Mojo overflows its stack on `comptime E0 = B1[B1[Self.T.E0]]`
            # in a B1 with a field of type `Self.T.E0`, and on
            # `comptime E0 = B1[Self]` in one with a field of type
            # `Self.T.E0.E0` (modular/modular#7814): not the struct
            # twice around an associated type, nor twice at all if a
            # field has a nested associated type
            if (
                self.nest_count(t, s) >= 2
                and (self.has_any_assoc(t) or self.has_nested_field(s))
                and getenv("DECL_FUZZ_NO_ASSOC_NEST_WORKAROUND") == ""
            ):
                continue
            out.append(t)
        return out^

    def nest_count(self, ty: Int, s: Int) -> Int:
        """How many times struct s is in ty's chain of type arguments."""
        var n = 0
        var t = ty
        while t >= 0:
            if self.tkind[t] == STRUCT and self.tid[t] == s:
                n += 1
            if self.tkind[t] != STRUCT and self.tkind[t] != ASSOC:
                break
            t = self.targ[t]
        return n

    def is_nested(self, ty: Int) -> Bool:
        """Whether ty is an associated type of one, `T.E0.E1`."""
        return self.tkind[ty] == ASSOC and self.tkind[self.targ[ty]] == ASSOC

    def has_nested_field(self, s: Int) -> Bool:
        """Whether a field of struct s has a nested associated type."""
        for f in self.structs[s].fields:
            if self.has_nested(f):
                return True
        return False

    def has_nested(self, ty: Int) -> Bool:
        """Whether ty has a nested associated type (`X.E0.E1`) in it."""
        var t = ty
        while t >= 0:
            if self.is_nested(t):
                return True
            if self.tkind[t] != STRUCT and self.tkind[t] != ASSOC:
                return False
            t = self.targ[t]
        return False

    def has_any_assoc(self, ty: Int) -> Bool:
        var t = ty
        while t >= 0:
            if self.tkind[t] == ASSOC:
                return True
            if self.tkind[t] != STRUCT:
                return False
            t = self.targ[t]
        return False

    def has_assoc(self, ty: Int, t: Int) -> Bool:
        """Whether ty has an associated type `X.E<t>` in it."""
        var kind = self.tkind[ty]
        if kind == ASSOC and self.tid[ty] == t:
            return True
        if (kind == STRUCT or kind == ASSOC) and self.targ[ty] >= 0:
            return self.has_assoc(self.targ[ty], t)
        return False

    def sig_has_assoc(self, m: Int, t: Int) -> Bool:
        """Whether method m's signature (in its trait's terms) has
        `X.E<t>` in it."""
        if self.has_assoc(self.methods[m].ret, t):
            return True
        for p in self.methods[m].params:
            if self.has_assoc(p, t):
                return True
        return False

    def well_formed(self, ty: Int, bounds: List[Int]) -> Bool:
        """Whether each generic struct in ty has an argument conforming to
        its bound (and each associated type's owner conforms to its
        trait)."""
        var kind = self.tkind[ty]
        if kind == ASSOC:
            return self.conforms(
                self.targ[ty], self.tid[ty], bounds
            ) and self.well_formed(self.targ[ty], bounds)
        if kind != STRUCT or self.targ[ty] < 0:
            return True
        ref sd = self.structs[self.tid[ty]]
        if sd.generic and not self.conforms(self.targ[ty], sd.bound, bounds):
            return False
        return self.well_formed(self.targ[ty], bounds)

    def all_traits(self, s: Int) -> List[Int]:
        """Struct s's declared conformances, the conditional one too."""
        var out = self.structs[s].traits.copy()
        if self.structs[s].cond >= 0:
            out.append(self.structs[s].cond)
        return out^

    def draw_bindings(mut self, mut data: ConjectureData) raises:
        """Each struct binds the associated types of the traits it conforms
        to. First, until nothing changes, a struct gives up conformances
        whose associated type nothing it can name conforms to the bound
        of (giving one up can leave another struct without candidates)."""
        var changed = True
        var dropped = False
        while changed:
            changed = False
            for s in range(len(self.structs)):
                for x in self.closure(self.all_traits(s)):
                    var u = self.traits[x].assoc
                    if u < 0 or len(self.binding_cands(s, u)) > 0:
                        continue
                    var kept = List[Int]()
                    for t in self.structs[s].traits:
                        if not self.refines(t, x):
                            kept.append(t)
                    self.structs[s].traits = kept^
                    var c = self.structs[s].cond
                    if c >= 0 and self.refines(c, x):
                        self.structs[s].cond = -1
                    changed = True
                    dropped = True
                    break
        # (fields were drawn before: `B0[S2]` may be wrong now)
        if dropped:
            for s in range(len(self.structs)):
                var bounds = [self.structs[s].bound] if self.structs[
                    s
                ].generic else List[Int]()
                for t in self.structs[s].fields.copy():
                    if not self.well_formed(t, bounds):
                        raise Error("STUCK")
        for s in range(len(self.structs)):
            var need = self.closure(self.all_traits(s))
            # (constants only the traits given up needed would be extra,
            # and a missing mutant could remove one)
            ref sd = self.structs[s]
            var kt = List[Int]()
            var kv = List[Int]()
            var ks = List[Int]()
            for i in range(len(sd.k_traits)):
                if has(need, sd.k_traits[i]):
                    kt.append(sd.k_traits[i])
                    kv.append(sd.k_values[i])
                    ks.append(sd.k_sources[i])
            self.structs[s].k_traits = kt^
            self.structs[s].k_values = kv^
            self.structs[s].k_sources = ks^
            for x in need:
                var u = self.traits[x].assoc
                if u < 0:
                    continue
                var cands = self.binding_cands(s, u)
                self.structs[s].a_traits.append(x)
                self.structs[s].a_types.append(cands[pick(data, len(cands))])

    def mentions(self, ty: Int, p: Int) -> Bool:
        """Whether type ty mentions PARAM p."""
        var kind = self.tkind[ty]
        if kind == PARAM:
            return self.tid[ty] == p
        if (kind == STRUCT or kind == ASSOC or kind == OFF) and self.targ[
            ty
        ] >= 0:
            return self.mentions(self.targ[ty], p)
        return False

    def draw_signature(
        mut self,
        mut data: ConjectureData,
        bounds: List[Int],
        extra: List[Int],
        own: Int,
        mut_often: Bool,
        mut params: List[Int],
        mut convs: List[Int],
        mut mbound: Int,
        mut mvalue: Int,
    ) raises -> Int:
        """A method's parameters (into params and convs) and result type,
        in a context with these bounds and extra types. A quarter of them
        (half for the rename near miss) are generic, `[U: TrN]` (into
        mbound): U is PARAM 1, the type of the first parameter (which Mojo
        infers it from), and often of others and the result. Parameters
        whose types mention U aren't `mut`, which calls would need places
        of each U for. Another eighth (more for the value kinds) have a
        value parameter `[k: Int]` instead (into mvalue, the struct V of
        their first parameter, `V[k]`), when some struct has one. A third
        of the generic ones (2/3 for the own2 kinds) have both, `[U: TrN,
        k: Int]` (PARAM 1 and 2; their first parameters are U and
        `V[k]`)."""
        var valued = List[Int]()
        for st in range(len(self.structs)):
            if self.structs[st].valued:
                valued.append(st)
        var own2_kind = self.mutant == MU_OWN2 or self.near == NR_OWN2
        var choice = data.draw(integers(0, 7))
        if choice < (4 if self.near == NR_RENAME or own2_kind else 2):
            mbound = pick(data, len(self.traits))
            if len(valued) > 0 and data.draw(integers(0, 2)) < (
                2 if own2_kind else 1
            ):
                mvalue = valued[pick(data, len(valued))]
        elif len(valued) > 0 and choice < (
            6 if self.mutant == MU_VALUE or self.near == NR_VALUE_EXPR else 3
        ):
            mvalue = valued[pick(data, len(valued))]
        var generic = mbound >= 0 or mvalue >= 0
        var both = mbound >= 0 and mvalue >= 0
        var kp = 2 if both else 1
        var bs = bounds.copy()
        var sig_own = own
        if generic:
            if len(bs) == 0:
                bs.append(-1)  # (PARAM 0 is a value or unused)
            bs.append(mbound)  # (-1 for a value parameter)
            if both:
                bs.append(-1)
        var pool = self.type_pool(bs, len(self.structs))
        pool += extra.copy()
        if mvalue >= 0:
            pool += self.value_family(mvalue, kp)
        if generic:
            var firsts = List[Int]()
            if mbound >= 0:
                firsts.append(self.intern(PARAM, 1, -1))
            if mvalue >= 0:
                firsts.append(
                    self.intern(STRUCT, mvalue, self.intern(PARAM, kp, -1))
                )
            for u in firsts:
                params.append(u)
                convs.append(CONV_VAR if data.draw(booleans()) else CONV_READ)
            if data.draw(booleans()):
                sig_own = firsts[pick(data, len(firsts))]
        for _ in range(data.draw(integers(0, 1 if generic else 2))):
            var t = self.draw_sig_type(data, pool, sig_own)
            var c = draw_conv(data, mut_often)
            if (
                generic
                and c == CONV_MUT
                and (self.mentions(t, 1) or self.mentions(t, 2))
            ):
                c = CONV_READ
            params.append(t)
            convs.append(c)
        return self.draw_sig_type(data, pool, sig_own)

    def exc_kind(self) -> Bool:
        """Whether the kind drawn is about exceptions (they raise more)."""
        return (
            self.mutant == MU_UNHANDLED
            or self.mutant == MU_RAISE_CTX
            or self.mutant == MU_RAISE_TYPE
            or self.mutant == MU_RAISE_IMPL
            or self.mutant == MU_TRY_SCOPE
            or self.mutant == MU_TRY_MOVE
            or self.near == NR_UNREACHABLE
            or self.near == NR_TRY_MOVE
        )

    def draw_method_raise(
        mut self, mut data: ConjectureData, self_conv: Int, exc_kind: Bool
    ) raises -> Int:
        """What a method raises: nothing, Error or Xk, for a third of them
        (1/2 for the exception kinds), never with `deinit self` (a counted
        struct's has to call `_died()`)."""
        if not self.exceptions or self_conv == CONV_DEINIT:
            return -1
        if data.draw(integers(0, 5)) >= (3 if exc_kind else 2):
            return -1
        if data.draw(integers(0, 2)) == 0:
            return -2
        return pick(data, self.n_err)

    def draw_declarations(mut self, mut data: ConjectureData) raises:
        # mut_read and alias mutants, and disjoint near misses, need calls
        # with `mut` arguments; mut_uninit and mut_reinit, bodies with them
        var mut_often = (
            self.mutant == MU_MUT_READ
            or self.mutant == MU_ALIAS
            or self.mutant == MU_MUT_UNINIT
            or self.mutant == MU_RET_UNINIT
            or self.near == NR_DISJOINT
            or self.near == NR_MUT_REINIT
            or self.near == NR_EARLY_RETURN
        )
        var mut_self_from = 2 if mut_often else 3  # `mut self` 1/2 or 1/4
        # `deinit self` for 1/6 of the other methods (1/2 for the deinit
        # near misses)
        var deinit_odds = 3 if (
            self.near == NR_DEINIT_DROP or self.near == NR_DEINIT_MOVE
        ) else 1
        var assoc_kind = self.mutant == MU_ASSOC or self.near == NR_ASSOC
        var exc_kind = self.exc_kind()
        self.exceptions = not (
            self.mutant == MU_MUT_UNINIT
            or self.mutant == MU_RET_UNINIT
            or self.near == NR_MUT_REINIT
            or self.near == NR_EARLY_RETURN
        )
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
            # an associated type `comptime E<t>: TrU` for a third (2/3 for
            # the assoc kinds), with any trait as its bound
            var assoc = -1
            if data.draw(integers(0, 2)) < (2 if assoc_kind else 1):
                assoc = pick(data, n_traits)
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
                        -1,
                        -1,
                        [],
                        -1,
                    )
                )
            var methods = List[Int]()
            if make >= 0:
                methods.append(make)
            self.traits.append(
                TraitDecl(
                    parents^, methods^, has_k, make, cap, strengthens, assoc
                )
            )

        # struct headers: capability, fields over earlier structs only
        # (acyclic, like FJ's fields) that are at least as capable,
        # conformances, associated constants
        var n_structs = data.draw(integers(1, 5))
        var vwhere_kind = self.mutant == MU_VWHERE or self.near == NR_VWHERE
        var value_kind = (
            self.mutant == MU_VALUE or self.near == NR_VALUE_EXPR or vwhere_kind
        )
        var where_kind = (
            self.mutant == MU_WHERE
            or self.mutant == MU_WHERE_IMPL
            or self.near == NR_WHERE
        )
        for s in range(n_structs):
            # (2/3 for the where kinds, which need conditional conformances)
            var generic = data.draw(integers(0, 2)) < (2 if where_kind else 1)
            # a value parameter for 1/4 of the others (3/4 for the value
            # kinds), with one or two values
            var valued = not generic and data.draw(integers(0, 3)) < (
                3 if value_kind else 1
            )
            var values = List[Int]()
            if valued:
                for i in range(data.draw(integers(1, 3))):
                    var k = data.draw(integers(-2, 5))
                    if i > 0 and data.draw(booleans()):
                        # a neighbor, so that `V[n + 1]` results are wanted
                        k = values[len(values) - 1] + (
                            1 if data.draw(booleans()) else -1
                        )
                    if not has(values, k):
                        values.append(k)
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
                # (1/4 for the where kinds, leaving traits for a
                # conditional conformance)
                if (
                    data.draw(integers(0, 3)) < (1 if where_kind else 2)
                    and self.traits[t].cap <= cap
                    and (not generic or self.make_ok(t, bound))
                ):
                    traits.append(t)
            # a conditional conformance for a third of the generic structs
            # (2/3 for the where kinds), to a trait not implied otherwise
            var cond = -1
            var cond_req = -1
            if generic and data.draw(integers(0, 2)) < (3 if where_kind else 1):
                var given = self.closure(traits)
                var cands = List[Int]()
                for t in range(n_traits):
                    if (
                        not has(given, t)
                        and self.traits[t].cap <= cap
                        and self.make_ok(t, bound)
                    ):
                        cands.append(t)
                if len(cands) > 0:
                    cond = cands[pick(data, len(cands))]
                    # usually a condition the bound doesn't imply
                    var reqs = List[Int]()
                    for u in range(n_traits):
                        if not self.refines(bound, u):
                            reqs.append(u)
                    # (for the where near miss, half the time one it does,
                    # so that it holds for every type argument)
                    var odds = 2 if self.near == NR_WHERE else 3
                    if len(reqs) > 0 and data.draw(integers(0, 3)) < odds:
                        cond_req = reqs[pick(data, len(reqs))]
                    else:
                        cond_req = pick(data, n_traits)
            var cond_where = where_kind or data.draw(booleans())
            var all_traits = traits.copy()
            if cond >= 0:
                all_traits.append(cond)
            var k_traits = List[Int]()
            var k_values = List[Int]()
            var k_sources = List[Int]()
            for u in self.closure(all_traits):
                if not self.traits[u].has_k:
                    continue
                k_traits.append(u)
                k_values.append(data.draw(integers(-5, 20)))
                var source = -1
                if valued and data.draw(booleans()):
                    source = -2  # (`Self.n + v`)
                if generic and data.draw(integers(0, 3)) > 0:
                    var sources = List[Int]()
                    for v in self.closure([bound]):
                        if self.traits[v].has_k:
                            sources.append(v)
                    if len(sources) > 0:
                        source = sources[pick(data, len(sources))]
                k_sources.append(source)
            var counted = data.draw(booleans())
            var refs = List[Bool]()
            for _ in range(len(fields)):
                refs.append(data.draw(booleans()))
            self.structs.append(
                StructDecl(
                    String("B" if generic else ("V" if valued else "S"), s),
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
                    counted,
                    refs^,
                    valued,
                    values^,
                    cond,
                    cond_req,
                    cond_where,
                    [],
                    [],
                    [],
                    [],
                )
            )

        self.draw_bindings(data)

        # half the time (3/4 for the exception kinds), X2 carries a value
        # of a concrete Copyable struct, `val`
        if self.exceptions and data.draw(integers(0, 3)) < (
            3 if exc_kind else 2
        ):
            var carry = List[Int]()
            for st in range(n_structs):
                if (
                    not self.structs[st].generic
                    and not self.structs[st].valued
                    and self.structs[st].cap >= CAP_C
                ):
                    carry.append(self.intern(STRUCT, st, -1))
            if len(carry) > 0:
                self.carry_ty = carry[pick(data, len(carry))]
                self.n_err = N_ERR + 1

        # trait method signatures (they may mention any struct)
        for t in range(n_traits):
            var lo = 0 if (
                self.traits[t].has_k or self.traits[t].make >= 0
            ) else 1
            for _ in range(data.draw(integers(lo, 2))):
                var m = len(self.methods)
                var self_conv = (
                    CONV_MUT if data.draw(integers(0, 3))
                    >= mut_self_from else CONV_READ
                )
                if (
                    self_conv == CONV_READ
                    and data.draw(integers(0, 5)) < deinit_odds
                ):
                    self_conv = CONV_DEINIT
                var params = List[Int]()
                var convs = List[Int]()
                var mbound = -1
                var mvalue = -1
                var ret = self.draw_signature(
                    data,
                    [t],
                    [],
                    self.p0_ty,
                    mut_often,
                    params,
                    convs,
                    mbound,
                    mvalue,
                )
                self.methods.append(
                    MethodDecl(
                        String("m", m),
                        t,
                        -1,
                        False,
                        self_conv,
                        params^,
                        convs^,
                        ret,
                        data.draw(integers(0, MAX_RANK)),
                        # (no default body for a `deinit self` method: a
                        # counted struct's has to call `_died()`)
                        data.draw(booleans()) and self_conv != CONV_DEINIT,
                        -1,
                        mbound,
                        mvalue,
                        [],
                        self.draw_method_raise(data, self_conv, exc_kind),
                    )
                )
                self.traits[t].methods.append(m)

        # struct own methods
        for s in range(n_structs):
            var bounds = [self.structs[s].bound] if self.structs[
                s
            ].generic else List[Int]()
            var own_ty = self.self_type(s)
            var extra = List[Int]()
            if self.structs[s].valued:
                extra = self.value_family(s, 0)
            for _ in range(data.draw(integers(0, 2))):
                var m = len(self.methods)
                var self_conv = (
                    CONV_MUT if data.draw(integers(0, 3))
                    >= mut_self_from else CONV_READ
                )
                if (
                    self_conv == CONV_READ
                    and data.draw(integers(0, 5)) < deinit_odds
                ):
                    self_conv = CONV_DEINIT
                var params = List[Int]()
                var convs = List[Int]()
                var mbound = -1
                var mvalue = -1
                var ret = self.draw_signature(
                    data,
                    bounds,
                    extra,
                    own_ty,
                    mut_often,
                    params,
                    convs,
                    mbound,
                    mvalue,
                )
                # a quarter of a valued struct's own methods (half for the
                # vwhere kinds) need `where Self.n + c >= k` (or `<=`)
                var mwhere = List[Prop]()
                if self.structs[s].valued and data.draw(integers(0, 3)) < (
                    2 if vwhere_kind else 1
                ):
                    mwhere.append(self.draw_prop(data, s, -1))
                self.methods.append(
                    MethodDecl(
                        String("m", m),
                        -1,
                        s,
                        False,
                        self_conv,
                        params^,
                        convs^,
                        ret,
                        data.draw(integers(0, MAX_RANK)),
                        False,
                        -1,
                        mbound,
                        mvalue,
                        mwhere^,
                        self.draw_method_raise(data, self_conv, exc_kind),
                    )
                )
                self.structs[s].own.append(m)

        # free and generic functions; parameter i < #bounds has type PARAM
        # i, or V[PARAM i] for a value parameter (bound -1), so that Mojo
        # infers each one from the arguments
        var valued_structs = List[Int]()
        for s in range(n_structs):
            if self.structs[s].valued:
                valued_structs.append(s)
        for f in range(data.draw(integers(2 if vwhere_kind else 0, 3))):
            var bounds = List[Int]()
            for _ in range(data.draw(integers(0, 2))):
                bounds.append(pick(data, n_traits))
            # a value parameter for half of them (3/4 for the value kinds)
            var vi = -1
            var vs = -1
            if len(valued_structs) > 0 and data.draw(integers(0, 3)) < (
                3 if value_kind else 2
            ):
                vs = valued_structs[pick(data, len(valued_structs))]
                if len(bounds) == 2:
                    vi = pick(data, 2)
                    bounds[vi] = -1
                else:
                    vi = pick(data, len(bounds) + 1)
                    bounds.insert(vi, -1)
            var pool = self.type_pool(bounds, n_structs)
            var own_ty = -1
            if vi >= 0:
                pool += self.value_family(vs, vi)
                own_ty = self.intern(STRUCT, vs, self.intern(PARAM, vi, -1))
            elif len(bounds) > 0:
                own_ty = self.p0_ty
            var params = List[Int]()
            var convs = List[Int]()
            for i in range(len(bounds)):
                if i == vi:
                    params.append(own_ty)
                else:
                    params.append(self.intern(PARAM, i, -1))
                convs.append(draw_conv(data, mut_often))
            # a quarter of the value parameters (half for the infer mutant)
            # can't be inferred: their parameter is `V[n + 1]` or `V[n -
            # 1]`, and calls write the value
            if vi >= 0 and data.draw(integers(0, 3)) < (
                2 if self.mutant == MU_INFER else 1
            ):
                params[vi] = self.intern(
                    STRUCT,
                    vs,
                    self.offset(
                        self.intern(PARAM, vi, -1),
                        1 if data.draw(booleans()) else -1,
                    ),
                )
            for _ in range(data.draw(integers(0, 2))):
                params.append(self.draw_sig_type(data, pool, own_ty))
                convs.append(draw_conv(data, mut_often))
            # (rising for the vwhere kinds: a function's `where` is drawn for
            # calling the earlier ones)
            var rank = min(f + 1, MAX_RANK) if vwhere_kind else data.draw(
                integers(0, MAX_RANK)
            )
            # a sixth (half for the infer mutant) take one more type
            # parameter, W, that no parameter mentions, so calls write it:
            # its bound has a make the body can build W values with
            var wparam = -1
            if len(bounds) < 3 and data.draw(integers(0, 5)) < (
                3 if self.mutant == MU_INFER else 1
            ):
                var ws = List[Int]()
                for u in range(n_traits):
                    for x in self.closure([u]):
                        var mk = self.traits[x].make
                        if mk >= 0 and self.methods[mk].rank < rank:
                            ws.append(u)
                            break
                if len(ws) > 0:
                    wparam = len(bounds)
                    bounds.append(ws[pick(data, len(ws))])
                    pool = self.type_pool(bounds, n_structs)
                    if vi >= 0:
                        pool += self.value_family(vs, vi)
            # half raise (3/4 for the exception kinds): `raises` (Error) or
            # `raises Xk`
            var raise_ty = -1
            if self.exceptions and data.draw(integers(0, 3)) < (
                3 if exc_kind else 2
            ):
                raise_ty = -2 if data.draw(integers(0, 2)) == 0 else pick(
                    data, self.n_err
                )
            # a quarter of the type parameters also need `where
            # conforms_to(T, TrN)` (half for the where kinds)
            var wheres = List[Int]()
            for i in range(len(bounds)):
                var w = -1
                if bounds[i] >= 0 and data.draw(integers(0, 3)) < (
                    2 if where_kind else 1
                ):
                    # (a trait the bound doesn't imply)
                    var ws = List[Int]()
                    for u in range(n_traits):
                        if not self.refines(bounds[i], u):
                            ws.append(u)
                    if len(ws) > 0:
                        w = ws[pick(data, len(ws))]
                wheres.append(w)
            # half of the value parameters need `where n + c >= k` (or
            # `<=`; 3/4 for the vwhere kinds), with perhaps a `comptime
            # assert` it implies in the body
            var vwhere = List[Prop]()
            var asserts = List[Prop]()
            if vi >= 0 and data.draw(integers(0, 3)) < (
                3 if vwhere_kind else 2
            ):
                for _ in range(data.draw(integers(1, 2))):
                    vwhere.append(self.draw_prop(data, vs, f))
                var reqs = self.reqs_on(vs, f)
                if self.near == NR_VWHERE and len(reqs) > 0:
                    # (the near miss: a `where` stronger than what
                    # another function needs, and an assert of that)
                    var r = reqs[pick(data, len(reqs))].copy()
                    r.form = data.draw(integers(0, 3))
                    var w = r.copy()
                    var bound = r.k - r.c
                    bound += data.draw(integers(1, 2)) * (1 if r.ge else -1)
                    w.c = data.draw(integers(-1, 1))
                    w.k = bound + w.c
                    w.form = data.draw(integers(0, 3))
                    vwhere[0] = w^
                    asserts.append(r^)
                elif data.draw(integers(0, 2)) < (2 if vwhere_kind else 1):
                    asserts.append(self.draw_assert(data, vwhere, vs, f))
            self.fns.append(
                FnDecl(
                    String("g", f),
                    bounds^,
                    params^,
                    convs^,
                    self.draw_sig_type(data, pool, own_ty),
                    rank,
                    -1,
                    wheres^,
                    raise_ty,
                    vwhere^,
                    asserts^,
                    wparam,
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
        self.chances += 1
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

    def in_const_if(self, ctx: Ctx) -> Bool:
        """Whether ctx is inside a branch of an `if` whose condition is a
        constant (literals and associated constants), where use_moved and
        loop_move mutants aren't made: Mojo drops the dead branch before
        it checks uses of moved values, as for a ternary."""
        return ctx.const_if > 0

    def is_const(self, e: Int) -> Bool:
        """Whether e is built from literals and associated constants only
        (Mojo folds it), conservatively."""
        var k = self.exprs[e].kind
        if k == E_LIT or k == E_K or k == E_VALN:
            return True
        if k != E_BIN and k != E_TERN:
            return False
        for kid in self.exprs[e].kids:
            if not self.is_const(kid):
                return False
        return True

    def copy_self_branches(mut self, e: Int, v: Int) -> Int:
        """The ternary e (perhaps nested) with each branch that is the
        variable v itself copied; e itself if there is none."""
        if self.exprs[e].kind != E_TERN:
            return e
        var kids = self.exprs[e].kids.copy()
        var changed = False
        for b in range(2, 4):
            var k = kids[b]
            var nk: Int
            if (
                self.exprs[k].kind == E_VAR
                and self.exprs[k].a == v
                and MARK not in self.exprs[k].text
            ):
                var ty = self.exprs[k].ty
                var text = String(self.exprs[k].text, ".copy()")
                nk = self.add(E_COPY, 0, ty, [k], [], text^)
            else:
                nk = self.copy_self_branches(k, v)
            if nk != k:
                kids[b] = nk
                changed = True
        if not changed:
            return e
        var ops = materialize[CMP_OPS]()
        var text = String(
            "(",
            self.exprs[kids[2]].text,
            " if ",
            self.exprs[kids[0]].text,
            " ",
            ops[self.exprs[e].a],
            " ",
            self.exprs[kids[1]].text,
            " else ",
            self.exprs[kids[3]].text,
            ")",
        )
        return self.add(
            E_TERN, self.exprs[e].a, self.exprs[e].ty, kids^, [], text^
        )

    def where_workaround(self) -> Bool:
        """In a body with a `where`, Mojo gives T a refined type `T(TrN)`
        that it doesn't always identify with T (modular/modular#7811): an
        implicit copy of a T place into a struct's constructor, or a T
        place passed to a call with explicit type arguments, is
        rejected ("cannot implicitly convert 'T(Tr1)' value to
        'T(Tr1)'"), and since nightly 2026112505 so are ternaries whose
        branches involve T ("ambiguous merge", or "'Tr0' value has no
        attribute 'make1'" for a static method of the condition's trait,
        even in an Int ternary). The workaround copies such places with
        `.copy()` and draws no ternaries there."""
        return (
            len(self.facts) > 0
            and getenv("DECL_FUZZ_NO_WHERE_WORKAROUND") == ""
        )

    def where_copies(mut self, kids: List[Int]) -> List[Int]:
        """A constructor's arguments, with `.copy()` on variables and
        fields (of temporaries too) whose types mention a type parameter
        (where_workaround)."""
        if not self.where_workaround():
            return kids.copy()
        var out = List[Int]()
        for k in kids:
            var ty = self.exprs[k].ty
            var ek = self.exprs[k].kind
            if (
                (ek == E_VAR or ek == E_FIELD)
                and self.mentions_param(ty)
                and self.cap_of_any(ty) >= CAP_C
                and MARK not in self.exprs[k].text  # (a mutant's)
            ):
                var text = String(self.exprs[k].text, ".copy()")
                out.append(self.add(E_COPY, 0, ty, [k], [], text^))
            else:
                out.append(k)
        return out^

    def is_place(self, e: Int) -> Bool:
        """Whether e is a place: a variable, a field of a place, or a
        ternary of places."""
        ref x = self.exprs[e]
        if x.kind == E_VAR:
            return True
        if x.kind == E_FIELD:
            return self.is_place(x.kids[0])
        if x.kind == E_TERN:
            return self.is_place(x.kids[2]) and self.is_place(x.kids[3])
        return False

    def mark(mut self, e: Int) -> Int:
        """Marks e as the mutation: the line holding it gets `# MUTANT`."""
        self.exprs[e].text = String(MARK, self.exprs[e].text)
        self.mutated = True
        return e

    def mutation_state(self) -> Int:
        """For backtracking: a mutation (or near miss) in a discarded
        attempt is undone."""
        return (
            Int(self.mutated)
            + 2 * Int(self.near_made)
            + 4 * (self.loop_mark + 1)
            + 64 * (self.keep_dead + 1)
        )

    def restore_mutation(mut self, state: Int):
        self.mutated = state % 2 == 1
        self.near_made = (state // 2) % 2 == 1
        self.loop_mark = (state // 4) % 16 - 1
        self.keep_dead = state // 64 - 1

    def wants_near(self, kind: Int) -> Bool:
        """Whether a near miss of this kind is still to be made."""
        return self.near == kind and not self.near_made

    def near_chance(
        mut self, mut data: ConjectureData, kind: Int
    ) raises -> Bool:
        """Whether to make the near miss here (as `chance`)."""
        if not self.wants_near(kind):
            return False
        self.chances += 1
        return data.draw(integers(0, MU_ODDS - 1)) == 0

    def mark_near(mut self, e: Int) -> Int:
        """Marks e as the near miss: its line gets `# NEAR`."""
        self.exprs[e].text = String(MARK_NEAR, self.exprs[e].text)
        self.near_made = True
        return e

    def uses_var(self, e: Int, v: Int) -> Bool:
        """Whether e mentions variable v."""
        ref x = self.exprs[e]
        if (x.kind == E_VAR or x.kind == E_MOVE) and x.a == v:
            return True
        for k in x.kids:
            if self.uses_var(k, v):
                return True
        return False

    def borrows_var(self, e: Int, v: Int) -> Bool:
        """Whether e is a place rooted at v (passed read, it would borrow
        v rather than be a value)."""
        ref x = self.exprs[e]
        if x.kind == E_VAR:
            return x.a == v
        if x.kind == E_FIELD:
            return self.borrows_var(x.kids[0], v)
        if x.kind == E_TERN:
            return self.borrows_var(x.kids[2], v) or self.borrows_var(
                x.kids[3], v
            )
        return False

    def disjoint_places(mut self, ctx: Ctx, ty: Int) -> List[Int]:
        """For NR_DISJOINT: fields of type ty of a variable one of whose
        fields was passed `mut` in this statement, other than those."""
        var out = List[Int]()
        for q in ctx.taken:
            if q % 64 == 0:
                continue
            var v = q // 64
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                var p = v * 64 + f + 1
                if fs[f] == ty and not has(ctx.taken, p) and not has(out, p):
                    out.append(p)
        return out^

    def read_alias_places(mut self, ctx: Ctx, ty: Int) -> List[Int]:
        """For NR_READ_ALIAS: places of type ty (not Int: Ints are passed
        by value) overlapping a variable already read in this statement."""
        var out = List[Int]()
        if ty == self.int_ty:
            return out^
        for v in range(len(ctx.names)):
            if not ctx.touched[v] or not ctx.live[v] or ctx.excl[v]:
                continue
            if ctx.types[v] == ty:
                out.append(v * 64)
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                if fs[f] == ty:
                    out.append(v * 64 + f + 1)
        return out^

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
        """Places of type ty in live read variables (MU_MUT_READ; not ones
        frozen in a `try`, nor a handler's binding, which a typed handler
        owns)."""
        var out = List[Int]()
        for v in range(ctx.freeze_base, len(ctx.names)):
            if (
                ctx.kinds[v] != V_READ
                or not ctx.live[v]
                or ctx.excl[v]
                or self.tkind[ctx.types[v]] == ERR
            ):
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
        if (
            self.is_valued(ty)
            and self.wants(MU_VALUE)
            and self.chance(data, MU_VALUE)
        ):
            # `V[k + d](...)`, `V[Self.n + d](...)` or `V[n + d](...)`
            var d = data.draw(integers(1, 3))
            var vtext = self.val_str(
                self.offset(self.targ[ty], d), ctx.param_names
            )
            var fts = self.fields_of(ty)
            var vars = List[Int](length=len(fts), fill=CONV_VAR)
            var kids = self.gen_args(data, ctx, fts, vars, size - 1, False)
            var text = String(
                self.structs[self.tid[ty]].name,
                "[",
                vtext,
                "](",
                self.args_text(kids, 0),
                ")",
            )
            return self.mark(self.add(E_NEW, 0, ty, kids^, [], text^))
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
        MU_REF_ORIGIN, MU_MISSING, MU_SIG and MU_CAP."""
        var kind = self.mutant
        if kind == MU_REF_ORIGIN:
            # (struct * 64 + field) of an accessor; its origin becomes
            # `self` or another field
            var cands = List[Int]()
            for st in range(len(self.structs)):
                for f in range(len(self.structs[st].refs)):
                    if self.structs[st].refs[f]:
                        cands.append(st * 64 + f)
            if len(cands) == 0:
                return
            self.bad_ref = cands[pick(data, len(cands))]
            var f = self.bad_ref % 64
            var n = len(self.structs[self.bad_ref // 64].fields)
            var origins: List[String] = ["self"]
            for g in range(n):
                if g != f:
                    origins.append(String("self.f", g))
            self.bad_origin = origins[pick(data, len(origins))]
            self.mutated = True
            return
        if kind == MU_ASSOC:
            # (struct * 64 + binding, type): a concrete type that doesn't
            # conform to the bound
            var concrete: List[Int] = [self.int_ty, self.res_ty]
            for x in range(len(self.structs)):
                concrete += self.concrete_types(x)
            var cands = List[Int]()
            for st in range(len(self.structs)):
                for i in range(len(self.structs[st].a_traits)):
                    var at = self.structs[st].a_traits[i]
                    var u = self.traits[at].assoc
                    # (not one the bodies may use the bound's own
                    # associated type through, `Self.E0.E1`, nor one a
                    # signature mentions, `B2[Self.E0]` in the struct's
                    # implementation is written with the binding: a type
                    # that doesn't conform is an error at that use first)
                    var used = self.traits[u].assoc >= 0
                    for m in range(len(self.methods)):
                        used = used or self.sig_has_assoc(m, at)
                    if used:
                        continue
                    for t in concrete:
                        if not self.conforms(t, u, []):
                            cands.append((st * 64 + i) * 1024 + t)
            if len(cands) == 0:
                return
            var c = cands[pick(data, len(cands))]
            var st = c // (64 * 1024)
            self.structs[st].a_types[(c // 1024) % 64] = c % 1024
            self.mark_struct = st
            self.mutated = True
            return
        if kind == MU_WHERE_IMPL:
            # (struct * 64 + index, trait): a required method's gated
            # implementation, and a trait refining the condition's, not
            # implied by the struct's bound (else it would hold anyway)
            var cands = List[Int]()
            for st in range(len(self.structs)):
                ref sd = self.structs[st]
                if sd.cond < 0 or not sd.cond_where:
                    continue
                for i in range(len(sd.impl_methods)):
                    var m = sd.impl_methods[i]
                    if self.methods[m].has_default or not self.is_gated(st, m):
                        continue
                    for u in range(len(self.traits)):
                        if (
                            u != sd.cond_req
                            and self.refines(u, sd.cond_req)
                            and not self.refines(sd.bound, u)
                        ):
                            cands.append((st * 64 + i) * 64 + u)
            if len(cands) == 0:
                return
            var c = cands[pick(data, len(cands))]
            self.bad_where = c // 64
            self.bad_where_req = c % 64
            self.mark_struct = self.bad_where // 64
            self.mark_impl = self.bad_where % 64
            self.mutated = True
            return
        if kind == MU_MISSING:
            # (struct, index, 0 for a method, 1 for a constant or 2 for an
            # associated type)
            var cands = List[Int]()
            for s in range(len(self.structs)):
                ref sd = self.structs[s]
                for i in range(len(sd.impl_methods)):
                    if not self.methods[sd.impl_methods[i]].has_default:
                        cands.append((s * 64 + i) * 3)
                for i in range(len(sd.k_traits)):
                    cands.append((s * 64 + i) * 3 + 1)
                for i in range(len(sd.a_traits)):
                    # (not one an implementation's signature names: Mojo
                    # would stop at `-> Self.E0` there, "no attribute")
                    var named = False
                    for m in sd.impl_methods:
                        if self.sig_has_assoc(m, sd.a_traits[i]):
                            named = True
                    if not named:
                        cands.append((s * 64 + i) * 3 + 2)
            if len(cands) == 0:
                return
            var c = cands[pick(data, len(cands))]
            var s = c // 192
            var i = (c // 3) % 64
            if c % 3 == 0:
                _ = self.structs[s].impl_methods.pop(i)
                _ = self.structs[s].impl_bodies.pop(i)
            elif c % 3 == 1:
                _ = self.structs[s].k_traits.pop(i)
                _ = self.structs[s].k_values.pop(i)
                _ = self.structs[s].k_sources.pop(i)
            else:
                _ = self.structs[s].a_traits.pop(i)
                _ = self.structs[s].a_types.pop(i)
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
            var args = self.impl_args(s, self.structs[s].impl_methods[i])
            # concrete types, which substitution leaves alone
            var concrete: List[Int] = [self.int_ty, self.res_ty]
            for x in range(len(self.structs)):
                concrete += self.concrete_types(x)
            # what to change: the result type, the convention of `self`,
            # a parameter's type or convention, or a generic method's bound
            # (another trait, stricter or not, is an error)
            var changes: List[Int] = [0]
            if not md.is_static:
                if md.self_conv == CONV_READ:
                    changes.append(1)
                if len(md.params) > 0:
                    changes += [2, 3]
            if md.mbound >= 0 and len(self.traits) > 1:
                changes += [4, 4]
            var change = changes[pick(data, len(changes))]
            if change == 4:
                var others = List[Int]()
                for t in range(len(self.traits)):
                    if t != md.mbound:
                        others.append(t)
                md.mbound = others[pick(data, len(others))]
            elif change == 0:
                var old = self.subst(md.ret, args)
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
                    var old = self.subst(md.params[j], args)
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
        var bounds: List[Int] = [t]
        var names: List[String] = ["Self"]
        bounds += self.own_bounds(m)
        names += self.own_names(m)
        var pool = self.type_pool(bounds, len(self.structs))
        if self.methods[m].mvalue >= 0:
            pool += self.value_family(self.methods[m].mvalue, self.k_index(m))
        var ctx = Ctx(bounds^, names^, rank, -1, pool^)
        ctx.raise_ty = self.methods[m].raise_ty
        ctx.push("self", self.p0_ty, kind_of_conv(self.methods[m].self_conv))
        self.push_params(
            ctx, self.methods[m].params, self.methods[m].convs, "p"
        )
        return ctx^

    def self_type(mut self, s: Int) -> Int:
        if self.structs[s].generic or self.structs[s].valued:
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
        var valued = self.structs[s].valued
        var names = ["Self.T"] if generic else (
            ["Self.n"] if valued else List[String]()
        )
        if self.is_generic_method(m):
            # U is PARAM 1 (-1: PARAM 0 is a value or unused); an
            # implementation of a trait's may call it W (a rename near
            # miss)
            if len(bounds) == 0:
                bounds.append(-1)
                if not valued:
                    names.append("_")
            bounds += self.own_bounds(m)
            var rename = (
                self.methods[m].mbound >= 0
                and self.methods[m].trait_id >= 0
                and self.near_chance(data, NR_RENAME)
            )
            names += self.own_names(m, "W" if rename else "U")
            if rename:
                self.near_made = True
        var pool = self.type_pool(bounds, len(self.structs))
        if valued:
            pool += self.value_family(s, 0)
        if self.methods[m].mvalue >= 0:
            pool += self.value_family(self.methods[m].mvalue, self.k_index(m))
        var ctx = Ctx(
            bounds^,
            names^,
            rank,
            self_ty if data.draw(booleans()) else -1,
            pool^,
        )
        ctx.self_ty = self_ty
        ctx.raise_ty = self.impl_raise(s, m)
        if not self.methods[m].is_static:
            ctx.push("self", self_ty, kind_of_conv(self.methods[m].self_conv))
        var params = self.methods[m].params.copy()
        if self.methods[m].trait_id >= 0:
            params = self.subst_all(params, self.impl_args(s, m))
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
        var args = self.impl_args(s, m)
        return self.subst(self.methods[m].ret, args)

    def impl_args(mut self, s: Int, m: Int) -> List[Int]:
        """What to substitute into trait method m's signature in struct s's
        implementation: Self, and U (PARAM 1) for itself."""
        var out: List[Int] = [self.self_type(s)]
        for i in range(self.n_own(m)):
            out.append(self.intern(PARAM, i + 1, -1))
        return out^

    def gen_body(
        mut self,
        mut data: ConjectureData,
        var ctx: Ctx,
        ret: Int,
        size: Int = BODY_SIZE,
        root: Bool = False,
    ) raises -> Int:
        # entry points (root) drive everything: give them more statements
        ctx.ret = ret
        var stmts = self.gen_block(data, ctx, 5 if root else 3)
        stmts += self.mut_reinits(data, ctx)
        if self.deinit_body and ctx.live[0]:
            stmts += self.deinit_end(data, ctx)
        ctx.new_statement()
        var r: Int
        if root:
            r = self.gen(data, ctx, ret, size, P_OWNED, True, True)
        else:
            r = self.gen_typed(data, ctx, ret, size, P_OWNED, True)
        if self.keep_dead >= 0:
            # a mut_uninit mutant: Mojo reports the `mut` argument left
            # uninitialized at the return
            self.exprs[r].text = String(MARK, self.exprs[r].text)
            self.keep_dead = -1
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
        self.bodies.append(
            Body(stmts^, r, ctx.self_print, self.died, ctx.param_names.copy())
        )
        return len(self.bodies) - 1

    def is_deinit_self(self, v: Int) -> Bool:
        """Whether v is self in a `deinit self` method's body: left moved,
        it isn't an error (no mut_uninit, ret_uninit mutants)."""
        return self.deinit_body and v == 0

    def mut_reinits(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> List[Int]:
        """At the end of a body, `p = e` for each `mut` argument moved out
        (by the path kinds). A mut_uninit mutant may leave one moved
        instead, and a mut_reinit near miss may be this
        reinitialization."""
        var out = List[Int]()
        for v in range(len(ctx.names)):
            if ctx.kinds[v] != V_MUT or ctx.live[v] or v == self.keep_dead:
                continue
            if not self.is_deinit_self(v) and self.chance(data, MU_MUT_UNINIT):
                self.mutated = True
                self.keep_dead = v
                continue
            var st = self.gen_reinit(data, ctx, v)
            if self.near_chance(data, NR_MUT_REINIT):
                _ = self.mark_near(self.stmts[st].target)
            out.append(st)
        return out^

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

    def start_body(mut self, s: Int, m: Int):
        """Before generating struct s's body of method m: whether it's a
        `deinit self` method's, and whether its returns call `_died()`."""
        self.deinit_body = self.methods[m].self_conv == CONV_DEINIT
        self.died = self.deinit_body and self.is_counted(s)

    def is_counted(self, st: Int) -> Bool:
        """Whether struct st is printed counted: drawn so, `Movable` or
        `Copyable`, and not a struct a mutant marks (its own copy
        constructor would fail on an unmarked line)."""
        return (
            self.structs[st].counted
            and self.structs[st].cap <= CAP_C
            and st != self.mark_struct
        )

    def deinit_end(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> List[Int]:
        """At the end of a `deinit self` method's body (self live), perhaps
        a near miss: deinit_drop moves a field out of self (`var v =
        self.f^`, the rest of self is destroyed), deinit_move self itself
        (`var v = self^`; v is destroyed with the struct's `__deinit__`, so
        the return doesn't call `_died()`). self isn't used again."""
        var out = List[Int]()
        if self.wants_near(NR_DEINIT_DROP):
            var fields = self.fields_of(ctx.types[0])
            var cands = List[Int]()
            for f in range(len(fields)):
                if fields[f] != self.int_ty:  # (`^` on an Int copies it)
                    cands.append(f)
            if len(cands) > 0 and self.near_chance(data, NR_DEINIT_DROP):
                var f = cands[pick(data, len(cands))]
                ctx.new_statement()
                var place = self.place_expr(ctx, 0, f)
                var text = String(self.exprs[place].text, "^")
                var mv = self.mark_near(
                    self.add(E_FMOVE, 0, fields[f], [place], [], text^)
                )
                var name = String("v", ctx.counter)
                ctx.counter += 1
                ctx.push(name.copy(), fields[f], V_OWNED)
                out.append(
                    self.add_stmt(Stmt(S_VAR, -1, mv, -1, 0, [], [], name^))
                )
                ctx.live[0] = False
                ctx.move_depth[0] = -2
        elif self.near_chance(data, NR_DEINIT_MOVE):
            var st = self.move_stmt(ctx, 0)
            _ = self.mark_near(self.stmts[st].e)
            out.append(st)
            self.died = False
        return out^

    def start_alias(mut self, mut data: ConjectureData, s: Int) raises:
        """For NR_ASSOC, perhaps make struct s the one whose declarations
        and bodies write one of its bindings as `Self.E<t>`."""
        if len(self.structs[s].a_traits) == 0 or not self.near_chance(
            data, NR_ASSOC
        ):
            return
        var i = pick(data, len(self.structs[s].a_traits))
        self.alias_struct = s
        self.alias_saved = self.structs[s].a_types[i]
        self.alias_saved_text = String("Self.E", self.structs[s].a_traits[i])
        self.alias_ty = self.alias_saved
        self.alias_text = self.alias_saved_text
        self.near_made = True

    def plan_impls(mut self, mut data: ConjectureData) raises:
        """Which trait methods each struct implements (the required ones,
        and half the defaults, which it overrides), and what each
        implementation raises: a quarter of those of raising methods raise
        nothing. A raise_impl mutant's (of a method without a default)
        raises what the trait's doesn't allow."""
        var cands = List[Int]()  # (struct * 64 + index)
        for s in range(len(self.structs)):
            var all_traits = self.structs[s].traits.copy()
            if self.structs[s].cond >= 0:
                all_traits.append(self.structs[s].cond)
            for t in self.closure(all_traits):
                for m in self.traits[t].methods.copy():
                    if self.methods[m].has_default and not data.draw(
                        booleans()
                    ):
                        continue
                    var r = self.methods[m].raise_ty
                    if r != -1 and data.draw(integers(0, 3)) == 0:
                        r = -1
                    # (not overrides of defaults: Mojo ignores one that
                    # raises more, and every call runs the default)
                    if (
                        not self.methods[m].is_static
                        and not self.methods[m].has_default
                        and self.methods[m].self_conv != CONV_DEINIT
                    ):
                        cands.append(s * 64 + len(self.structs[s].impl_plan))
                    self.structs[s].impl_plan.append(m)
                    self.structs[s].impl_raises.append(r)
        if not self.wants(MU_RAISE_IMPL) or len(cands) == 0:
            return
        var c = cands[pick(data, len(cands))]
        var s = c // 64
        var i = c % 64
        var r = self.methods[self.structs[s].impl_plan[i]].raise_ty
        var bad = List[Int]()
        if r != -2:
            bad.append(-2)
        for k in range(self.n_err):
            if k != r:
                bad.append(k)
        self.structs[s].impl_raises[i] = bad[pick(data, len(bad))]
        self.mark_struct = s
        self.mark_impl = i
        self.mutated = True

    def impl_raise(self, s: Int, m: Int) -> Int:
        """What struct s's body of method m raises: an own method's, or its
        implementation's of a trait's."""
        var i = index_of(self.structs[s].impl_plan, m)
        if i >= 0:
            return self.structs[s].impl_raises[i]
        return self.methods[m].raise_ty

    def method_raise(self, m: Int, recv: Int) -> Int:
        """What calling method m on a receiver of type recv raises, to
        Mojo: a struct's implementation's (which may raise nothing), else
        the trait's declaration."""
        if self.methods[m].trait_id < 0 or self.tkind[recv] != STRUCT:
            return self.methods[m].raise_ty
        return self.impl_raise(self.tid[recv], m)

    def draw_bodies(mut self, mut data: ConjectureData) raises:
        self.plan_impls(data)
        # trait defaults
        for m in range(len(self.methods)):
            if self.methods[m].has_default:
                var ctx = self.trait_ctx(m)
                var ret = self.methods[m].ret
                self.methods[m].body = self.gen_body(data, ctx^, ret)
        # trait methods each struct implements: the required ones, and
        # defaults it overrides (impl_plan)
        for s in range(len(self.structs)):
            self.start_alias(data, s)
            for m in self.structs[s].impl_plan.copy():
                # (a gated implementation knows its condition)
                if self.where_text(s, m) != "":
                    self.facts = [self.structs[s].cond_req]
                var ctx = self.struct_ctx(data, s, m)
                var ret = self.body_ret(s, m)
                self.start_body(s, m)
                var b = self.gen_body(data, ctx^, ret)
                self.facts = []
                self.structs[s].impl_methods.append(m)
                self.structs[s].impl_bodies.append(b)
            self.alias_ty = -1
        # own methods
        for s in range(len(self.structs)):
            if s == self.alias_struct:
                self.alias_ty = self.alias_saved
            for m in self.structs[s].own.copy():
                var ctx = self.struct_ctx(data, s, m)
                var ret = self.methods[m].ret
                self.start_body(s, m)
                # (its `where` is known in its body)
                for pr in self.methods[m].vwhere:
                    self.vfacts.append(Self.prop_key(0, pr.c, pr.ge, pr.k))
                self.methods[m].body = self.gen_body(data, ctx^, ret)
                self.vfacts = []
            self.alias_ty = -1
        self.deinit_body = False
        self.died = False
        # functions
        for f in range(len(self.fns)):
            var bounds = self.fns[f].bounds.copy()
            var rank = self.fns[f].rank
            for i in range(len(self.fns[f].wheres)):
                if self.fns[f].wheres[i] >= 0:
                    self.facts.append(i * 64 + self.fns[f].wheres[i])
            var vi = self.vw_fn_index(f)
            for pr in self.fns[f].vwhere:
                self.vfacts.append(Self.prop_key(vi, pr.c, pr.ge, pr.k))
            for pr in self.fns[f].asserts:
                var key = Self.prop_key(vi, pr.c, pr.ge, pr.k)
                if not has(self.vfacts, key):
                    self.vfacts_assert.append(key)
            if vi >= 0:
                self.cif_fn = f
            var pool = self.fn_pool(f)
            var ctx = Ctx(bounds^, self.fn_names(f), rank, -1, pool^)
            ctx.raise_ty = self.fns[f].raise_ty
            self.push_params(ctx, self.fns[f].params, self.fns[f].convs, "p")
            var ret = self.fns[f].ret
            self.fns[f].body = self.gen_body(data, ctx^, ret)
            self.facts = []
            self.vfacts = []
            self.vfacts_assert = []
            self.cif_fn = -1
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
        keep_moved: Int = -1,
        reinit_in: Int = -1,
        exit: Int = -1,
    ) raises -> List[Int]:
        """Statements; in a nested block, variables live at its start are
        live at its end (moved ones are reinitialized), and its locals go
        out of scope. For a branch of an `if` with a plan, keep_moved is a
        variable the block moves (unless a statement does) and leaves
        moved, and reinit_in one moved before it that it reinitializes
        (unless a statement does). With exit (S_RETURN, S_BREAK or
        S_CONTINUE), the block ends with that statement (`returning_end`,
        `loop_exit_end`)."""
        var n_outer = len(ctx.names)
        var live_at_start = ctx.live.copy()
        var depth_at_start = ctx.move_depth.copy()
        var out = List[Int]()
        var moved = -1
        var to_use = -1  # a variable moved for a use_moved mutant
        var to_reinit = -1  # a variable moved for a reinit near miss
        var near_ref = -1  # (for ref_reinit, the binding to use after it)
        var n = data.draw(integers(0, n_max))
        var plan_at = -1  # (before which statement the plan acts)
        if keep_moved >= 0 or reinit_in >= 0:
            plan_at = data.draw(integers(0, n))
        for i in range(n):
            if i == plan_at:
                out += self.plan_step(data, ctx, keep_moved, reinit_in)
            var setup = self.setup_movable(ctx)
            if len(setup) > 0 and data.draw(integers(0, MU_ODDS - 1)) == 0:
                # a move for a later `if` (or the body's end) to
                # reinitialize, assignable in this block
                var v = setup[pick(data, len(setup))]
                out.append(self.move_stmt(ctx, v))
                ctx.move_depth[v] = ctx.depth
            if data.draw(integers(0, MU_ODDS - 1)) == 0:
                var places = self.ref_places(ctx)
                if len(places) > 0:
                    var p = places[pick(data, len(places))]
                    out.append(self.ref_stmt(data, ctx, p // 64, p % 64 - 1))
            if to_reinit >= 0 and data.draw(booleans()):
                out += self.reinit_stmts(data, ctx, to_reinit, near_ref)
                to_reinit = -1
                near_ref = -1
            if to_reinit < 0 and self.wants_near(NR_REF_REINIT):
                # `ref rN = x` (or x.fK), x moved, reinitialized later in
                # the block, then rN used
                var owned = List[Int]()
                for v in self.owned_vars(ctx, len(ctx.names)):
                    if not ctx.from_tuple[v]:  # (see Ctx.from_tuple)
                        owned.append(v)
                if len(owned) > 0 and self.near_chance(data, NR_REF_REINIT):
                    to_reinit = owned[pick(data, len(owned))]
                    var nf = len(self.fields_of(ctx.types[to_reinit]))
                    var f = data.draw(integers(-1, nf - 1))
                    var rs = self.ref_stmt(data, ctx, to_reinit, f)
                    _ = self.mark_near(self.stmts[rs].e)
                    near_ref = len(ctx.ref_names) - 1
                    out.append(rs)
                    out.append(self.move_stmt(ctx, to_reinit))
            if to_reinit < 0 and self.wants_near(NR_REINIT):
                # move a variable (in a loop, perhaps an outer one), and
                # reinitialize it later in the block
                var owned = self.owned_vars(ctx, len(ctx.names))
                if len(owned) > 0 and self.near_chance(data, NR_REINIT):
                    to_reinit = owned[pick(data, len(owned))]
                    var st = self.move_stmt(ctx, to_reinit)
                    var e = self.stmts[st].e
                    self.exprs[e].text = String(MARK_NEAR, self.exprs[e].text)
                    out.append(st)
            if (
                self.wants_near(NR_DISJOINT)
                or self.wants_near(NR_READ_ALIAS)
                or self.wants_near(NR_MOVE_COPY)
            ):
                out += self.near_call_stmts(data, ctx)
            if self.wants_near(NR_DISCARD_MOVE):
                # `_ = x^`, which leaves x alive, then a use of x
                var owned = self.owned_vars(ctx, len(ctx.names))
                if len(owned) > 0 and self.near_chance(data, NR_DISCARD_MOVE):
                    var v = owned[pick(data, len(owned))]
                    ctx.new_statement()
                    var text = String(ctx.names[v], "^")
                    var e = self.add(E_MOVE, v, ctx.types[v], [], [], text^)
                    out.append(
                        self.add_stmt(
                            Stmt(
                                S_EXPR, -1, self.mark_near(e), -1, 0, [], [], ""
                            )
                        )
                    )
                    var use = self.place_expr(ctx, v, -1)
                    out.append(
                        self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                    )
            if (
                to_use < 0
                and self.wants(MU_USE_MOVED)
                and not self.in_const_if(ctx)
                and data.draw(integers(0, MU_ODDS - 1)) == 0
            ):
                # few variables are moved, so move one (it isn't
                # reinitialized before the block's end); in a loop, a local
                # one (an outer one would make a loop_move mutant too)
                var owned = List[Int]()
                for v in self.owned_vars(ctx, len(ctx.names)):
                    if not loop or v >= n_outer:
                        owned.append(v)
                if len(owned) > 0:
                    to_use = owned[pick(data, len(owned))]
                    out.append(self.move_stmt(ctx, to_use))
            if loop and self.wants(MU_LOOP_MOVE) and not self.in_const_if(ctx):
                # move an outer variable, and don't reinitialize it: the
                # next iteration uses it (the whole loop is marked)
                var outer = self.loop_movable(ctx, n_outer, out)
                if len(outer) > 0 and self.chance(data, MU_LOOP_MOVE):
                    moved = outer[pick(data, len(outer))]
                    out.append(self.loop_move_stmt(data, ctx, moved))
                    self.mutated = True
                    self.loop_mark = ctx.depth
            if loop and self.wants_loop_exit(ctx) and ctx.no_exit == 0:
                out += self.exit_if(data, ctx, -1)
            if (
                self.wants(MU_RET_UNINIT)
                and not self.in_const_if(ctx)
                and ctx.no_exit == 0
            ):
                out += self.exit_if(data, ctx, S_RETURN)
            if self.wants_partial(ctx):
                out += self.partial_stmts(data, ctx)
            out += self.raise_if(data, ctx)
            if self.wants(MU_USE_MOVED) and not self.in_const_if(ctx):
                var dead = self.moved_vars(ctx)
                if len(dead) > 0 and self.chance(data, MU_USE_MOVED):
                    var v = dead[pick(data, len(dead))]
                    var e = self.mark(self.spell(data, ctx, v, -1))
                    out.append(
                        self.add_stmt(Stmt(S_USE, -1, e, -1, 0, [], [], ""))
                    )
            out.append(self.gen_stmt(data, ctx))
        out += self.plan_step(data, ctx, keep_moved, reinit_in)
        if loop and self.wants(MU_LOOP_MOVE) and not self.in_const_if(ctx):
            # no chance was taken: move one last
            var outer = self.loop_movable(ctx, n_outer, out)
            if len(outer) > 0:
                self.chances += 1
                moved = outer[pick(data, len(outer))]
                out.append(self.loop_move_stmt(data, ctx, moved))
                self.mutated = True
                self.loop_mark = ctx.depth
        if to_reinit >= 0:
            out += self.reinit_stmts(data, ctx, to_reinit, near_ref)
        if to_use >= 0 and self.wants(MU_USE_MOVED):
            # no chance was taken after the move
            self.chances += 1
            var e = self.mark(self.spell(data, ctx, to_use, -1))
            out.append(self.add_stmt(Stmt(S_USE, -1, e, -1, 0, [], [], "")))
        if exit >= 0:
            if exit == S_RETURN:
                out += self.returning_end(data, ctx)
            else:
                out += self.loop_exit_end(data, ctx, exit)
            # (the block doesn't fall through: the code after it sees the
            # variables as they were at its start)
            for v in range(n_outer):
                ctx.live[v] = live_at_start[v]
                ctx.move_depth[v] = depth_at_start[v]
            if ctx.depth > 0:
                ctx.drop_refs(ctx.depth, n_outer)
            ctx.truncate(n_outer)
            return out^
        if ctx.depth > 0:
            # (no moves in the reinitializations: one could move a
            # variable already passed over, which the next iteration uses
            # in a loop's body, and which the next case of a `match`, or an
            # `if`'s other branch, could reinitialize, so that it looks
            # live after the statement)
            ctx.no_move += 1
            for v in range(n_outer):
                if (
                    live_at_start[v]
                    and not ctx.live[v]
                    and v != moved
                    and v != keep_moved
                    and v != self.keep_dead
                ):
                    out.append(self.gen_reinit(data, ctx, v))
            ctx.no_move -= 1
            ctx.drop_refs(ctx.depth, n_outer)
            ctx.truncate(n_outer)
        return out^

    def near_callees(
        mut self, ctx: Ctx, ctors: Bool, disjoint: Bool = False
    ) -> List[Callee]:
        """What a near miss's call can be: functions that aren't generic,
        methods with a read receiver (argument 0), and with ctors, struct
        constructors. With disjoint, also generic functions (instantiated
        with each choice of conforming types from the pool, up to 64) and
        methods with a `mut self` receiver."""
        var out = List[Callee]()
        for f in range(len(self.fns)):
            # (not raising ones: a near miss's call isn't in a `try`)
            if self.fns[f].rank >= ctx.rank or self.fns[f].raise_ty != -1:
                continue
            var bounds = self.fns[f].bounds.copy()
            if len(bounds) == 0:
                out.append(
                    Callee(
                        C_FN,
                        f,
                        self.fns[f].ret,
                        self.fns[f].params.copy(),
                        self.fns[f].convs.copy(),
                        [],
                    )
                )
                continue
            if not disjoint:
                continue
            var choices = List[List[Int]]()
            var total = 1
            for i in range(len(bounds)):
                choices.append(self.targ_choices(ctx, f, i))
                total *= len(choices[i])
            for c in range(min(total, 64)):
                var targs = List[Int]()
                var r = c
                for i in range(len(bounds)):
                    targs.append(choices[i][r % len(choices[i])])
                    r //= len(choices[i])
                var params = self.subst_all(self.fns[f].params.copy(), targs)
                var ret = self.subst(self.fns[f].ret, targs)
                out.append(
                    Callee(
                        C_FN,
                        f,
                        ret,
                        params^,
                        self.fns[f].convs.copy(),
                        targs^,
                    )
                )
        for r in ctx.pool.copy():
            if self.tkind[r] != STRUCT:
                continue
            for m in self.methods_on(r, ctx.bounds):
                var conv = self.methods[m].self_conv
                if (
                    self.methods[m].is_static
                    or self.is_generic_method(m)
                    or not (
                        conv == CONV_READ or (disjoint and conv == CONV_MUT)
                    )
                    or self.methods[m].rank >= ctx.rank
                    or self.method_raise(m, r) != -1
                ):
                    continue
                var params: List[Int] = [r]
                params += self.method_params(m, r)
                var convs: List[Int] = [conv]
                convs += self.methods[m].convs.copy()
                out.append(
                    Callee(
                        C_METHOD, m, self.method_ret(m, r), params^, convs^, []
                    )
                )
            if ctors:
                var fs = self.fields_of(r)
                out.append(
                    Callee(
                        C_CTOR,
                        r,
                        r,
                        fs.copy(),
                        List[Int](length=len(fs), fill=CONV_VAR),
                        [],
                    )
                )
        return out^

    def call_with(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        c: Callee,
        pos: List[Int],
        fixed: List[Int],
    ) raises -> Int:
        """A call of c whose arguments at pos are fixed (the rest drawn;
        the caller keeps them off the fixed arguments' variables)."""
        var kids = List[Int]()
        var mut_call = has(c.convs, CONV_MUT)
        for n in range(len(c.params)):
            var at = -1
            for q in range(len(pos)):
                if pos[q] == n:
                    at = q
            if at >= 0:
                kids.append(fixed[at])
            elif c.kind == C_METHOD and n == 0:
                kids.append(self.gen(data, ctx, c.params[0], 1, P_READ))
            else:
                kids.append(
                    self.gen_arg(
                        data, ctx, c.params[n], c.convs[n], 1, mut_call
                    )
                )
        if c.kind == C_FN:
            var text = self.fns[c.id].name
            if len(c.tys) > 0:
                text += "["
                for i in range(len(c.tys)):
                    if i > 0:
                        text += ", "
                    text += self.cty(c.tys[i], ctx)
                text += "]"
            text += String("(", self.args_text(kids, 0), ")")
            return self.add(E_CALL, c.id, c.ret, kids^, c.tys.copy(), text^)
        if c.kind == C_CTOR:
            kids = self.where_copies(kids)
            var text = String(
                self.cty(c.id, ctx), "(", self.args_text(kids, 0), ")"
            )
            return self.add(E_NEW, 0, c.id, kids^, [], text^)
        var text = String(
            self.exprs[kids[0]].text,
            ".",
            self.methods[c.id].name,
            "(",
            self.args_text(kids, 1),
            ")",
        )
        return self.add(E_METHOD, c.id, c.ret, kids^, [], text^)

    def near_var(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        kinds: List[Int],
        mut out: List[Int],
    ) raises -> Int:
        """A live variable of type ty and one of these kinds, half the time
        one already there, else a new local (`var vN = e`, added to out)."""
        var vs = List[Int]()
        for v in range(len(ctx.names)):
            if ctx.live[v] and ctx.types[v] == ty and has(kinds, ctx.kinds[v]):
                vs.append(v)
        if len(vs) > 0 and data.draw(booleans()):
            return vs[pick(data, len(vs))]
        ctx.new_statement()
        var init = self.gen(data, ctx, ty, BODY_SIZE - 1, P_OWNED, False, True)
        var name = String("v", ctx.counter)
        ctx.counter += 1
        var v = len(ctx.names)
        ctx.push(name.copy(), ty, V_OWNED)
        out.append(self.add_stmt(Stmt(S_VAR, -1, init, -1, 0, [], [], name^)))
        return v

    def near_call_stmts(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> List[Int]:
        """For a disjoint, read_alias or move_copy near miss, perhaps a
        statement `_ = call` built for it, after `var v = ...` if no
        variable fits. The calls, variables and types such a near miss
        needs meet too seldom to wait for them:
        - disjoint: `g(..., v.f, ..., v.g, ...)`, with a `mut` parameter
          and another one, `mut` or read, given two fields of v (g may
          be generic, or a method with `v.f` its `mut self` receiver);
        - read_alias: `g(..., x, ..., x or x.f, ...)` for two read
          parameters, neither an Int (an Int is passed by value);
        - move_copy: `g(..., x^, ..., e, ...)` with e a value made from x
          (`x.copy()`, `x.f.copy()`, or an Int field `x.f`) for a later
          parameter that isn't `mut`.
        The other arguments don't use v (or x). None if there is no such
        call or the chance isn't taken."""
        var out = List[Int]()
        var cs = self.near_callees(
            ctx, self.near == NR_MOVE_COPY, self.near == NR_DISJOINT
        )
        # candidates: callee, i, j, and (type, field a, field b) packed
        var c_k = List[Int]()
        var c_ij = List[Int]()
        var c_t = List[Int]()
        for k in range(len(cs)):
            ref ps = cs[k].params
            ref cv = cs[k].convs
            for i in range(len(ps)):
                for j in range(len(ps)):
                    if i == j:
                        continue
                    if self.near == NR_DISJOINT:
                        if cv[i] != CONV_MUT or cv[j] == CONV_VAR:
                            continue
                        if (
                            cs[k].kind == C_METHOD
                            and cv[0] == CONV_MUT
                            and i != 0
                            and j != 0
                        ):
                            continue  # (a `mut self` receiver is one of them)
                        for t in ctx.pool.copy():
                            if self.tkind[t] != STRUCT:
                                continue
                            var fs = self.fields_of(t)
                            for a in range(len(fs)):
                                for b in range(len(fs)):
                                    if (
                                        a != b
                                        and fs[a] == ps[i]
                                        and fs[b] == ps[j]
                                    ):
                                        c_k.append(k)
                                        c_ij.append(i * 64 + j)
                                        c_t.append(t * 4096 + a * 64 + b)
                    elif self.near == NR_READ_ALIAS:
                        if (
                            cv[i] != CONV_READ
                            or cv[j] != CONV_READ
                            or ps[i] == self.int_ty
                            or ps[j] == self.int_ty
                            or not has(ctx.pool, ps[i])
                        ):
                            continue
                        if ps[j] == ps[i]:
                            c_k.append(k)
                            c_ij.append(i * 64 + j)
                            c_t.append(ps[i] * 4096 + 63)
                        var fs = self.fields_of(ps[i])
                        for f in range(len(fs)):
                            if fs[f] == ps[j]:
                                c_k.append(k)
                                c_ij.append(i * 64 + j)
                                c_t.append(ps[i] * 4096 + f)
                    else:  # NR_MOVE_COPY
                        if (
                            j < i
                            or cv[i] != CONV_VAR
                            or cv[j] == CONV_MUT
                            or ps[i] == self.int_ty
                            or not has(ctx.pool, ps[i])
                        ):
                            continue
                        var copyable = (
                            ps[j] == self.int_ty
                            or self.cap_of(ps[j], ctx.bounds) >= CAP_C
                        )
                        if not copyable:
                            continue
                        if ps[j] == ps[i]:
                            c_k.append(k)
                            c_ij.append(i * 64 + j)
                            c_t.append(ps[i] * 4096 + 63)
                        var fs = self.fields_of(ps[i])
                        for f in range(len(fs)):
                            if fs[f] == ps[j]:
                                c_k.append(k)
                                c_ij.append(i * 64 + j)
                                c_t.append(ps[i] * 4096 + f)
        if len(c_k) == 0 or not self.near_chance(data, self.near):
            return out^
        var n = pick(data, len(c_k))
        ref c = cs[c_k[n]]
        var i = c_ij[n] // 64
        var j = c_ij[n] % 64
        var t = c_t[n] // 4096
        var fa = (c_t[n] // 64) % 64
        var fb = c_t[n] % 64
        var saved = ctx.copy()
        var state = self.mutation_state()
        var n_out = 0
        try:
            var fixed = List[Int]()
            var v: Int
            if self.near == NR_DISJOINT:
                v = self.near_var(data, ctx, t, [V_OWNED, V_MUT], out)
                n_out = len(out)
                saved = ctx.copy()  # (the new local stays if the call is stuck)
                state = self.mutation_state()
                ctx.new_statement()
                ctx.taken = [v * 64 + fa + 1, v * 64 + fb + 1]
                fixed.append(self.place_expr(ctx, v, fa))
                fixed.append(self.mark_near(self.place_expr(ctx, v, fb)))
            elif self.near == NR_READ_ALIAS:
                v = self.near_var(data, ctx, t, [V_OWNED, V_MUT, V_READ], out)
                n_out = len(out)
                saved = ctx.copy()  # (the new local stays if the call is stuck)
                state = self.mutation_state()
                ctx.new_statement()
                fixed.append(self.place_expr(ctx, v, -1))
                var f = -1 if fb == 63 else fb
                fixed.append(self.mark_near(self.place_expr(ctx, v, f)))
            else:
                v = self.near_var(data, ctx, t, [V_OWNED], out)
                n_out = len(out)
                saved = ctx.copy()  # (the new local stays if the call is stuck)
                state = self.mutation_state()
                ctx.new_statement()
                var text = String(ctx.names[v], "^")
                fixed.append(self.add(E_MOVE, v, t, [], [], text^))
                var f = -1 if fb == 63 else fb
                var e = self.place_expr(ctx, v, f)
                if c.params[j] != self.int_ty:
                    var ctext = String(self.exprs[e].text, ".copy()")
                    e = self.add(E_COPY, 0, c.params[j], [e], [], ctext^)
                fixed.append(self.mark_near(e))
            # nothing else in the call may use v
            ctx.excl[v] = True
            ctx.touched[v] = True
            var call = self.call_with(data, ctx, c, [i, j], fixed)
            if self.near == NR_MOVE_COPY:
                ctx.live[v] = False
                ctx.move_depth[v] = ctx.depth
            out.append(
                self.add_stmt(Stmt(S_EXPR, -1, call, -1, 0, [], [], String()))
            )
            return out^
        except err:
            if String(err) != "STUCK":
                raise err^
            # drop the call (a new local stays)
            ctx = saved^
            self.restore_mutation(state)
            while len(out) > n_out:
                _ = out.pop()
            return out^

    def reinit_stmts(
        mut self, mut data: ConjectureData, mut ctx: Ctx, v: Int, b: Int
    ) raises -> List[Int]:
        """For a reinit near miss: `v = e` for the moved variable v, then a
        use of it, or (ref_reinit) of binding b to it."""
        ctx.new_statement()
        var st = self.gen_reinit(data, ctx, v)
        _ = self.mark_near(self.stmts[st].target)
        var use: Int
        if b >= 0:
            use = self.place_expr(ctx, v, ctx.ref_field[b])
            self.exprs[use].text = String(MARK_NEAR, ctx.ref_names[b])
            self.exprs[use].tys = [1]
        else:
            use = self.place_expr(ctx, v, -1)
        return [st, self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))]

    def returning_end(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> List[Int]:
        """The end of a block with an early return: `p = e` for each `mut`
        argument still moved (a ret_uninit mutant leaves one moved, moving
        it here if it's live, and marks the `return`), then `return e`.
        A mut_uninit mutant's argument, if it's still moved here, stays
        moved and the `return` is marked: Mojo reports it there (and a
        block that returns leaves it as it was before the block, perhaps
        live, so the body's marked return can be valid)."""
        var out = List[Int]()
        var left = -1
        if self.keep_dead >= 0 and not ctx.live[self.keep_dead]:
            left = self.keep_dead
        elif self.wants(MU_RET_UNINIT) and not self.in_const_if(ctx):
            var cands = List[Int]()
            for v in range(len(ctx.names)):
                if (
                    ctx.kinds[v] == V_MUT
                    and ctx.types[v] != self.int_ty
                    and not self.is_deinit_self(v)
                ):
                    cands.append(v)
            if len(cands) > 0 and self.chance(data, MU_RET_UNINIT):
                self.mutated = True
                left = cands[pick(data, len(cands))]
                if ctx.live[left]:
                    out.append(self.move_stmt(ctx, left))
        for v in range(len(ctx.names)):
            if ctx.kinds[v] == V_MUT and not ctx.live[v] and v != left:
                out.append(self.gen_reinit(data, ctx, v))
        ctx.new_statement()
        var e = self.gen_typed(data, ctx, ctx.ret, BODY_SIZE - 1, P_OWNED, True)
        if left >= 0:
            e = self.mark(e)
        # (op 1: `_died()` first)
        out.append(
            self.add_stmt(Stmt(S_RETURN, -1, e, -1, Int(self.died), [], [], ""))
        )
        return out^

    def loop_exit_end(
        mut self, mut data: ConjectureData, mut ctx: Ctx, exit: Int
    ) raises -> List[Int]:
        """The end of a block in a loop that ends with `break` or
        `continue`: `v = e` for each variable from outside the loop live at
        the start of its body and moved since, then the statement. Before a
        `break`, a break_moved mutant or loop_exit near miss moves one
        (`ctx.break_var`), left moved; before a `continue`, a loop_exit near
        miss moves one, reinitialized with the others."""
        var out = List[Int]()
        var bv = -1
        var mutant = (
            exit == S_BREAK
            and self.wants(MU_BREAK_MOVED)
            and not self.in_const_if(ctx)
        )
        if mutant or self.wants_near(NR_LOOP_EXIT):
            # (a mutant's variable isn't used again by an enclosing loop:
            # its next iteration's error could come first)
            var lo = ctx.parent_base if mutant else 0
            var cands = List[Int]()
            for v in self.owned_vars(ctx, ctx.loop_base):
                if v >= lo and ctx.loop_live[v]:
                    cands.append(v)
            var take = len(cands) > 0 and (
                self.chance(
                    data, MU_BREAK_MOVED
                ) if mutant else self.near_chance(data, NR_LOOP_EXIT)
            )
            if take:
                var v = cands[pick(data, len(cands))]
                var st = self.move_stmt(ctx, v)
                if mutant:
                    self.mutated = True
                else:
                    _ = self.mark_near(self.stmts[st].e)
                out.append(st)
                if exit == S_BREAK:
                    bv = v
                    ctx.break_var = v
        # (no moves in the reinitializations: one could move a variable
        # already passed over, which the loop or the code after it uses)
        ctx.no_move += 1
        for v in range(ctx.loop_base):
            if ctx.loop_live[v] and not ctx.live[v] and v != bv:
                out.append(self.gen_reinit(data, ctx, v))
        ctx.no_move -= 1
        out.append(self.add_stmt(Stmt(exit, -1, -1, -1, 0, [], [], "")))
        return out^

    def wants_loop_exit(self, ctx: Ctx) -> Bool:
        """Whether a break_moved mutant or loop_exit near miss can still be
        made here."""
        return (
            self.wants(MU_BREAK_MOVED) and not self.in_const_if(ctx)
        ) or self.wants_near(NR_LOOP_EXIT)

    def exit_if(
        mut self, mut data: ConjectureData, mut ctx: Ctx, kind: Int
    ) raises -> List[Int]:
        """A chance for break_moved and loop_exit (kind -1: in a loop's
        body, `if i == k:` on the loop variable i, ending with `break` or
        `continue` after a move, `loop_exit_end`), or for ret_uninit (kind
        S_RETURN: an `if` on a condition that isn't constant, ending with
        an early return, `returning_end`). Nothing if the chance isn't
        taken."""
        var state = self.mutation_state()
        ctx.new_statement()
        var exit = kind
        var x: Int
        var y: Int
        if exit < 0:
            exit = S_BREAK
            if not self.wants(MU_BREAK_MOVED) and data.draw(booleans()):
                exit = S_CONTINUE
            var lv = ctx.loop_base  # (the loop variable)
            x = self.add(E_VAR, lv, self.int_ty, [], [], ctx.names[lv])
            var k = data.draw(integers(0, 2))
            y = self.add(E_LIT, k, self.int_ty, [], [], String(k))
        else:
            x = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            y = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            if self.is_const(x) and self.is_const(y):
                return []
        var op = pick(data, comptime (len(CMP_OPS)))
        var n = len(ctx.names)
        var live = ctx.live.copy()
        var depths = ctx.move_depth.copy()
        ctx.depth += 1
        var then: List[Int]
        if exit == S_RETURN:
            then = self.returning_end(data, ctx)
        else:
            then = self.loop_exit_end(data, ctx, exit)
        ctx.depth -= 1
        ctx.truncate(n)
        ctx.live = live^
        ctx.move_depth = depths^
        if self.mutation_state() == state:
            return []
        return [self.add_stmt(Stmt(S_IF, -1, x, y, op, then^, [], String()))]

    def wants_partial(self, ctx: Ctx) -> Bool:
        """Whether a partial kind can still be made here (a mutant not in
        a constant `if`)."""
        return (
            self.wants(MU_PARTIAL_USE) and not self.in_const_if(ctx)
        ) or self.wants_near(NR_PARTIAL_MOVE)

    def partial_stmts(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> List[Int]:
        """A chance for the partial kinds: `var vN = x.f^` for a live owned
        or `mut` x and a field f that isn't an Int (a mutant's x is
        declared in the innermost loop body, if any), then:
        - partial_use: `_use(x)` or `_use(x.f)`, both lines marked;
        - partial_move: up to two statements that don't use x (and don't
          exit), `x.f = e` (or an `if` that does it in both branches),
          and a use of x."""
        var mutant = self.mutant == MU_PARTIAL_USE
        var cands = List[Int]()  # v * 64 + f
        for v in range(len(ctx.names)):
            var k = ctx.kinds[v]
            if not ctx.live[v] or (k != V_OWNED and k != V_MUT):
                continue
            if mutant and v < ctx.loop_base:
                continue
            var fs = self.fields_of(ctx.types[v])
            for f in range(len(fs)):
                if fs[f] != self.int_ty:
                    cands.append(v * 64 + f)
        if len(cands) == 0:
            return []
        if mutant:
            if not self.chance(data, self.mutant):
                return []
            self.mutated = True
        elif not self.near_chance(data, NR_PARTIAL_MOVE):
            return []
        var c = cands[pick(data, len(cands))]
        var v = c // 64
        var f = c % 64
        var fty = self.fields_of(ctx.types[v])[f]
        ctx.new_statement()
        var place = self.place_expr(ctx, v, f)
        var text = String(self.exprs[place].text, "^")
        var mv = self.add(E_FMOVE, 0, fty, [place], [], text^)
        if mutant:
            mv = self.mark(mv)
        else:
            mv = self.mark_near(mv)
        var name = String("v", ctx.counter)
        ctx.counter += 1
        ctx.push(name.copy(), fty, V_OWNED)
        var out: List[Int] = [
            self.add_stmt(Stmt(S_VAR, -1, mv, -1, 0, [], [], name^))
        ]
        ctx.live[v] = False  # (nothing uses or assigns x meanwhile)
        ctx.move_depth[v] = -2
        if self.mutant == MU_PARTIAL_USE:
            ctx.new_statement()
            var use = self.mark(
                self.place_expr(ctx, v, f if data.draw(booleans()) else -1)
            )
            out.append(self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], "")))
            return out^
        ctx.no_exit += 1
        var exit_catch = ctx.exit_catch
        ctx.exit_catch = ctx.catching
        var region_loops = ctx.region_loops
        if getenv("DECL_FUZZ_NO_PARTIAL_LOOP_WORKAROUND") == "":
            # Mojo rejects the move ("cannot be consumed, because 'x' is
            # used later") when a loop nested in another loop comes before
            # the reassignment (modular/modular#7787): no nested loops here
            ctx.region_loops = ctx.in_loop
        for _ in range(data.draw(integers(0, 2))):
            out.append(self.gen_stmt(data, ctx))
        ctx.region_loops = region_loops
        ctx.new_statement()
        # (the reassignment's value is still in the region: a raise there
        # would leave the variable partly moved)
        if data.draw(integers(0, 2)) == 0:
            var op = pick(data, comptime (len(CMP_OPS)))
            var x = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            var y = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            var branches = List[Int]()
            for _ in range(2):
                ctx.new_statement()
                var e = self.gen_typed(data, ctx, fty, BODY_SIZE - 2, P_OWNED)
                var target = self.place_expr(ctx, v, f)
                branches.append(
                    self.add_stmt(Stmt(S_ASSIGN, target, e, -1, 0, [], [], ""))
                )
            out.append(
                self.add_stmt(
                    Stmt(S_IF, -1, x, y, op, [branches[0]], [branches[1]], "")
                )
            )
        else:
            var e = self.gen_typed(data, ctx, fty, BODY_SIZE - 2, P_OWNED)
            var target = self.place_expr(ctx, v, f)
            out.append(
                self.add_stmt(Stmt(S_ASSIGN, target, e, -1, 0, [], [], ""))
            )
        ctx.no_exit -= 1
        ctx.exit_catch = exit_catch
        ctx.live[v] = True
        ctx.move_depth[v] = -1
        ctx.new_statement()
        var use = self.place_expr(ctx, v, -1)
        out.append(self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], "")))
        return out^

    def loop_move_stmt(
        mut self, mut data: ConjectureData, mut ctx: Ctx, v: Int
    ) raises -> Int:
        """For a loop_move mutant in a loop's body: `var vN = v^`, or
        `if i == k: var vN = v^` (perhaps then `continue`) on the loop
        variable i. Either way, v stays moved."""
        if data.draw(booleans()):
            return self.move_stmt(ctx, v)
        ctx.new_statement()
        var lv = ctx.loop_base  # (the loop variable)
        var x = self.add(E_VAR, lv, self.int_ty, [], [], ctx.names[lv])
        var k = data.draw(integers(0, 2))
        var y = self.add(E_LIT, k, self.int_ty, [], [], String(k))
        var op = pick(data, comptime (len(CMP_OPS)))
        var n = len(ctx.names)
        ctx.depth += 1
        var then: List[Int] = [self.move_stmt(ctx, v)]
        if data.draw(booleans()):
            then.append(
                self.add_stmt(Stmt(S_CONTINUE, -1, -1, -1, 0, [], [], ""))
            )
        ctx.depth -= 1
        ctx.truncate(n)
        return self.add_stmt(Stmt(S_IF, -1, x, y, op, then^, [], String()))

    def draw_exit(
        mut self,
        mut data: ConjectureData,
        ctx: Ctx,
        const_cond: Bool,
        mode: Int,
        br: Int,
    ) raises -> List[Int]:
        """Which branch of the `if` being drawn (BR_THEN or BR_ELSE) ends
        with an exit, and which (S_RETURN, or in a loop S_BREAK or
        S_CONTINUE); empty for none. Not in an `if` with a constant
        condition (Mojo would drop the code after it, and so its errors).
        With a plan (mode, br), a mutant's continuing branch is one that
        leaves the variable moved; an early_return near miss's returning
        branch is."""
        if ctx.ret < 0 or const_cond or ctx.no_exit > 0:
            return []
        var mutant_plan = mode >= 0 and (
            self.mutant == MU_MAYBE_MOVED
            or self.mutant == MU_MUT_UNINIT
            or self.mutant == MU_UNINIT
        )
        if mode >= 0 and self.near == NR_EARLY_RETURN:
            return [br if mode == PLAN_MOVE else 1 - br, S_RETURN]
        var loop_kind = ctx.in_loop > 0 and (
            self.wants(MU_BREAK_MOVED) or self.wants_near(NR_LOOP_EXIT)
        )
        var often = (
            self.wants(MU_RET_UNINIT)
            or self.wants_near(NR_EARLY_RETURN)
            or loop_kind
        )
        if data.draw(integers(0, 1 if often else 5)) != 0:
            return []
        var r = pick(data, 2)
        if mutant_plan and br != BR_BOTH:
            r = 1 - br if mode == PLAN_MOVE else br
        var exit = S_RETURN
        if ctx.in_loop > 0:
            if self.wants(MU_BREAK_MOVED):
                exit = S_BREAK
            elif self.wants_near(NR_LOOP_EXIT):
                exit = S_BREAK if data.draw(booleans()) else S_CONTINUE
            elif not self.wants(MU_RET_UNINIT):
                exit = [S_RETURN, S_BREAK, S_CONTINUE][pick(data, 3)]
        return [r, exit]

    def plan_step(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        keep_moved: Int,
        reinit_in: Int,
    ) raises -> List[Int]:
        """In a branch with a plan: moves keep_moved if it's live (leaving
        it unassignable in the block), or reinitializes reinit_in if it's
        moved."""
        var out = List[Int]()
        if keep_moved >= 0 and ctx.live[keep_moved]:
            out.append(self.move_stmt(ctx, keep_moved))
        if reinit_in >= 0 and not ctx.live[reinit_in]:
            if (
                self.mutant == MU_UNINIT or self.near == NR_DEFERRED
            ) and data.draw(integers(0, 2)) == 0:
                out.append(self.nested_reinit(data, ctx, reinit_in))
            else:
                out.append(self.gen_reinit(data, ctx, reinit_in))
        return out^

    def wants_path(self) -> Bool:
        """Whether a path kind (a mutant or near miss made by an `if`'s
        plan) is still to be made."""
        return (
            self.wants(MU_MAYBE_MOVED)
            or self.wants(MU_MUT_UNINIT)
            or self.wants_near(NR_MAYBE_MOVED)
            or self.wants_near(NR_REINIT_PATHS)
            or self.wants_near(NR_MUT_REINIT)
            or self.wants_deferred()
            or self.wants_near(NR_EARLY_RETURN)
        )

    def wants_deferred(self) -> Bool:
        """Whether a deferred kind (uninit, deferred) is still to be
        made."""
        return self.wants(MU_UNINIT) or self.wants_near(NR_DEFERRED)

    def deferred_chance(
        mut self, mut data: ConjectureData, ctx: Ctx
    ) raises -> Bool:
        """Whether to make the deferred kind here (an uninit mutant is
        made, and so counts as made, only outside constant `if`s)."""
        if self.wants(MU_UNINIT):
            if self.in_const_if(ctx) or not self.chance(data, MU_UNINIT):
                return False
            self.mutated = True
            return True
        return self.near_chance(data, NR_DEFERRED)

    def decl_stmt(
        mut self, mut data: ConjectureData, mut ctx: Ctx, near: Bool
    ) raises -> Int:
        """`var vN: T`, a variable declared without a value: moved, and
        assignable in this block. With near, marked as the near miss."""
        var ty = self.draw_type(data, ctx.pool)
        var name = String("v", ctx.counter)
        ctx.counter += 1
        var text = String(
            MARK_NEAR if near else "", name, ": ", self.cty(ty, ctx)
        )
        if near:
            self.near_made = True
        ctx.push(name^, ty, V_OWNED)
        var v = len(ctx.names) - 1
        ctx.live[v] = False
        ctx.move_depth[v] = ctx.depth
        return self.add_stmt(Stmt(S_VAR, -1, -1, -1, 0, [], [], text^))

    def nested_reinit(
        mut self, mut data: ConjectureData, mut ctx: Ctx, v: Int
    ) raises -> Int:
        """`if c: v = e1 else: v = e2`, for the moved variable v."""
        ctx.new_statement()
        var op = pick(data, comptime (len(CMP_OPS)))
        var x = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
        var y = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
        ctx.depth += 1
        var a = self.gen_reinit(data, ctx, v)
        ctx.live[v] = False
        var b = self.gen_reinit(data, ctx, v)
        ctx.depth -= 1
        return self.add_stmt(Stmt(S_IF, -1, x, y, op, [a], [b], String()))

    def setup_movable(self, ctx: Ctx) -> List[Int]:
        """The variables the path kinds may move ahead of an `if` that
        reinitializes them (or of the body's end): live owned ones for
        maybe_moved and reinit_paths, live `mut` ones for mut_uninit and
        mut_reinit, none for other kinds. Not Ints (`^` on an Int has no
        effect)."""
        var owned = (
            self.wants(MU_MAYBE_MOVED)
            or self.wants_near(NR_REINIT_PATHS)
            or self.wants_near(NR_EARLY_RETURN)
        )
        var muts = (
            self.wants(MU_MUT_UNINIT)
            or self.wants_near(NR_MUT_REINIT)
            or self.wants(MU_RET_UNINIT)
            or self.wants_near(NR_EARLY_RETURN)
        )
        var out = List[Int]()
        if not owned and not muts:
            return out^
        for v in range(len(ctx.names)):
            if not ctx.live[v] or ctx.types[v] == self.int_ty:
                continue
            var k = ctx.kinds[v]
            if (owned and k == V_OWNED) or (muts and k == V_MUT):
                out.append(v)
        return out^

    def draw_plan(
        mut self, mut data: ConjectureData, ctx: Ctx, x: Int, y: Int
    ) raises -> List[Int]:
        """For a path kind, perhaps a plan for the `if` being drawn, with
        condition operands x and y: [variable, PLAN_*, BR_*, PRE_*], and
        the mutant or near miss counts as made; empty if there is none or
        the chance isn't taken. With PRE_MOVE, a live variable that the
        condition doesn't use is moved just before the `if`, for its
        branches to reinitialize; with PRE_DECL (the deferred kinds), the
        variable (-1 here) is a new one declared without a value. A
        mutant's `if` isn't in a loop that uses the variable again (the
        next iteration's error could come first), and neither it nor an
        `if` around it has a constant condition (Mojo drops the dead
        branch first)."""
        var mutant = (
            self.wants(MU_MAYBE_MOVED)
            or self.wants(MU_MUT_UNINIT)
            or self.wants(MU_UNINIT)
        )
        if not mutant and not self.wants_path():
            return []
        var const_cond = self.is_const(x) and self.is_const(y)
        if mutant and (const_cond or self.in_const_if(ctx)):
            return []
        if self.wants_near(NR_EARLY_RETURN) and (ctx.ret < 0 or const_cond):
            return []
        if self.wants_deferred():
            if not self.deferred_chance(data, ctx):
                return []
            # (a mutant assigns in one branch: both would be valid)
            return [-1, PLAN_REINIT, pick(data, 2 if mutant else 3), PRE_DECL]
        var cands = List[Int]()  # v * 4 + PLAN_* + 2 * premove
        for v in range(len(ctx.names)):
            if ctx.types[v] == self.int_ty or v == self.keep_dead:
                continue
            if mutant and (v < ctx.loop_base or self.is_deinit_self(v)):
                continue
            var k = ctx.kinds[v]
            var kind_ok: Bool
            if self.mutant == MU_MAYBE_MOVED or self.near == NR_REINIT_PATHS:
                kind_ok = k == V_OWNED
            elif self.near == NR_MAYBE_MOVED or self.near == NR_EARLY_RETURN:
                kind_ok = k == V_OWNED or k == V_MUT
            else:  # mut_uninit, mut_reinit
                kind_ok = k == V_MUT
            if not kind_ok:
                continue
            if ctx.live[v]:
                if self.near != NR_REINIT_PATHS:
                    cands.append(v * 4 + PLAN_MOVE)
                if (
                    self.near != NR_MAYBE_MOVED
                    and not self.uses_var(x, v)
                    and not self.uses_var(y, v)
                ):
                    cands.append(v * 4 + PLAN_REINIT + 2)
            elif ctx.move_depth[v] == ctx.depth:  # (moved in this block)
                if self.near != NR_MAYBE_MOVED:
                    cands.append(v * 4 + PLAN_REINIT)
        if len(cands) == 0:
            return []
        if mutant:
            if not self.chance(data, self.mutant):
                return []
            self.mutated = True
        elif not self.near_chance(data, self.near):
            return []
        var c = cands[pick(data, len(cands))]
        var mode = c % 2
        # (a mutant reinitializes in one branch: both would be valid; an
        # early_return near miss acts in the branch that returns, or in
        # the other)
        var one = (mode == PLAN_REINIT and mutant) or (
            self.near == NR_EARLY_RETURN
        )
        var br = pick(data, 2 if one else 3)
        return [c // 4, mode, br, (c // 2) % 2]

    def finish_plan(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        pre: Int,
        st: Int,
        v: Int,
        mode: Int,
        all_init: Bool,
    ) raises -> Int:
        """After the `if` st with a plan for v (and the move pre before it,
        or -1), where all_init says whether both branches left v live (a
        plan to reinitialize may be undone: a block's last statements,
        reinitializing others, can move v again): v's state, and what
        follows the `if` (in an S_USE group with them):
        - maybe_moved, uninit mutants: a use of v (marked);
        - mut_uninit mutant: nothing, and v stays moved to the return;
        - maybe_moved near miss: perhaps `v = e` and a use;
        - deferred near miss: as reinit_paths, but perhaps neither when
          a branch left v unassigned;
        - reinit_paths, mut_reinit: `v = e` unless both branches
          reinitialized v, then a use."""
        ctx.live[v] = all_init
        ctx.move_depth[v] = -1 if all_init else ctx.depth
        var group = List[Int]()
        if pre >= 0:
            group.append(pre)
        group.append(st)
        if self.mutant == MU_MUT_UNINIT:
            ctx.move_depth[v] = -2
            self.keep_dead = v
            if pre < 0:
                return st
            return self.add_stmt(
                Stmt(S_USE, -1, -1, -1, 0, group^, [], String())
            )
        if self.mutant == MU_MAYBE_MOVED or self.mutant == MU_UNINIT:
            ctx.move_depth[v] = -2
            ctx.new_statement()
            var use = self.mark(self.place_expr(ctx, v, -1))
            group.append(self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], "")))
        else:
            var reinit = not all_init
            if self.near == NR_MAYBE_MOVED:
                reinit = data.draw(booleans())
            elif self.near == NR_MUT_REINIT and mode == PLAN_MOVE:
                reinit = False  # (later, or at the body's end)
            elif self.near == NR_DEFERRED and reinit:
                reinit = data.draw(booleans())
            if reinit:
                group.append(self.gen_reinit(data, ctx, v))
            if ctx.live[v]:
                var use = self.place_expr(ctx, v, -1)
                group.append(
                    self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                )
        if len(group) == 1:
            return st
        return self.add_stmt(Stmt(S_USE, -1, -1, -1, 0, group^, [], String()))

    def owned_vars(self, ctx: Ctx, n: Int) -> List[Int]:
        """The live owned variables among the first n, except Ints (`^` on
        an Int has no effect)."""
        var out = List[Int]()
        for v in range(n):
            if (
                ctx.kinds[v] == V_OWNED
                and ctx.live[v]
                and ctx.types[v] != self.int_ty
                and not self.tuple_bound(ctx, v)
            ):
                out.append(v)
        return out^

    def tuple_bound(self, ctx: Ctx, v: Int) -> Bool:
        """Whether v was bound out of a temporary tuple by a pattern (and
        the workaround applies): see Ctx.from_tuple."""
        return (
            ctx.from_tuple[v]
            and getenv("DECL_FUZZ_NO_TUPLE_VAR_WORKAROUND") == ""
        )

    def loop_movable(
        self, ctx: Ctx, n_outer: Int, body: List[Int]
    ) -> List[Int]:
        """The outer variables a loop_move mutant can move after the
        statements `body` of a loop body: not ones these assign (that
        would reinitialize them on every iteration)."""
        var out = List[Int]()
        for v in self.owned_vars(ctx, n_outer):
            if not self.assigns(body, v):
                out.append(v)
        return out^

    def assigns(self, stmts: List[Int], v: Int) -> Bool:
        """Whether some statement in stmts, or nested in one, assigns the
        whole variable v."""
        for i in stmts:
            ref st = self.stmts[i]
            if st.kind == S_ASSIGN:
                ref t = self.exprs[st.target]
                if t.kind == E_VAR and t.a == v:
                    return True
            if self.assigns(st.body, v) or self.assigns(st.orelse, v):
                return True
        return False

    def move_stmt(mut self, mut ctx: Ctx, v: Int) -> Int:
        """`var vN = v^`, leaving v moved and not assignable, so that it
        stays moved until the end of the block."""
        ctx.new_statement()
        var ty = ctx.types[v]
        var e = self.add(E_MOVE, v, ty, [], [], String(ctx.names[v], "^"))
        var name = String("v", ctx.counter)
        ctx.counter += 1
        ctx.push(name.copy(), ty, V_OWNED)
        ctx.live[v] = False
        ctx.move_depth[v] = -2
        return self.add_stmt(Stmt(S_VAR, -1, e, -1, 0, [], [], name^))

    def place_expr(mut self, ctx: Ctx, v: Int, f: Int) -> Int:
        """The place `v` or `v.f<f>`."""
        var var_e = self.add(E_VAR, v, ctx.types[v], [], [], ctx.names[v])
        if f < 0:
            return var_e
        var fty = self.fields_of(ctx.types[v])[f]
        var text = String(ctx.names[v], ".", self.field_name(ctx.types[v], f))
        return self.add(E_FIELD, f, fty, [var_e], [], text^)

    def ref_stmt(
        mut self, mut data: ConjectureData, mut ctx: Ctx, v: Int, f: Int
    ) raises -> Int:
        """`ref rN = <the place v or v.f<f>>`, in scope until the end of the
        block."""
        ctx.new_statement()
        var e = self.spell(data, ctx, v, f, True)
        var name = String("r", ctx.counter)
        ctx.counter += 1
        ctx.ref_names.append(name.copy())
        ctx.ref_var.append(v)
        ctx.ref_field.append(f)
        ctx.ref_depth.append(ctx.depth)
        ctx.ref_ro.append(False)
        return self.add_stmt(Stmt(S_REF, -1, e, -1, 0, [], [], name^))

    def ref_places(mut self, ctx: Ctx) -> List[Int]:
        """The places of live variables (v * 64 + f + 1) that can be bound:
        not a read Int (an argument or loop variable), which is passed by
        value and has no memory origin."""
        var out = List[Int]()
        for v in range(len(ctx.names)):
            if not ctx.live[v] or self.tkind[ctx.types[v]] == ERR:
                continue
            if (
                ctx.from_tuple[v]
                and getenv("DECL_FUZZ_NO_TUPLE_VAR_WORKAROUND") == ""
            ):
                continue
            if ctx.kinds[v] != V_READ or ctx.types[v] != self.int_ty:
                out.append(v * 64)
            for f in range(len(self.fields_of(ctx.types[v]))):
                out.append(v * 64 + f + 1)
        return out^

    def has_accessor(self, ty: Int, f: Int) -> Bool:
        return (
            f >= 0
            and self.tkind[ty] == STRUCT
            and self.structs[self.tid[ty]].refs[f]
        )

    def spell(
        mut self,
        mut data: ConjectureData,
        ctx: Ctx,
        v: Int,
        f: Int,
        write: Bool = False,
    ) raises -> Int:
        """The place `v` or `v.f<f>` (as place_expr), perhaps spelled
        through a `ref`: an accessor `v.f<f>_ref()`, a binding to the place,
        or a binding to v then `.f<f>` (or the accessor). Only for a live v
        (but for a use_moved mutant), and not for a move: a `ref` names
        the place, which Mojo checks like the variable itself. To write
        to the place (or bind it), not through a pattern's binding, which
        is read-only."""
        var e = self.place_expr(ctx, v, f)
        var texts: List[String] = [self.exprs[e].text]
        var vty = ctx.types[v]
        var acc = self.has_accessor(vty, f)
        if acc:
            texts.append(String(ctx.names[v], ".f", f, "_ref()"))
        for b in range(len(ctx.ref_names)):
            if ctx.ref_var[b] != v or (write and ctx.ref_ro[b]):
                continue
            if ctx.ref_field[b] == f:
                texts.append(ctx.ref_names[b])
            elif ctx.ref_field[b] < 0:
                texts.append(
                    String(ctx.ref_names[b], ".", self.field_name(vty, f))
                )
                if acc:
                    texts.append(String(ctx.ref_names[b], ".f", f, "_ref()"))
        if len(texts) == 1:
            return e
        var i = pick(data, len(texts))
        if i > 0:
            self.exprs[e].text = texts[i]
            self.exprs[e].tys = [1]  # (for STAT_REF)
        return e

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
            for v in range(ctx.freeze_base, len(ctx.names)):
                # (not a handler's binding, which a typed handler owns)
                if (
                    ctx.kinds[v] == V_READ
                    and ctx.live[v]
                    and self.tkind[ctx.types[v]] != ERR
                ):
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
                var target = self.mark(self.spell(data, ctx, v, f))
                return self.add_stmt(
                    Stmt(S_ASSIGN, target, e, -1, 0, [], [], String())
                )
        if self.wants(MU_REF_RVALUE):
            # (type * 64 + field) with an accessor
            var cands = List[Int]()
            for t in ctx.pool:
                var fs = self.fields_of(t)
                for f in range(len(fs)):
                    if self.has_accessor(t, f):
                        cands.append(t * 64 + f)
            if len(cands) > 0 and self.chance(data, MU_REF_RVALUE):
                var c = cands[pick(data, len(cands))]
                var t = c // 64
                var f = c % 64
                var recv = self.gen(data, ctx, t, BODY_SIZE - 2, P_OWNED)
                if self.is_place(recv):  # (an ImplicitlyCopyable value)
                    var text = String(self.exprs[recv].text, ".copy()")
                    recv = self.add(E_COPY, 0, t, [recv], [], text^)
                var fty = self.fields_of(t)[f]
                var text = String(self.exprs[recv].text, ".f", f, "_ref()")
                var target = self.mark(
                    self.add(E_FIELD, f, fty, [recv], [], text^)
                )
                var e = self.gen_typed(data, ctx, fty, BODY_SIZE - 2, P_OWNED)
                return self.add_stmt(
                    Stmt(S_ASSIGN, target, e, -1, 0, [], [], String())
                )
        var mut_types = self.mut_call_types(ctx)
        var kinds: List[Int] = [S_VAR, S_EXPR]
        if self.can_try(ctx):
            kinds += [S_TRY, S_TRY]
            if self.try_kind():
                kinds += [S_TRY, S_TRY, S_TRY, S_TRY]
        if (
            ctx.depth < MAX_DEPTH
            and ctx.no_exit == 0
            and getenv("DECL_FUZZ_NO_PATTERNS") == ""
        ):
            kinds += [S_MATCH, S_MATCH]
            if self.mutant >= MU_PAT_FIELD and self.mutant <= MU_PAT_VAR:
                kinds += [S_MATCH, S_MATCH, S_MATCH, S_MATCH]
        if (
            self.cif_fn >= 0
            and ctx.depth < MAX_DEPTH
            and not (
                # (a reference in its branches is "use of uninitialized
                # value", modular/modular#7818)
                ctx.in_finally > 0
                and getenv("DECL_FUZZ_NO_NESTED_FINALLY_WORKAROUND") == ""
            )
        ):
            kinds.append(S_CIF)
            if self.mutant == MU_VWHERE or self.near == NR_VWHERE:
                kinds += [S_CIF, S_CIF]
        if len(mut_types) > 0:
            kinds += [S_EXPR, S_EXPR]
        if len(t_var) > 0:
            kinds += [S_ASSIGN, S_ASSIGN]
        if ctx.depth < MAX_DEPTH:
            kinds += [S_IF, S_FOR]
            if self.wants_path():
                kinds += [S_IF, S_IF, S_IF]  # an `if` that can get a plan
            if (
                self.wants(MU_LOOP_MOVE)
                and not self.in_const_if(ctx)
                and len(self.owned_vars(ctx, len(ctx.names))) > 0
            ):
                kinds += [S_FOR, S_FOR, S_FOR]  # a loop that can move one
            if self.wants_deferred():
                kinds += [S_FOR]  # a loop that can assign a new variable
            if self.wants(MU_RET_UNINIT):
                kinds += [S_IF, S_IF, S_IF]  # an `if` that can return
            if self.wants(MU_BREAK_MOVED) or self.wants_near(NR_LOOP_EXIT):
                # loops, and in them `if`s that can break
                if ctx.in_loop > 0:
                    kinds += [S_IF, S_IF, S_IF]
                else:
                    kinds += [S_FOR, S_FOR]
        if ctx.region_loops >= 0 and ctx.in_loop > ctx.region_loops:
            # (no loop in a loop where a field is moved out: see
            # `partial_stmts`)
            var others = List[Int]()
            for k in kinds:
                if k != S_FOR:
                    others.append(k)
            kinds = others^
        var kind = kinds[pick(data, len(kinds))]

        if kind == S_TRY:
            return self.try_statement(data, ctx)
        if kind == S_CIF:
            return self.cif_statement(data, ctx)
        if kind == S_MATCH:
            return self.pattern_statement(data, ctx)

        if kind == S_VAR:
            # half the time a type with `mut` methods, to call them on
            var receivers = self.mut_receivers(ctx)
            var ty: Int
            if len(receivers) > 0 and data.draw(booleans()):
                ty = receivers[pick(data, len(receivers))]
            else:
                ty = self.draw_type(data, ctx.pool)
            if ty == self.int_ty and (
                self.wants(MU_LOOP_MOVE)
                or self.wants(MU_USE_MOVED)
                or self.wants_near(NR_REINIT)
                or self.wants_near(NR_MOVE_COPY)
                or self.wants_near(NR_DISCARD_MOVE)
                or self.wants(MU_MAYBE_MOVED)
                or self.wants_near(NR_MAYBE_MOVED)
                or self.wants_near(NR_REINIT_PATHS)
                or self.wants(MU_BREAK_MOVED)
                or self.wants_near(NR_LOOP_EXIT)
            ):
                # (these mutants and near misses move a variable, and not
                # an Int)
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
            # (a moved v, perhaps by e, is assigned by name: through a
            # `ref`, it would be a use of v)
            var target = self.spell(data, ctx, v, f, True) if ctx.live[
                v
            ] else self.place_expr(ctx, v, f)
            if f < 0:
                ctx.live[v] = True
                ctx.move_depth[v] = -1
                if (
                    ty != self.int_ty
                    and getenv("DECL_FUZZ_NO_SELF_ASSIGN_WORKAROUND") == ""
                ):
                    # `v = (v if c else w)` gives garbage, or w's value,
                    # when it picks v, at -O1+ (as `v = v`,
                    # modular/modular#7760): `v.copy()` in that branch
                    e = self.copy_self_branches(e, v)
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
            var const_cond = self.is_const(x) and self.is_const(y)
            # a plan for one variable (pv), for the path kinds
            var plan = self.draw_plan(data, ctx, x, y)
            var pv = -1
            var mode = -1
            var br = -1
            var pre = -1
            var start_live = False
            var start_depth = -1
            if len(plan) > 0:
                pv = plan[0]
                mode = plan[1]
                br = plan[2]
                if plan[3] == PRE_MOVE:
                    pre = self.move_stmt(ctx, pv)
                    ctx.move_depth[pv] = ctx.depth
                elif plan[3] == PRE_DECL:
                    pre = self.decl_stmt(data, ctx, self.near >= 0)
                    pv = len(ctx.names) - 1
                start_live = ctx.live[pv]
                start_depth = ctx.move_depth[pv]
                if self.near >= 0 and plan[3] != PRE_DECL:
                    x = self.mark_near(x)
            var in_then = pv >= 0 and br != BR_ELSE
            var in_else = pv >= 0 and br != BR_THEN
            var exit = self.draw_exit(data, ctx, const_cond, mode, br)
            var ret_br = exit[0] if len(exit) > 0 else -1
            var exit_kind = exit[1] if len(exit) > 0 else -1
            ctx.depth += 1
            ctx.const_if += Int(const_cond)
            var then = self.gen_block(
                data,
                ctx,
                2,
                False,
                pv if in_then and mode == PLAN_MOVE else -1,
                pv if in_then and mode == PLAN_REINIT else -1,
                exit_kind if ret_br == BR_THEN else -1,
            )
            var then_live = False
            if pv >= 0:  # (as it was before the then branch)
                then_live = ctx.live[pv]
                ctx.live[pv] = start_live
                ctx.move_depth[pv] = start_depth
            var orelse = self.gen_block(
                data,
                ctx,
                2,
                False,
                pv if in_else and mode == PLAN_MOVE else -1,
                pv if in_else and mode == PLAN_REINIT else -1,
                exit_kind if ret_br == BR_ELSE else -1,
            )
            ctx.const_if -= Int(const_cond)
            ctx.depth -= 1
            var st = self.add_stmt(
                Stmt(S_IF, -1, x, y, op, then^, orelse^, String())
            )
            if pv < 0:
                return st
            # (the state the branches that don't return left)
            var all_init = (then_live or ret_br == BR_THEN) and (
                ctx.live[pv] or ret_br == BR_ELSE
            )
            return self.finish_plan(data, ctx, pre, st, pv, mode, all_init)

        # S_FOR; for a deferred kind, perhaps `var dv: T` before it, which
        # the body assigns (and the near miss uses there)
        var pre = -1
        var dv = -1
        if self.wants_deferred() and self.deferred_chance(data, ctx):
            pre = self.decl_stmt(data, ctx, self.near >= 0)
            dv = len(ctx.names) - 1
        if self.wants_loop_exit(ctx):
            # break_moved and loop_exit need a variable from outside the
            # loop to move (for a mutant, not one an enclosing loop uses)
            var lo = ctx.loop_base if self.mutant == MU_BREAK_MOVED else 0
            var have = False
            for v in self.owned_vars(ctx, len(ctx.names)):
                have = have or v >= lo
            var ty = self.draw_type(data, ctx.pool)
            if not have and ty != self.int_ty:
                ctx.new_statement()
                var init = self.gen(
                    data, ctx, ty, BODY_SIZE - 1, P_OWNED, False, True
                )
                var vname = String("v", ctx.counter)
                ctx.counter += 1
                ctx.push(vname.copy(), ty, V_OWNED)
                var st = self.add_stmt(
                    Stmt(S_VAR, -1, init, -1, 0, [], [], vname^)
                )
                if pre >= 0:  # (with dv's declaration: one group)
                    pre = self.add_stmt(
                        Stmt(S_USE, -1, -1, -1, 0, [pre, st], [], String())
                    )
                else:
                    pre = st
        var count = data.draw(integers(0, 3))
        # a third of the loops are `while` loops on a counter, a `var`
        # (but not for the mutants that assign or mut-borrow a read
        # variable, which the counter would look like)
        var is_while = data.draw(integers(0, 2)) == 0 and not (
            self.mutant == MU_ASSIGN_READ or self.mutant == MU_MUT_READ
        )
        var name = String("i", ctx.counter)
        ctx.counter += 1
        var n = len(ctx.names)
        ctx.push(name.copy(), self.int_ty, V_READ)
        ctx.depth += 1
        var loop_base = ctx.loop_base
        var parent_base = ctx.parent_base
        var loop_live = ctx.loop_live.copy()
        ctx.parent_base = loop_base
        ctx.loop_base = n
        ctx.loop_live = ctx.live.copy()
        ctx.in_loop += 1
        # (a `break` of an enclosing loop's body, drawn before this loop,
        # belongs to that loop)
        var outer_bv = ctx.break_var
        ctx.break_var = -1
        var body = self.gen_block(data, ctx, 2, True, -1, dv)
        ctx.in_loop -= 1
        ctx.loop_live = loop_live^
        ctx.parent_base = parent_base
        if dv >= 0 and self.near >= 0 and ctx.live[dv]:
            ctx.new_statement()
            var use = self.place_expr(ctx, dv, -1)
            body.append(self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], "")))
        ctx.loop_base = loop_base
        ctx.depth -= 1
        ctx.truncate(n)
        var loop = self.add_stmt(
            Stmt(S_FOR, 1 if is_while else -1, -1, -1, count, body^, [], name^)
        )
        var bv = ctx.break_var  # (moved before a `break` of this loop)
        ctx.break_var = outer_bv
        if bv >= 0:
            ctx.live[bv] = False
            ctx.move_depth[bv] = ctx.depth
        if dv >= 0 or bv >= 0 or pre >= 0:
            var group = List[Int]()
            if pre >= 0:
                group.append(pre)
            if dv >= 0:
                # the loop may run no times: dv is maybe-uninitialized
                ctx.live[dv] = False
                ctx.move_depth[dv] = ctx.depth
            group.append(self.loop_uses(loop, ctx, n))
            ctx.new_statement()
            if bv >= 0 and self.mutant == MU_BREAK_MOVED:
                ctx.move_depth[bv] = -2
                var use = self.mark(self.place_expr(ctx, bv, -1))
                group.append(
                    self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                )
            elif bv >= 0 and data.draw(booleans()):
                group.append(self.gen_reinit(data, ctx, bv))
                var use = self.place_expr(ctx, bv, -1)
                group.append(
                    self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                )
            if dv < 0:
                pass
            elif self.mutant == MU_UNINIT:
                ctx.move_depth[dv] = -2
                var use = self.mark(self.place_expr(ctx, dv, -1))
                group.append(
                    self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                )
            elif data.draw(booleans()):
                group.append(self.gen_reinit(data, ctx, dv))
                var use = self.place_expr(ctx, dv, -1)
                group.append(
                    self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                )
            return self.add_stmt(
                Stmt(S_USE, -1, -1, -1, 0, group^, [], String())
            )
        return self.loop_uses(loop, ctx, n)

    def loop_uses(mut self, loop: Int, ctx: Ctx, n: Int) -> Int:
        """The loop statement, perhaps in an S_USE group with reads after
        it (the workaround below); n variables are in scope."""
        if (
            self.loop_mark == ctx.depth + 1
        ):  # this loop's body, not a nested one
            self.marked_stmts.append(loop)
            self.loop_mark = -1
        if getenv("DECL_FUZZ_NO_LOOP_STORE_WORKAROUND") != "":
            return loop
        # A variable whose last use is a field assignment in a loop is
        # destroyed on every iteration (modular/modular#7759; also when it
        # is assigned whole after the loop, and for a `mut` argument or
        # `mut self`), so the loop is followed by a read of each live owned
        # or `mut` variable. The loop and the reads form one S_USE group.
        var uses: List[Int] = [loop]
        for v in range(n):
            if ctx.kinds[v] != V_READ and ctx.live[v]:
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
            if (
                ctx.from_tuple[v]
                and getenv("DECL_FUZZ_NO_TUPLE_VAR_WORKAROUND") == ""
            ):
                continue  # (see Ctx.from_tuple)
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
        var places = self.mut_places(ctx, ty)
        if self.wants_near(NR_DISJOINT):
            # another field of a variable a field of which is taken
            var good = self.disjoint_places(ctx, ty)
            if len(good) > 0 and (
                len(places) == 0 or self.near_chance(data, NR_DISJOINT)
            ):
                self.chances += Int(len(places) == 0)
                var p = good[pick(data, len(good))]
                ctx.touched[p // 64] = True
                ctx.taken.append(p)
                return self.mark_near(
                    self.spell(data, ctx, p // 64, p % 64 - 1, True)
                )
        if len(bad) > 0 and (
            # (places_for let the call go ahead for the mutant)
            len(places) == 0
            or self.chance(data, self.mutant)
        ):
            self.chances += Int(len(places) == 0)
            var p = bad[pick(data, len(bad))]
            ctx.touched[p // 64] = True
            return self.mark(self.spell(data, ctx, p // 64, p % 64 - 1))
        if len(places) == 0:
            raise Error("STUCK")
        var p = places[pick(data, len(places))]
        var v = p // 64
        ctx.excl[v] = True
        ctx.touched[v] = True
        ctx.taken.append(p)
        return self.spell(data, ctx, v, p % 64 - 1, True)

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
        different root variables (greedily). For a mut_read or alias
        mutant, one of them may have only a read place, or one sharing a
        root variable: take_place makes the mutant there. So may one for
        a disjoint near miss (another field of a root variable used)."""
        var used = List[Int]()
        var spare = (
            self.wants(MU_MUT_READ)
            or self.wants(MU_ALIAS)
            or self.wants_near(NR_DISJOINT)
        )
        for ty in needed:
            var found = False
            var places = self.mut_places(ctx, ty)
            for p in places:
                if not has(used, p // 64):
                    used.append(p // 64)
                    found = True
                    break
            if found:
                continue
            if spare and (
                len(places)
                > 0 if not self.wants(MU_MUT_READ) else len(
                    self.read_places(ctx, ty)
                )
                > 0
            ):
                spare = False
                continue
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
                    and not self.is_generic_method(m)
                    and self.methods[m].rank < ctx.rank
                    and self.raise_ok(ctx, self.method_raise(m, r))
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
                or not self.raise_ok(ctx, self.fns[f].raise_ty)
            ):
                continue
            var needed = List[Int]()
            for j in range(len(self.fns[f].params)):
                if self.fns[f].convs[j] == CONV_MUT:
                    needed.append(self.fns[f].params[j])
            if self.places_for(ctx, needed) and not has(out, self.fns[f].ret):
                out.append(self.fns[f].ret)
        return out^

    def gen_args(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        params: List[Int],
        convs: List[Int],
        size: Int,
        mut_call: Bool,
    ) raises -> List[Int]:
        """A call's arguments, in order. For a move_copy near miss, after
        an argument `x^` (not an Int), the later ones may use x: Mojo moves
        it at the call, after evaluating them. Not as a place passed read,
        which would borrow it (an aliasing error): such an argument gets
        `.copy()`, or is drawn again without x if its type isn't
        Copyable."""
        # (a struct can contain itself through associated types: B's field
        # `Self.T.E0.E0` in B[S], with S.E0 = C and C.E0 = B[S]; values of
        # it can't be made)
        if ctx.nest > MAX_NEST:
            raise Error("STUCK")
        ctx.nest += 1
        var kids = List[Int]()
        var moved = -1
        var moved_kind = 0
        for j in range(len(params)):
            var later = j < len(params) - 1
            if moved < 0 or not self.wants_near(NR_MOVE_COPY):
                var k = self.gen_arg(
                    data, ctx, params[j], convs[j], size, mut_call, later
                )
                kids.append(k)
                if (
                    moved < 0
                    and self.wants_near(NR_MOVE_COPY)
                    and self.exprs[k].kind == E_MOVE
                    and self.exprs[k].ty != self.int_ty
                ):
                    moved = self.exprs[k].a
                    moved_kind = ctx.kinds[moved]
                continue
            # x usable, as a read variable (so neither moved nor `mut`)
            ctx.live[moved] = True
            ctx.kinds[moved] = V_READ
            var saved = ctx.copy()
            var state = self.mutation_state()
            var k = self.gen_arg(
                data, ctx, params[j], convs[j], size, mut_call, later
            )
            ctx.live[moved] = False
            ctx.kinds[moved] = moved_kind
            if (
                convs[j] == CONV_READ
                and params[j] != self.int_ty
                and self.borrows_var(k, moved)
            ):
                if self.cap_of(params[j], ctx.bounds) >= CAP_C:
                    var text = String(self.exprs[k].text, ".copy()")
                    k = self.add(E_COPY, 0, params[j], [k], [], text^)
                else:
                    ctx = saved^
                    self.restore_mutation(state)
                    ctx.live[moved] = False
                    ctx.kinds[moved] = moved_kind
                    k = self.gen_arg(
                        data, ctx, params[j], convs[j], size, mut_call, later
                    )
            if self.uses_var(k, moved):
                k = self.mark_near(k)
            kids.append(k)
        # (where_workaround: a T place passed for a T parameter is
        # rejected too, `g1[Self.T](self.f0)`)
        for j in range(len(kids)):
            if convs[j] != CONV_MUT:
                kids[j] = self.where_copies([kids[j]])[0]
        ctx.nest -= 1
        return kids^

    def gen_arg(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        conv: Int,
        size: Int,
        mut_call: Bool = False,
        later: Bool = False,
    ) raises -> Int:
        """An argument; mut_call says the call has `mut` arguments, and
        later that more arguments follow this one."""
        if conv == CONV_MUT:
            return self.take_place(data, ctx, ty)
        if conv == CONV_READ and ty != self.int_ty:
            # near misses: a read argument that is a field disjoint from a
            # `mut` one, or that overlaps a value read already
            var good = List[Int]()
            if mut_call and self.wants_near(NR_DISJOINT):
                good = self.disjoint_places(ctx, ty)
            elif self.wants_near(NR_READ_ALIAS):
                good = self.read_alias_places(ctx, ty)
            if len(good) > 0 and self.near_chance(data, self.near):
                var p = good[pick(data, len(good))]
                ctx.touched[p // 64] = True
                return self.mark_near(
                    self.spell(data, ctx, p // 64, p % 64 - 1)
                )
        if (
            conv == CONV_VAR
            and later
            and ty != self.int_ty
            and ctx.no_move == 0
            and self.wants_near(NR_MOVE_COPY)
        ):
            # `x^`, so that the later arguments may use x (gen_args)
            var owned = List[Int]()
            for v in self.owned_vars(ctx, len(ctx.names)):
                if (
                    ctx.types[v] == ty
                    and not ctx.touched[v]
                    and not ctx.excl[v]
                ):
                    owned.append(v)
            if len(owned) > 0 and self.near_chance(data, NR_MOVE_COPY):
                var v = owned[pick(data, len(owned))]
                ctx.live[v] = False
                ctx.move_depth[v] = ctx.depth
                ctx.touched[v] = True
                return self.add(
                    E_MOVE, v, ty, [], [], String(ctx.names[v], "^")
                )
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
                return self.mark(self.spell(data, ctx, p // 64, p % 64 - 1))
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
                and not self.in_const_if(ctx)
                and self.chance(data, MU_USE_MOVED)
            ):
                var v = dead[pick(data, len(dead))]
                # (through a binding: a `ref` outliving its origin)
                var e = self.spell(data, ctx, v, -1)
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
            for v in range(ctx.freeze_base, len(ctx.names)):
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

        if self.wants(MU_REF_MOVE) and pos == P_OWNED and kind != INT:
            # `^` on a place spelled through a `ref`
            var texts = List[String]()
            for v in range(len(ctx.names)):
                if not ctx.live[v] or ctx.excl[v]:
                    continue
                var vty = ctx.types[v]
                var fs = self.fields_of(vty)
                for f in range(len(fs)):
                    if fs[f] == ty and self.has_accessor(vty, f):
                        texts.append(String(ctx.names[v], ".f", f, "_ref()"))
                for b in range(len(ctx.ref_names)):
                    if ctx.ref_var[b] != v:
                        continue
                    var f = ctx.ref_field[b]
                    if (vty if f < 0 else fs[f]) == ty:
                        texts.append(ctx.ref_names[b])
                    elif f < 0:
                        for g in range(len(fs)):
                            if fs[g] == ty:
                                texts.append(
                                    String(
                                        ctx.ref_names[b],
                                        ".",
                                        self.field_name(vty, g),
                                    )
                                )
            if len(texts) > 0 and self.chance(data, MU_REF_MOVE):
                var text = String(texts[pick(data, len(texts))], "^")
                return self.mark(self.add(E_LIT, 0, ty, [], [], text^))

        if size > 0 and self.wants(MU_RAISE_CTX):
            var rc = self.raise_ctx_call(data, ctx, ty, size)
            if rc >= 0:
                return rc
        if size > 0 and (self.wants(MU_WHERE) or self.wants_near(NR_WHERE)):
            var g = self.gated_call(data, ctx, ty, size, pos)
            if g >= 0:
                return g

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
                    and not self.tuple_bound(ctx, v)
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
        # `V[k].n` and `Self.n`
        var valn = List[Int]()
        if kind == INT:
            for t in ctx.pool:
                if self.is_valued(t):
                    valn.append(t)

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
                var ms = self.methods_on(r, ctx.bounds)
                if (
                    self.wants(MU_VWHERE)
                    and rk == STRUCT
                    and not self.in_branch(ctx)
                ):
                    # (gated methods whose `where` fails for r: choosing
                    # one is the vwhere mutant's chance)
                    for m in self.structs[self.tid[r]].own:
                        if not self.mw_holds(m, r):
                            ms.append(m)
                # (raising ones only where the error goes; one that nothing
                # catches is the raise_ctx mutant's chance)
                var ctx_bad = self.wants(MU_RAISE_CTX) and self.raise_ctx_here(
                    ctx
                )
                for m in ms:
                    if (
                        self.methods[m].rank < ctx.rank
                        and (
                            ctx_bad
                            or self.raise_ok(ctx, self.method_raise(m, r))
                        )
                        and self.method_fit(m, r, ty, ctx) > -2
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
                if self.fns[f].rank >= ctx.rank or not self.raise_ok(
                    ctx, self.fns[f].raise_ty
                ):
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
        if len(valn) > 0:
            rules.append(R_VALN)
        if kind == STRUCT or kind == RES:
            rules.append(R_NEW)
        if len(makes) > 0:
            rules += [R_MAKE, R_MAKE]
        if size > 0:
            if kind == INT:
                rules.append(R_BIN)
            if not self.where_workaround():
                rules.append(R_TERN)
            if len(field_recv) > 0:
                rules.append(R_FIELD)
            if len(meth_recv) > 0:
                rules += [R_METHOD, R_METHOD, R_METHOD, R_METHOD]
            if len(k_recv) > 0:
                rules += [R_K, R_K]
            if len(call_fn) > 0:
                rules += [R_CALL, R_CALL, R_CALL]
                # (in a `try` body, raising calls are the point)
                if ctx.catching > 0:
                    var raising = List[Int]()
                    for f in call_fn:
                        if self.fns[f].raise_ty != -1:
                            raising.append(f)
                    if len(raising) > 0:
                        rules += [R_CALL, R_CALL, R_CALL]
                        if data.draw(booleans()):
                            call_fn = raising^
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
            valn^,
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

    def mut_moved(self, ctx: Ctx) -> Bool:
        """Whether a `mut` argument (not a `deinit self`) is moved now: an
        error leaving the function then is "use of uninitialized value"
        at the raise point, as a `return` would be."""
        for v in range(len(ctx.names)):
            if (
                ctx.kinds[v] == V_MUT
                and not ctx.live[v]
                and not self.is_deinit_self(v)
            ):
                return True
        return False

    def raise_ok(self, ctx: Ctx, r: Int) -> Bool:
        """Whether a call raising r (FnDecl.raise_ty) can go here: in a `try`
        body (its handlers will cover r), or where the error propagates
        (`raises`, or `raises Xr`), but not where a field is moved out
        (ctx.no_exit: an exit would leave the variable partly moved)."""
        if r == -1:
            return True
        if ctx.no_exit > 0 and ctx.catching <= ctx.exit_catch:
            return False
        if ctx.catching == 0 and self.mut_moved(ctx):
            return False
        if ctx.fin_type != -9 and ctx.catching == ctx.fin_catch:
            if r != ctx.fin_type:
                return False
        if ctx.catching > 0:
            # Mojo crashes on a `try` whose raising call is in a dead
            # branch (`if False:`) and is followed by another statement
            # (modular/modular#7813): none in a
            # constant `if`, or a ternary's branch, there
            if (ctx.const_if > 0 or ctx.no_move > 0) and getenv(
                "DECL_FUZZ_NO_DEAD_RAISE_WORKAROUND"
            ) == "":
                return False
            return True
        return ctx.raise_ty == -2 or (r >= 0 and ctx.raise_ty == r)

    def raise_ctx_here(self, ctx: Ctx) -> Bool:
        """Whether a raise_ctx mutant's call can go here: not in a dead
        branch (Mojo drops it before checking), nor where a field is moved
        out (Mojo reports the move instead), nor in a `finally` (whose
        error types are restricted, fin_type)."""
        return not (
            self.in_branch(ctx)
            or self.in_const_if(ctx)
            or ctx.no_exit > 0
            or ctx.in_finally > 0
        )

    def raise_ctx_call(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        size: Int,
    ) raises -> Int:
        """For MU_RAISE_CTX, a call of a raising function (not generic,
        without `mut` arguments) whose error nothing here catches, or
        -1."""
        if not self.raise_ctx_here(ctx):
            return -1
        var cands = List[Int]()
        for f in range(len(self.fns)):
            ref fd = self.fns[f]
            if (
                fd.raise_ty != -1
                and not self.raise_ok(ctx, fd.raise_ty)
                and len(fd.bounds) == 0
                and fd.rank < ctx.rank
                and fd.ret == ty
                and not has(fd.convs, CONV_MUT)
            ):
                cands.append(f)
        if len(cands) == 0 or not self.chance(data, MU_RAISE_CTX):
            return -1
        self.mutated = True
        var f = cands[pick(data, len(cands))]
        var params = self.fns[f].params.copy()
        var convs = self.fns[f].convs.copy()
        var kids = self.gen_args(data, ctx, params, convs, size // 2, False)
        var text = String(self.fns[f].name, "(", self.args_text(kids, 0), ")")
        return self.mark(self.add(E_CALL, f, ty, kids^, [], text^))

    def raise_if(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> List[Int]:
        """Now and then `if c: raise Xk(e)`: in a `try` body (any k, which
        its handlers will catch), or in a raising function's body where a
        field isn't moved out (k is the declared type, any for `raises`;
        another for MU_RAISE_TYPE)."""
        if ctx.no_exit > 0 and ctx.catching <= ctx.exit_catch:
            return []
        var caught = ctx.catching > 0
        if not caught and self.mut_moved(ctx):
            return []
        if (
            caught
            and (ctx.const_if > 0 or ctx.no_move > 0)
            and getenv("DECL_FUZZ_NO_DEAD_RAISE_WORKAROUND") == ""
        ):
            return []  # (the dead-branch crash, as in `raise_ok`)
        if not caught and ctx.raise_ty == -1:
            return []
        var in_fin = ctx.fin_type != -9 and ctx.catching == ctx.fin_catch
        if in_fin and ctx.fin_type < 0:
            return []  # (a `finally` raises one type, Ctx.fin_type)
        var odds = 2
        if data.draw(integers(0, odds - 1)) != 0:
            return []
        ctx.new_statement()
        var x = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
        var y = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
        if self.is_const(x) and self.is_const(y):
            return []
        var op = pick(data, comptime (len(CMP_OPS)))
        ctx.depth += 1
        var k = ctx.raise_ty if (ctx.raise_ty >= 0 and not caught) else pick(
            data, self.n_err
        )
        if in_fin:
            k = ctx.fin_type
        var e = self.gen_typed(data, ctx, self.int_ty, 2, P_OWNED)
        if caught and not has(ctx.raised, k):
            ctx.raised.append(k)
        if (
            not caught
            and ctx.raise_ty >= 0
            and self.wants(MU_RAISE_TYPE)
            and not self.in_const_if(ctx)
            and ctx.in_finally == 0
            and self.chance(data, MU_RAISE_TYPE)
        ):
            k = (ctx.raise_ty + 1) % self.n_err
            e = self.mark(e)
            self.mutated = True
        # (X2 also carries a value)
        var val = -1
        if k == N_ERR:
            val = self.gen_typed(data, ctx, self.carry_ty, 2, P_OWNED)
        ctx.depth -= 1
        var r = self.add_stmt(Stmt(S_RAISE, -1, e, val, k, [], [], ""))
        return [self.add_stmt(Stmt(S_IF, -1, x, y, op, [r], [], String()))]

    def cif_statement(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        """`comptime if <prop>:` about the function's value parameter n,
        with an `else` half the time: the body knows prop (Mojo's evidence
        for a `where`), so it's mostly one another function on V needs with
        n + d for n and isn't known yet; else one true of a value of V's.
        Outer variables are read-only in both branches (Mojo checks moves
        per instantiation, after dropping a branch), which are drawn as a
        constant `if`'s."""
        var f = self.cif_fn
        var vi = self.vw_fn_index(f)
        var vs = self.tid[self.fns[f].params[vi]]
        var cands = List[Prop]()
        for r in self.reqs_on(vs, f):
            var key = Self.prop_key(vi, r.c, r.ge, r.k)
            if not has(self.vfacts, key) and not has(self.vfacts_assert, key):
                cands.append(r.copy())
        var pr: Prop
        if len(cands) > 0 and data.draw(integers(0, 3)) > 0:
            pr = cands[pick(data, len(cands))].copy()
            pr.form = data.draw(integers(0, 3))
        else:
            pr = self.draw_prop(data, vs, f)
        var key = Self.prop_key(vi, pr.c, pr.ge, pr.k)
        var added = not has(self.vfacts, key) and not has(
            self.vfacts_assert, key
        )
        var n = len(ctx.names)
        var kinds = ctx.kinds.copy()
        var freeze = ctx.freeze_base
        for v in range(n):
            ctx.kinds[v] = V_READ
        ctx.freeze_base = n
        ctx.const_if += 1
        ctx.depth += 1
        if added:
            self.vfacts_assert.append(key)
        var body = self.gen_block(data, ctx, 3, False)
        if added:
            _ = self.vfacts_assert.pop()
        ctx.truncate(n)
        var orelse = List[Int]()
        if data.draw(booleans()):
            orelse = self.gen_block(data, ctx, 3, False)
            ctx.truncate(n)
        ctx.depth -= 1
        ctx.const_if -= 1
        for v in range(n):
            ctx.kinds[v] = kinds[v]
        ctx.freeze_base = freeze
        var text = self.prop_text(pr, vi, ctx.param_names)
        return self.add_stmt(Stmt(S_CIF, -1, -1, -1, key, body^, orelse^, text))

    # ---- patterns: `match`, `if` with `case` clauses, `guard`, `var (..)`

    def pattern_ok(mut self, ty: Int) -> Bool:
        """Whether a struct pattern can match ty: a struct (or Res) with
        fields. In a body with a `where`, not one that mentions a type
        parameter: Mojo gives the subject the refined type, which doesn't
        match the pattern's (modular/modular#7811: "cannot match value of
        type 'B0[T(Tr1)]' against pattern type 'B0[T]'"), unless
        DECL_FUZZ_NO_WHERE_WORKAROUND=1."""
        var k = self.tkind[ty]
        if self.where_workaround() and self.mentions_param(ty):
            return False
        return (k == STRUCT or k == RES) and len(self.fields_of(ty)) > 0

    def add_pat(mut self, var p: PatNode) -> Int:
        self.pats.append(p^)
        return len(self.pats) - 1

    def tuple_var_workaround(self) -> Bool:
        """A `var` binding from a temporary tuple is "use of uninitialized
        value '(tuple element)'" beside an element pattern that can fail
        (`case (var z, 3) = (e1, e2)`), and in `if` and `match` when it's
        bound by a `ref` and another element isn't a `var` (`case (var
        z, w) = (e1, e2)` then `ref r = z`): a tuple with a `var` element
        has only `var` elements (DECL_FUZZ_NO_TUPLE_VAR_WORKAROUND=1 lifts
        it). In a `guard`, one after the first clause copies its elements
        ("cannot be implicitly copied"): no `var` elements there
        (DECL_FUZZ_NO_GUARD_VAR_WORKAROUND=1 allows them)."""
        return getenv("DECL_FUZZ_NO_TUPLE_VAR_WORKAROUND") == ""

    def sub_pattern(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        field: Int,
        place: Bool,
        nested: Int,
        refutable: Bool,
        mut binds: List[Int],
        allow_var: Bool = True,
    ) raises -> Int:
        """The pattern for one field (field >= 0) or tuple element of type
        ty. In a variable subject (place), a name binds the field
        read-only, and nested patterns bind nothing (their places would
        be deeper); without refutable, only `_`, names and `var` names."""
        var kinds: List[Int] = [PK_WILD, PK_BIND, PK_BIND]
        if place and field < 0:
            kinds = [PK_WILD]
        if allow_var and self.cap_of(ty, ctx.bounds) == CAP_IC:
            kinds.append(PK_VAR)
        if refutable and ty == self.int_ty:
            kinds += [PK_LIT, PK_LIT, PK_OR, PK_EQ]
        if refutable and nested < 1 and self.pattern_ok(ty):
            kinds.append(PK_STRUCT)
        var k = kinds[pick(data, len(kinds))]
        var bad_var = False
        if (
            field >= 0
            and place  # (out of a temporary, it may become a move: #7659)
            and self.cap_of(ty, ctx.bounds) < CAP_IC
            and not self.in_const_if(ctx)
            and self.chance(data, MU_PAT_VAR)
        ):
            # (a copy of a field: Mojo moves only out of a tuple)
            k = PK_VAR
            bad_var = True
            self.mutated = True
        if k == PK_STRUCT:
            return self.struct_pattern(
                data, ctx, ty, place, nested + 1, binds, allow_var
            )
        if k == PK_LIT:
            var l = pick(data, len(self.literals))
            return self.add_pat(PatNode(k, ty, l, -1, False, "", [], []))
        if k == PK_OR:
            var l1 = pick(data, len(self.literals))
            var l2 = pick(data, len(self.literals))
            return self.add_pat(PatNode(k, ty, l1, l2, False, "", [], []))
        if k == PK_EQ:
            # (it runs only if the fields before it matched: no moves)
            ctx.no_move += 1
            var e = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
            ctx.no_move -= 1
            return self.add_pat(PatNode(k, ty, e, -1, False, "", [], []))
        if k == PK_WILD:
            return self.add_pat(PatNode(k, ty, -1, -1, False, "", [], []))
        var name = String(MARK if bad_var else "", "b", ctx.counter)
        ctx.counter += 1
        # (a name in a variable subject's top level: a read-only `ref`
        # binding to the field, else a local)
        var push = k == PK_VAR or not place
        var p = self.add_pat(PatNode(k, ty, -1, field, push, name^, [], []))
        binds.append(p)
        return p

    def struct_pattern(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        place: Bool,
        nested: Int,
        mut binds: List[Int],
        allow_var: Bool = True,
    ) raises -> Int:
        """`Head(f0=p0, ...)` for some of ty's fields (at least one)."""
        var fs = self.fields_of(ty)
        var fields = List[Int]()
        for f in range(len(fs)):
            if data.draw(integers(0, 2)) > 0:
                fields.append(f)
        if len(fields) == 0:
            fields.append(pick(data, len(fs)))
        var kids = List[Int]()
        for f in fields:
            kids.append(
                self.sub_pattern(
                    data,
                    ctx,
                    fs[f],
                    f if nested == 0 else -1,
                    place,
                    nested,
                    True,
                    binds,
                    allow_var,
                )
            )
        var head = self.cty(ty, ctx)
        var bad = -1
        if (
            nested == 0
            and not self.in_const_if(ctx)
            and self.chance(data, MU_PAT_FIELD)
        ):
            # (its first field is written `z`)
            bad = -7
            head = String(MARK, head)
            self.mutated = True
        return self.add_pat(
            PatNode(PK_STRUCT, ty, -1, bad, False, head^, fields^, kids^)
        )

    def subject_pattern(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        place: Bool,
        mut binds: List[Int],
    ) raises -> Int:
        """A struct pattern for a subject of type ty; for a pat_type mutant,
        perhaps for another type (its names then bind locals)."""
        if self.wants(MU_PAT_TYPE) and not self.in_const_if(ctx):
            var others = List[Int]()
            for t in ctx.pool:
                if t != ty and self.pattern_ok(t):
                    others.append(t)
            if len(others) > 0 and self.chance(data, MU_PAT_TYPE):
                var t = others[pick(data, len(others))]
                var p = self.struct_pattern(data, ctx, t, False, 0, binds)
                self.pats[p].name = String(MARK, self.pats[p].name)
                self.mutated = True
                return p
        return self.struct_pattern(data, ctx, ty, place, 0, binds)

    def irrefutable(self, p: Int) -> Bool:
        """Whether pattern p matches every value."""
        ref node = self.pats[p]
        if node.kind == PK_WILD or node.kind == PK_BIND or node.kind == PK_VAR:
            return True
        if node.kind != PK_STRUCT and node.kind != PK_TUPLE:
            return False
        for k in node.kids:
            if not self.irrefutable(k):
                return False
        return True

    def const_clauses(self, cs: Int) -> Bool:
        """Whether a `case` clause of set cs has a constant subject (`match
        100:`, `= (1, 2)`), which Mojo folds: its branches are drawn like a
        constant `if`'s, without raise points or mutants (a dead one isn't
        checked)."""
        for c in self.csets[cs]:
            ref cl = self.clauses[c]
            if (
                cl.kind == CL_BOOL
                and self.is_const(cl.l)
                and self.is_const(cl.r)
            ):
                return True  # (a constant comparison: folded too)
            if cl.kind != CL_CASE or len(cl.sexprs) == 0:
                continue
            var all_const = True
            for e in cl.sexprs:
                all_const = all_const and self.is_const(e)
            if all_const:
                return True
        return False

    def dead_else(self, cs: Int) -> Bool:
        """Whether Mojo takes the `else` of an `if` or `guard` with clause
        set cs for dead code: when its patterns are irrefutable (it
        ignores the Boolean clauses: "unreachable code after match that
        always completes", modular/modular#7829). Such an `else` is drawn like a constant
        `if`'s dead branch, without raising calls (modular/modular#7813)
        or mutants."""
        if self.const_clauses(cs):
            return True
        for c in self.csets[cs]:
            ref cl = self.clauses[c]
            if cl.kind == CL_CASE and not self.irrefutable(cl.l):
                return False
        return True

    def push_binds(
        mut self,
        mut ctx: Ctx,
        binds: List[Int],
        subj: Int,
        depth: Int,
        from_tuple: Bool = False,
    ):
        """Brings a pattern's bindings into scope: a local for each one
        that adds a variable, a read-only `ref` binding to the subject's
        field for the others."""
        for p in binds:
            ref node = self.pats[p]
            if node.push:
                var kind = V_OWNED if node.kind == PK_VAR else V_READ
                ctx.push(node.name.copy(), node.ty, kind)
                ctx.from_tuple[len(ctx.names) - 1] = from_tuple
            else:
                ctx.ref_names.append(node.name.copy())
                ctx.ref_var.append(subj)
                ctx.ref_field.append(node.b)
                ctx.ref_depth.append(depth)
                ctx.ref_ro.append(True)

    def subject_vars(mut self, ctx: Ctx) -> List[Int]:
        """Live variables a struct pattern can match (in place)."""
        var out = List[Int]()
        for v in range(len(ctx.names)):
            if (
                ctx.live[v]
                and not ctx.excl[v]
                and self.pattern_ok(ctx.types[v])
            ):
                out.append(v)
        return out^

    def rvalue_subject(
        mut self, mut data: ConjectureData, mut ctx: Ctx, ty: Int
    ) raises -> Int:
        """A temporary of type ty (a place is copied: `v.copy()`, or an
        Int `Int(v)`)."""
        var state = self.mutation_state()
        var e = self.gen_typed(data, ctx, ty, BODY_SIZE - 2, P_OWNED)
        if self.mutation_state() != state and (
            self.is_place(e) or self.mutant == MU_IMPLICIT_COPY
        ):
            # (an implicit_copy mutant's place: a valid subject, and with
            # `.copy()` a valid value; gen_stmt undoes it)
            raise Error("STUCK")
        if self.is_place(e):
            var text = String(self.exprs[e].text, ".copy()")
            if ty == self.int_ty:
                text = String("Int(", self.exprs[e].text, ")")
            e = self.add(E_COPY, 0, ty, [e], [], text^)
        return e

    def case_clause(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        depth: Int,
        first: Bool,
        in_guard: Bool = False,
    ) raises -> Int:
        """`case <pattern> = <subject>`, its bindings in scope after it (at
        depth): the subject a variable, a temporary struct, or a tuple of
        temporaries; moves only in the first clause (the others may not
        run)."""
        var tuple_var = not (
            in_guard
            and not first
            and getenv("DECL_FUZZ_NO_GUARD_VAR_WORKAROUND") == ""
        )
        ctx.no_move += Int(not first)
        var vars = self.subject_vars(ctx)
        var structs = List[Int]()
        for t in ctx.pool:
            if self.pattern_ok(t):
                structs.append(t)
        var form = data.draw(integers(0, 2))
        if form == 0 and len(vars) == 0:
            form = 1
        if form == 1 and len(structs) == 0:
            form = 2
        var binds = List[Int]()
        var cl: Clause
        var subj = -1
        if form == 0:
            subj = vars[pick(data, len(vars))]
            ctx.touched[subj] = True
            var p = self.subject_pattern(
                data, ctx, ctx.types[subj], True, binds
            )
            cl = Clause(CL_CASE, 0, p, -1, subj, [], ctx.names[subj].copy())
        elif form == 1:
            var ty = structs[pick(data, len(structs))]
            var e = self.rvalue_subject(data, ctx, ty)
            var p = self.subject_pattern(data, ctx, ty, False, binds)
            cl = Clause(CL_CASE, 0, p, -1, -1, [e], "")
        else:
            # a tuple of two or three temporaries, perhaps moved in
            var n = data.draw(integers(2, 3))
            var tys = List[Int]()
            var es = List[Int]()
            for _ in range(n):
                var ty = self.draw_type(data, ctx.pool)
                tys.append(ty)
                es.append(self.gen(data, ctx, ty, BODY_SIZE - 2, P_OWNED))
            var kids = List[Int]()
            # (with the workaround, all `var` names or none)
            var all_var = (
                tuple_var
                and self.tuple_var_workaround()
                and data.draw(booleans())
            )
            for i in range(n):
                if all_var:
                    var name = String("b", ctx.counter)
                    ctx.counter += 1
                    var k = self.add_pat(
                        PatNode(PK_VAR, tys[i], -1, -1, True, name^, [], [])
                    )
                    binds.append(k)
                    kids.append(k)
                    continue
                kids.append(
                    self.sub_pattern(
                        data,
                        ctx,
                        tys[i],
                        -1,
                        False,
                        0,
                        True,
                        binds,
                        tuple_var and not self.tuple_var_workaround(),
                    )
                )
            var p = self.add_pat(
                PatNode(PK_TUPLE, -1, -1, -1, False, "", [], kids^)
            )
            cl = Clause(CL_CASE, 0, p, -1, -1, es^, "")
        ctx.no_move -= Int(not first)
        self.push_binds(ctx, binds, subj, depth, form == 2)
        self.clauses.append(cl^)
        return len(self.clauses) - 1

    def bool_clause(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        """`l op r` on Ints (a guard, or a clause of an `if` or `guard`)."""
        var op = pick(data, comptime (len(CMP_OPS)))
        var x = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
        var y = self.gen_typed(data, ctx, self.int_ty, 1, P_READ)
        self.clauses.append(Clause(CL_BOOL, op, x, y, -1, [], ""))
        return len(self.clauses) - 1

    def clause_set(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        depth: Int,
        in_guard: Bool = False,
    ) raises -> Int:
        """One to three clauses, at least one a `case`, each seeing the
        bindings of those before it; Boolean ones after the first may
        not run, so they don't move anything either."""
        var n = data.draw(integers(1, 3))
        var at = pick(data, n)  # (a `case` there at least)
        var set = List[Int]()
        for i in range(n):
            if i == at or data.draw(booleans()):
                set.append(self.case_clause(data, ctx, depth, i == 0, in_guard))
            else:
                ctx.no_move += Int(i > 0)
                set.append(self.bool_clause(data, ctx))
                ctx.no_move -= Int(i > 0)
        self.csets.append(set^)
        return len(self.csets) - 1

    def can_guard(self, ctx: Ctx) -> Bool:
        """Whether a `guard` can exit here (its `else` returns, or in a
        loop breaks or continues)."""
        return (
            ctx.ret >= 0
            and ctx.no_exit == 0
            and ctx.in_finally == 0
            and not self.in_const_if(ctx)
        )

    def pattern_statement(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        """A `match`, an `if` with `case` clauses, a `guard`, or `var (bA,
        bB) = (e1, e2)`."""
        var forms: List[Int] = [S_MATCH, S_IFC, S_DESTR]
        if self.can_guard(ctx):
            forms += [S_GUARD, S_GUARD]
        if self.wants(MU_GUARD_FALL) and self.can_guard(ctx):
            forms = [S_GUARD]
        elif self.wants(MU_PAT_SCOPE):
            forms = [S_IFC, S_GUARD] if self.can_guard(ctx) else [S_IFC]
        var form = forms[pick(data, len(forms))]
        ctx.new_statement()
        if form == S_DESTR:
            var n = data.draw(integers(2, 3))
            var es = List[Int]()
            var kids = List[Int]()
            var binds = List[Int]()
            for _ in range(n):
                var ty = self.draw_type(data, ctx.pool)
                es.append(self.gen(data, ctx, ty, BODY_SIZE - 2, P_OWNED))
                var name = String("b", ctx.counter)
                ctx.counter += 1
                var p = self.add_pat(
                    PatNode(PK_VAR, ty, -1, -1, True, name^, [], [])
                )
                kids.append(p)
                binds.append(p)
            var p = self.add_pat(
                PatNode(PK_TUPLE, -1, -1, -1, False, "", [], kids^)
            )
            self.clauses.append(Clause(CL_CASE, 0, p, -1, -1, es^, ""))
            self.csets.append([len(self.clauses) - 1])
            self.push_binds(ctx, binds, -1, ctx.depth, True)
            return self.add_stmt(
                Stmt(S_DESTR, -1, -1, -1, len(self.csets) - 1, [], [], "")
            )
        if form == S_MATCH:
            return self.match_statement(data, ctx)
        var n = len(ctx.names)
        if form == S_GUARD:
            var nref = len(ctx.ref_names)
            var set = self.clause_set(data, ctx, ctx.depth, True)
            if self.const_clauses(set):
                # (Mojo folds it: a false one would make the rest of the
                # block dead, and unchecked)
                raise Error("STUCK")
            if (
                ctx.catching > 0
                and self.dead_else(set)
                and getenv("DECL_FUZZ_NO_GUARD_TRY_WORKAROUND") == ""
            ):
                # (in a `try` body, a `guard` whose patterns always match
                # can hide a use of a variable the `try`'s `else` moved:
                # an accepted try_move mutant; gen_stmt draws another
                # statement)
                raise Error("STUCK")
            # the `else` doesn't see the bindings: out of scope for it
            var saved = ctx.copy()
            ctx.truncate(n)
            while len(ctx.ref_names) > nref:
                _ = ctx.ref_names.pop()
                _ = ctx.ref_var.pop()
                _ = ctx.ref_field.pop()
                _ = ctx.ref_depth.pop()
                _ = ctx.ref_ro.pop()
            var exit = S_RETURN
            if ctx.in_loop > 0 and data.draw(booleans()):
                exit = S_BREAK if data.draw(booleans()) else S_CONTINUE
            var dead = Int(self.dead_else(set))
            # (Mojo doesn't check a dead `else`: not there)
            var fall = (
                dead == 0
                and not self.in_const_if(ctx)
                and self.chance(data, MU_GUARD_FALL)
            )
            ctx.depth += 1
            ctx.const_if += dead
            var orelse = self.gen_block(
                data, ctx, 1, False, -1, -1, -1 if fall else exit
            )
            ctx.const_if -= dead
            ctx.depth -= 1
            var scope = self.scope_use(data, ctx, saved, n, nref)
            if scope >= 0:
                orelse.insert(0, scope)
            # back in scope after it (the `else` doesn't fall through)
            for v in range(n, len(saved.names)):
                ctx.push(saved.names[v].copy(), saved.types[v], saved.kinds[v])
                ctx.from_tuple[v] = saved.from_tuple[v]
            for b in range(nref, len(saved.ref_names)):
                ctx.ref_names.append(saved.ref_names[b].copy())
                ctx.ref_var.append(saved.ref_var[b])
                ctx.ref_field.append(saved.ref_field[b])
                ctx.ref_depth.append(saved.ref_depth[b])
                ctx.ref_ro.append(saved.ref_ro[b])
            var st = self.add_stmt(
                Stmt(S_GUARD, -1, -1, -1, set, [], orelse^, "")
            )
            if fall:
                self.mutated = True
                self.marked_stmts.append(st)
            return st
        # S_IFC (the clauses run before either branch: drawn at this depth,
        # their bindings in scope in the first)
        var nref = len(ctx.ref_names)
        var set = self.clause_set(data, ctx, ctx.depth + 1)
        ctx.depth += 1
        var bound = ctx.copy()
        var folded = Int(self.const_clauses(set))
        ctx.const_if += folded
        var then = self.gen_block(data, ctx, 2)
        ctx.const_if -= folded
        ctx.drop_refs(ctx.depth, n)
        ctx.truncate(n)
        var orelse = List[Int]()
        if data.draw(booleans()):
            var dead = Int(self.dead_else(set))
            ctx.const_if += dead
            orelse = self.gen_block(data, ctx, 2)
            ctx.const_if -= dead
        var scope = self.scope_use(data, ctx, bound, n, nref)
        if scope >= 0:
            orelse.insert(0, scope)
        ctx.depth -= 1
        return self.add_stmt(Stmt(S_IFC, -1, -1, -1, set, then^, orelse^, ""))

    def fresh_literals(
        mut self, mut data: ConjectureData, p: Int, mut used: List[Int]
    ) raises:
        """An Int `match` with a negative literal in two cases (`case -1:`
        twice) is taken for exhaustive: the code after it is compiled as
        unreachable (a trap), and so are later cases (modular/modular#7828).
        So the literals of case p are ones no earlier case has (used),
        unless DECL_FUZZ_NO_DUP_CASE_WORKAROUND=1."""
        if getenv("DECL_FUZZ_NO_DUP_CASE_WORKAROUND") != "":
            return
        var kind = self.pats[p].kind
        if kind != PK_LIT and kind != PK_OR:
            return
        var fresh = List[Int]()
        for l in range(len(self.literals)):
            if not has(used, self.literal_values[l]):
                fresh.append(l)
        if len(fresh) < 2:  # (then a wildcard)
            self.pats[p].kind = PK_WILD
            return
        if has(used, self.literal_values[self.pats[p].a]):
            self.pats[p].a = fresh[pick(data, len(fresh))]
        used.append(self.literal_values[self.pats[p].a])
        if kind == PK_OR:
            if has(used, self.literal_values[self.pats[p].b]):
                var rest = List[Int]()
                for l in fresh:
                    if not has(used, self.literal_values[l]):
                        rest.append(l)
                self.pats[p].b = (
                    rest[pick(data, len(rest))] if len(rest)
                    > 0 else self.pats[p].a
                )
            used.append(self.literal_values[self.pats[p].b])

    def scope_use(
        mut self,
        mut data: ConjectureData,
        ctx: Ctx,
        bound: Ctx,
        n: Int,
        nref: Int,
    ) raises -> Int:
        """For a pat_scope mutant, perhaps `_use(bN)` of a name that bound
        (in context bound: its variables from n, its `ref` bindings from
        nref) but is out of scope in ctx; else -1."""
        if not self.wants(MU_PAT_SCOPE) or self.in_const_if(ctx):
            return -1
        var names = List[String]()
        for v in range(n, len(bound.names)):
            names.append(bound.names[v])
        for b in range(nref, len(bound.ref_names)):
            names.append(bound.ref_names[b])
        if len(names) == 0 or not self.chance(data, MU_PAT_SCOPE):
            return -1
        var text = String(MARK, names[pick(data, len(names))])
        var e = self.add(E_LIT, 0, self.int_ty, [], [], text^)
        self.mutated = True
        return self.add_stmt(Stmt(S_USE, -1, e, -1, 0, [], [], ""))

    def match_statement(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        """`match <subject>:` with one to three cases, perhaps guarded, and
        perhaps a last `case _:`. The subject is a variable, a temporary
        struct, or an Int (whose cases are literals, `l1 | l2`, `== e`, or
        a name with a guard)."""
        var vars = self.subject_vars(ctx)
        var structs = List[Int]()
        for t in ctx.pool:
            if self.pattern_ok(t):
                structs.append(t)
        var form = data.draw(integers(0, 2))
        if form == 0 and len(vars) == 0:
            form = 1
        if form == 1 and len(structs) == 0:
            form = 2
        var subj = -1
        var e = -1
        var ty = self.int_ty
        var name = String()
        if form == 0:
            subj = vars[pick(data, len(vars))]
            ctx.touched[subj] = True
            ty = ctx.types[subj]
            name = ctx.names[subj].copy()
        elif form == 1:
            ty = structs[pick(data, len(structs))]
            e = self.rvalue_subject(data, ctx, ty)
        else:
            e = self.rvalue_subject(data, ctx, self.int_ty)
        # (a constant subject: Mojo folds the match, see const_clauses)
        var folded = Int(e >= 0 and self.is_const(e))
        ctx.const_if += folded
        var cases = List[Int]()
        var n = len(ctx.names)
        var n_cases = data.draw(integers(1, 3))
        var covered = False  # (no unreachable cases: see dead_else)
        var used = List[Int]()  # (the literals of an Int's cases)
        for i in range(n_cases + 1):
            var last = i == n_cases
            if covered or (last and data.draw(booleans())):
                break
            ctx.new_statement()
            ctx.depth += 1
            var binds = List[Int]()
            var p: Int
            if last:
                p = self.add_pat(
                    PatNode(PK_WILD, ty, -1, -1, False, "", [], [])
                )
            elif form == 2:
                p = self.sub_pattern(data, ctx, ty, -1, False, 0, True, binds)
                self.fresh_literals(data, p, used)
            else:
                p = self.subject_pattern(data, ctx, ty, form == 0, binds)
            self.clauses.append(Clause(CL_CASE, 0, p, -1, -1, [], ""))
            var set: List[Int] = [len(self.clauses) - 1]
            self.push_binds(ctx, binds, subj, ctx.depth)
            if not last and data.draw(integers(0, 2)) == 0:
                ctx.no_move += 1  # (a guard runs only if the pattern matched)
                set.append(self.bool_clause(data, ctx))
                ctx.no_move -= 1
            covered = len(set) == 1 and self.irrefutable(p)
            self.csets.append(set^)
            var cs = len(self.csets) - 1
            var cfold = Int(self.const_clauses(cs))  # (a constant guard)
            ctx.const_if += cfold
            var body = self.gen_block(data, ctx, 2)
            ctx.const_if -= cfold
            ctx.drop_refs(ctx.depth, n)
            ctx.truncate(n)
            ctx.depth -= 1
            cases.append(
                self.add_stmt(Stmt(S_CASE, -1, -1, -1, cs, body^, [], ""))
            )
        ctx.const_if -= folded
        return self.add_stmt(Stmt(S_MATCH, subj, e, -1, 0, cases^, [], name^))

    def can_try(self, ctx: Ctx) -> Bool:
        """Whether a `try` here could call a raising function."""
        if ctx.depth >= MAX_DEPTH:
            return False
        for f in range(len(self.fns)):
            if self.fns[f].raise_ty != -1 and self.fns[f].rank < ctx.rank:
                return True
        for m in range(len(self.methods)):
            if (
                self.methods[m].raise_ty != -1
                and self.methods[m].rank < ctx.rank
            ):
                return True
        return False

    def try_statement(
        mut self, mut data: ConjectureData, mut ctx: Ctx
    ) raises -> Int:
        """`try:` with handlers for the error types its body raises: typed
        ones (`except Xk __as eN:`, whose bodies can read `eN.code`) in a
        random order, then perhaps `except:` for the rest (always for
        Error). Variables from outside are read-only in the body and the
        handlers (`freeze_base`). An unhandled mutant leaves out a typed
        handler; an unreachable near miss adds one that can't run."""
        var n = len(ctx.names)
        var kinds = ctx.kinds.copy()
        var freeze = ctx.freeze_base
        for v in range(n):
            ctx.kinds[v] = V_READ
        ctx.freeze_base = n
        var outer_raised = ctx.raised.copy()
        ctx.raised = []
        ctx.catching += 1
        ctx.depth += 1
        var body = self.gen_block(data, ctx, 3, False)
        ctx.depth -= 1
        ctx.catching -= 1
        var raised = ctx.raised.copy()
        ctx.raised = outer_raised^
        ctx.truncate(n)
        if len(raised) == 0:
            # (nothing to catch: every handler would be unreachable, and
            # one can't use variables, modular/modular#7812) the statements
            # as a group
            for v in range(n):
                ctx.kinds[v] = kinds[v]
            ctx.freeze_base = freeze
            # (target 1: its locals go out of scope after it)
            return self.add_stmt(Stmt(S_USE, 1, -1, -1, 0, body^, [], ""))
        # which handlers, in which order
        var typed = List[Int]()
        var has_error = False
        for r in raised:
            if r == -2:
                has_error = True
            else:
                typed.insert(pick(data, len(typed) + 1), r)
        var bare = has_error or data.draw(integers(0, 2)) == 0
        if bare and not has_error:
            # (the bare handler catches the ones left out: at least one, or
            # it would be unreachable)
            typed.resize(pick(data, len(typed)), 0)
        var mark = 0
        if (
            not bare
            and len(typed) >= 2
            and self.wants(MU_UNHANDLED)
            and not self.in_const_if(ctx)
            and self.chance(data, MU_UNHANDLED)
        ):
            _ = typed.pop(pick(data, len(typed)))
            mark = 1
            self.mutated = True
        var hts = typed.copy()
        if bare:
            hts.append(-1)
        var unreachable = -1  # (its index in hts)
        if self.wants_near(NR_UNREACHABLE) and self.near_chance(
            data, NR_UNREACHABLE
        ):
            # a type caught before, one not raised, or anything after
            # `except:`
            var t = pick(data, self.n_err)
            if bare:
                hts.append(t)
            elif len(typed) > 0 and data.draw(booleans()):
                hts.append(typed[pick(data, len(typed))])
            else:
                var unraised = List[Int]()
                for k in range(self.n_err):
                    if not has(raised, k):
                        unraised.append(k)
                if len(unraised) == 0:
                    unraised = typed.copy()
                hts.append(unraised[pick(data, len(unraised))])
            unreachable = len(hts) - 1
            self.near_made = True
        var handlers = List[Int]()
        for i in range(len(hts)):
            var t = hts[i]
            var name = String("e", ctx.counter)
            ctx.counter += 1
            ctx.depth += 1
            # (an unreachable handler that uses its binding, or a local
            # variable, is rejected with "use of uninitialized value",
            # modular/modular#7812: its body is `pass`)
            var dead = (
                i == unreachable
                and getenv("DECL_FUZZ_NO_UNREACHABLE_WORKAROUND") == ""
            )
            # (half the bare ones bind the error, `except eN:`: as the
            # type left, if only one is, else as an Error)
            var bound = t < 0 and not dead and data.draw(booleans())
            var bt = t
            if bound:
                var left = List[Int]()
                for r in raised:
                    var caught = False
                    for j in range(i):
                        caught = caught or hts[j] == r
                    if not caught:
                        left.append(r)
                bt = left[0] if len(left) == 1 else -2
            if (t >= 0 and not dead) or bound:
                ctx.push(name.copy(), self.intern(ERR, bt, -1), V_READ)
            var hb = List[Int]()
            if not dead:
                hb = self.gen_block(data, ctx, 2, False)
                if t >= 0 or bound:
                    hb += self.reraise(data, ctx, n, bt, name, hb)
            ctx.depth -= 1
            ctx.truncate(n)
            handlers.append(
                self.add_stmt(
                    Stmt(
                        S_HANDLER,
                        t,
                        -1,
                        Int(bound),
                        Int(i == unreachable),
                        hb^,
                        [],
                        name^,
                    )
                )
            )
        # (with an unreachable handler, the `finally` can't use variables
        # either, modular/modular#7812: none)
        var no_finally = (
            unreachable >= 0
            and getenv("DECL_FUZZ_NO_UNREACHABLE_WORKAROUND") == ""
        )
        handlers += self.try_clauses(data, ctx, n, kinds, body, no_finally)
        for v in range(n):
            ctx.kinds[v] = kinds[v]
        ctx.freeze_base = freeze
        return self.add_stmt(
            Stmt(S_TRY, -1, -1, -1, mark, body^, handlers^, String())
        )

    def reraise(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        slot: Int,
        t: Int,
        name: String,
        hb: List[Int],
    ) raises -> List[Int]:
        """For a third of the handlers binding the error (in slot; of type
        Xt, or Error for t = -2), `raise eN^` at the end, where the error
        goes; for MU_RAISE_TYPE, in a function raising another type. Not
        after an exit."""
        if len(hb) > 0:
            var last = self.stmts[hb[len(hb) - 1]].kind
            if last == S_RETURN or last == S_BREAK or last == S_CONTINUE:
                return []
        var r = t if t >= 0 else -2
        var bad = False
        if not self.raise_ok(ctx, r):
            if not (
                ctx.catching == 0
                and ctx.raise_ty >= 0
                and self.wants(MU_RAISE_TYPE)
                and self.raise_ctx_here(ctx)
                and ctx.in_finally == 0
                and self.chance(data, MU_RAISE_TYPE)
            ):
                return []
            bad = True
            self.mutated = True
        elif data.draw(integers(0, 2)) != 0:
            return []
        elif ctx.catching > 0 and not has(ctx.raised, r):
            ctx.raised.append(r)
        return [
            self.add_stmt(
                Stmt(S_RAISE, slot, -1, Int(bad), r, [], [], name.copy())
            )
        ]

    def try_kind(self) -> Bool:
        """Whether the kind drawn needs `else` and `finally` clauses."""
        return (
            self.mutant == MU_TRY_SCOPE
            or self.mutant == MU_TRY_MOVE
            or self.near == NR_TRY_MOVE
        )

    def try_clauses(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        n: Int,
        kinds: List[Int],
        body: List[Int],
        no_finally: Bool,
    ) raises -> List[Int]:
        """A `try`'s `else` and `finally` clauses, each for a quarter (half
        for the try kinds; no `finally` with no_finally), with the outer
        variables read-only (`kinds` holds what they were). A try_move mutant's `else` moves an owned
        one, which its `finally` uses (a near miss's reinitializes it
        first); a try_scope mutant's `finally` uses a variable the body
        declared."""
        var odds = 1 if self.try_kind() else 3
        var out = List[Int]()
        # (a reference to a value in a `finally` nested in another's is
        # "use of uninitialized value", when both bodies can raise: no
        # `finally` there)
        var nested = (
            ctx.in_finally > 0
            and getenv("DECL_FUZZ_NO_NESTED_FINALLY_WORKAROUND") == ""
        )
        # (in a `deinit self` method, a `return` in the body leaves self
        # uninitialized in the `finally`: none there)
        var deinit = (
            self.deinit_body
            and getenv("DECL_FUZZ_NO_DEINIT_FINALLY_WORKAROUND") == ""
        )
        var can_finally = not nested and not no_finally and not deinit
        var moved = -1
        var moving = (
            (self.wants(MU_TRY_MOVE) or self.wants_near(NR_TRY_MOVE))
            and self.raise_ctx_here(ctx)
            and can_finally
        )
        if data.draw(integers(0, odds)) == 0 or moving:
            var eb = List[Int]()
            if moving:
                var cands = List[Int]()
                for v in range(n):
                    if (
                        kinds[v] == V_OWNED
                        and ctx.live[v]
                        and ctx.types[v] != self.int_ty
                        and not self.is_deinit_self(v)
                    ):
                        cands.append(v)
                var mutant = self.mutant == MU_TRY_MOVE
                if len(cands) > 0 and (
                    self.chance(data, MU_TRY_MOVE) if mutant else (
                        self.near_chance(data, NR_TRY_MOVE)
                    )
                ):
                    moved = cands[pick(data, len(cands))]
                    eb.append(self.move_stmt(ctx, moved))
                    if mutant:
                        self.mutated = True
                    else:
                        # (with a value that can't raise: an error between
                        # the move and the assignment would reach the
                        # `finally` with the variable moved)
                        var exit_catch = ctx.exit_catch
                        ctx.exit_catch = ctx.catching
                        ctx.no_exit += 1
                        eb.append(self.gen_reinit(data, ctx, moved))
                        ctx.no_exit -= 1
                        ctx.exit_catch = exit_catch
                        self.near_made = True
            ctx.depth += 1
            eb += self.gen_block(data, ctx, 2, False)
            ctx.depth -= 1
            ctx.truncate(n)
            out.append(
                self.add_stmt(Stmt(S_HANDLER, H_ELSE, -1, -1, 0, eb^, [], ""))
            )
        var scoped = List[String]()  # (the body's own variables)
        if (
            self.wants(MU_TRY_SCOPE)
            and self.raise_ctx_here(ctx)
            and can_finally
        ):
            for st in body:
                if self.stmts[st].kind == S_VAR:
                    scoped.append(String(self.stmts[st].name.split(":")[0]))
        if can_finally and (
            data.draw(integers(0, odds)) == 0 or moved >= 0 or len(scoped) > 0
        ):
            var fb = List[Int]()
            var use = -1
            if moved >= 0:
                use = self.add(
                    E_VAR, moved, ctx.types[moved], [], [], ctx.names[moved]
                )
                use = self.mark(use) if self.mutant == MU_TRY_MOVE else (
                    self.mark_near(use)
                )
            elif len(scoped) > 0 and self.chance(data, MU_TRY_SCOPE):
                var name = scoped[pick(data, len(scoped))]
                use = self.mark(self.add(E_VAR, -1, self.int_ty, [], [], name))
                self.mutated = True
            if use >= 0:
                fb.append(
                    self.add_stmt(Stmt(S_USE, -1, use, -1, 0, [], [], ""))
                )
            ctx.depth += 1
            ctx.in_finally += 1
            # (one error type may leave it, one its context lets out: with
            # a raising handler, Mojo unifies the types leaving a `try`
            # with a `finally`, and two make an Error)
            var fin_type = ctx.fin_type
            var fin_catch = ctx.fin_catch
            if getenv("DECL_FUZZ_NO_FINALLY_UNIFY_WORKAROUND") == "":
                var ok = List[Int]()
                for r in range(-2, self.n_err):
                    if r != -1 and self.raise_ok(ctx, r):
                        ok.append(r)
                ctx.fin_type = ok[pick(data, len(ok))] if len(ok) > 0 else -1
                ctx.fin_catch = ctx.catching
            fb += self.gen_block(data, ctx, 2, False)
            ctx.fin_type = fin_type
            ctx.fin_catch = fin_catch
            ctx.in_finally -= 1
            ctx.depth -= 1
            ctx.truncate(n)
            out.append(
                self.add_stmt(
                    Stmt(S_HANDLER, H_FINALLY, -1, -1, 0, fb^, [], "")
                )
            )
        return out^

    def gated_call(
        mut self,
        mut data: ConjectureData,
        mut ctx: Ctx,
        ty: Int,
        size: Int,
        pos: Int,
    ) raises -> Int:
        """For MU_WHERE, a call of a gated method on a receiver whose
        condition fails; for NR_WHERE, on one whose condition holds; or -1.
        Of implementations drawn so far, without `mut` arguments."""
        # (not in a dead branch, which Mojo drops before checking
        # constraints, as for moved values)
        var bad = self.wants(MU_WHERE)
        if bad and (self.in_branch(ctx) or self.in_const_if(ctx)):
            return -1
        var recv = List[Int]()
        var ids = List[Int]()
        for r in ctx.pool:
            if self.tkind[r] != STRUCT:
                continue
            var st = self.tid[r]
            if self.structs[st].cond < 0 or not self.structs[st].cond_where:
                continue
            var req = self.structs[st].cond_req
            var holds = self.conforms(self.targ[r], req, ctx.bounds)
            if holds == bad:
                continue
            for m in self.structs[st].impl_methods.copy():
                if (
                    self.is_gated(st, m)
                    and not self.methods[m].is_static
                    and not self.has_mut(m)
                    and self.methods[m].rank < ctx.rank
                    and self.raise_ok(ctx, self.method_raise(m, r))
                    and self.method_fit(m, r, ty, ctx) > -2
                ):
                    recv.append(r)
                    ids.append(m)
        if len(recv) == 0:
            return -1
        if bad:
            if not self.chance(data, MU_WHERE):
                return -1
            self.mutated = True
        elif not self.near_chance(data, NR_WHERE):
            return -1
        var i = pick(data, len(recv))
        var c = Cands(
            [], [], [], [], [], [], [recv[i]], [ids[i]], [], [], [], []
        )
        var e = self.apply_rule(data, ctx, R_METHOD, ty, size, pos, c)
        return self.mark(e) if bad else self.mark_near(e)

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
                return self.mark(self.spell(data, ctx, v, c.atom_fields[i]))
            if mode == A_MOVE:
                ctx.live[v] = False
                ctx.move_depth[v] = ctx.depth
                ctx.touched[v] = True
                return self.add(
                    E_MOVE, v, ty, [], [], String(ctx.names[v], "^")
                )
            ctx.touched[v] = True
            var place = self.spell(data, ctx, v, c.atom_fields[i])
            if mode == A_COPY:
                var text = String(self.exprs[place].text, ".copy()")
                return self.add(E_COPY, 0, ty, [place], [], text^)
            return place

        if rule == R_NEW:  # T-New: the fields are consumed
            var bad = self.bad_type_text(data, ctx, ty)
            var near = False
            if (
                ty == ctx.self_ty
                and self.is_valued(ty)
                and self.near_chance(data, NR_VALUE_EXPR)
            ):
                var exprs: List[String] = [
                    "Self.n + 0",
                    "0 + Self.n",
                    "Self.n * 1",
                    "1 * Self.n",
                    "Self.n - 0",
                    "(Self.n + 2) - 2",
                    "2 + Self.n - 2",
                ]
                bad = String(
                    self.structs[self.tid[ty]].name,
                    "[",
                    exprs[pick(data, len(exprs))],
                    "]",
                )
                near = True
            var fts = self.fields_of(ty)
            var vars = List[Int](length=len(fts), fill=CONV_VAR)
            var kids = self.gen_args(data, ctx, fts, vars, sub, False)
            kids = self.where_copies(kids)
            var text = String(
                self.cty(ty, ctx) if bad == "" else bad,
                "(",
                self.args_text(kids, 0),
                ")",
            )
            var e = self.add(E_NEW, 0, ty, kids^, [], text^)
            if near:
                return self.mark_near(e)
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
            var state = self.mutation_state()
            var x = self.gen_typed(data, ctx, self.int_ty, half, P_READ)
            var y = self.gen_typed(data, ctx, self.int_ty, half, P_READ)
            if (
                ctx.in_finally > 0
                and self.is_const(x)
                and self.is_const(y)
                and getenv("DECL_FUZZ_NO_NESTED_FINALLY_WORKAROUND") == ""
            ):
                # (in a `finally` whose `try` can raise, a reference in the
                # live branch of a constant ternary is "use of uninitialized
                # value": one value instead)
                self.restore_mutation(state)
                return self.gen_typed(data, ctx, ty, half, P_OWNED)
            ctx.no_move += 1
            var t = self.gen_typed(data, ctx, ty, half, P_OWNED)
            var e = self.gen_typed(data, ctx, ty, half, P_OWNED)
            ctx.no_move -= 1
            if (
                self.is_place(t)
                and self.is_place(e)
                and self.exprs[t].text != self.exprs[e].text
                and kind != INT
                and MARK not in self.exprs[e].text
                and getenv("DECL_FUZZ_NO_TERN_PLACE_WORKAROUND") == ""
            ):
                # a ternary of two places, passed read next to a value
                # overlapping one of them, is rejected as aliasing a `mut`
                # argument (modular/modular#7781): copy one
                var text = String(self.exprs[e].text, ".copy()")
                e = self.add(E_COPY, 0, ty, [e], [], text^)
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
            if self.has_accessor(c.field_recv[i], c.field_idx[i]) and data.draw(
                booleans()
            ):
                self.exprs[fe].text = String(
                    self.exprs[recv].text, ".f", c.field_idx[i], "_ref()"
                )
                self.exprs[fe].tys = [1]
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
            var mr = self.method_raise(m, r)
            if not self.raise_ok(ctx, mr):
                # (the raise_ctx mutant's candidate)
                if not self.chance(data, MU_RAISE_CTX):
                    raise Error("STUCK")
                self.mutated = True
                wrong = True
            elif mr != -1 and ctx.catching > 0 and not has(ctx.raised, mr):
                ctx.raised.append(mr)
            if not self.mw_holds(m, r):
                # (the vwhere mutant's candidate: a gated method whose
                # `where` fails for r)
                if not self.chance(data, MU_VWHERE):
                    raise Error("STUCK")
                self.mutated = True
                wrong = True
            elif self.props_by_assert(
                self.methods[m].vwhere, self.targ[r]
            ) and self.near_chance(data, NR_VWHERE):
                name = String(MARK_NEAR, name)
                self.near_made = True
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
            # a generic method's own parameters (`U`, `k`): what the result
            # type fixes, or any allowed one; MU_BOUND: a U that doesn't
            # conform (bad_us holds what's written, if it isn't us)
            var us = List[Int]()
            var bad_us = List[Int]()
            var b = self.methods[m].mbound
            var gm = self.is_generic_method(m)
            var ki = self.k_index(m) - 1  # (k's index in us)
            if gm:
                us = self.method_assign(m, r, ty, ctx)
                for i in range(len(us)):
                    if us[i] < 0:
                        var ok = self.own_choices(m, i, ctx)
                        us[i] = ok[pick(data, len(ok))]
            if ki >= 0 and self.wants(MU_VALUE):
                # another value explicitly: `x.m[k + d](...)`
                if self.chance(data, MU_VALUE):
                    bad_us = us.copy()
                    bad_us[ki] = self.offset(us[ki], data.draw(integers(1, 3)))
                    self.mutated = True
                    wrong = True
            if b >= 0:
                if self.wants(MU_BOUND) or (
                    self.wants(MU_WHERE)
                    and not self.in_branch(ctx)
                    and not self.in_const_if(ctx)
                ):
                    var bad = List[Int]()
                    for t in ctx.pool:
                        if (
                            self.wants(MU_BOUND)
                            and not self.conforms(t, b, ctx.bounds)
                        ) or self.cond_only(t, b, ctx.bounds):
                            bad.append(t)
                    if len(bad) > 0 and self.chance(data, self.mutant):
                        bad_us = us.copy()
                        bad_us[0] = bad[pick(data, len(bad))]
                        self.mutated = True
                        wrong = True
            var mutated_before = self.mutated
            var kids = List[Int]()
            if self.methods[m].self_conv == CONV_MUT:
                kids.append(self.take_place(data, ctx, r, True))
            elif self.methods[m].self_conv == CONV_DEINIT:
                # an owned receiver: `x^`, a copy, or a new value
                kids.append(self.gen(data, ctx, r, sub, P_OWNED))
            else:
                kids.append(self.gen(data, ctx, r, sub, P_READ))
            var params = self.method_params(m, r, us)
            var convs = self.methods[m].convs.copy()
            var mut_call = self.has_mut(m)
            kids += self.gen_args(data, ctx, params, convs, half, mut_call)
            var text = String(self.exprs[kids[0]].text, ".", name)
            if gm:
                # explicit half the time, and always when an argument of
                # another type might change what U is inferred to be; for
                # two, perhaps only U (k is inferred), or k by keyword
                var forced = len(bad_us) > 0 or (
                    self.mutated and not mutated_before
                )
                # MU_OWN2: both, positionally, in the wrong order;
                # NR_OWN2: both by keyword, k first
                var swapped = (
                    len(us) == 2 and not forced and self.chance(data, MU_OWN2)
                )
                var reversed = (
                    len(us) == 2
                    and not forced
                    and not swapped
                    and self.near_chance(data, NR_OWN2)
                )
                if swapped:
                    self.mutated = True
                    wrong = True
                if forced or swapped or reversed or data.draw(booleans()):
                    var xs = bad_us.copy() if len(bad_us) > 0 else us.copy()
                    var written = List[String]()
                    for i in range(len(xs)):
                        if i == ki:
                            written.append(self.val_str(xs[i], ctx.param_names))
                        else:
                            written.append(self.cty(xs[i], ctx))
                    # (with two: both, U alone (k is inferred), `k=` alone,
                    # or both by keyword)
                    var form = 0
                    if len(xs) == 2 and not forced:
                        form = data.draw(integers(0, 3))
                        # (on a struct whose implementation renamed U, a
                        # call names its parameter: no `U=` with the
                        # rename near miss)
                        if form == 3 and self.near == NR_RENAME:
                            form = 0
                    if swapped:
                        text += String("[", written[1], ", ", written[0], "]")
                    elif reversed:
                        text += String(
                            MARK_NEAR,
                            "[k=",
                            written[1],
                            ", U=",
                            written[0],
                            "]",
                        )
                        self.near_made = True
                    elif form == 1:
                        text += String("[", written[0], "]")
                    elif form == 2:
                        text += String("[k=", written[1], "]")
                    elif form == 3:
                        text += String(
                            "[U=", written[0], ", k=", written[1], "]"
                        )
                    else:
                        text += String("[", ", ".join(written), "]")
            text += String("(", self.args_text(kids, 1), ")")
            var e = self.add(E_METHOD, m, ty, kids^, us^, text^)
            return self.mark(e) if wrong else e

        if rule == R_VALN:  # a value parameter
            var t = c.valn[pick(data, len(c.valn))]
            var text = String(self.cty(t, ctx), ".n")
            var ak = self.tkind[self.targ[t]]
            if (ak == PARAM or ak == OFF) and data.draw(booleans()):
                # `Self.n`, `n`, `(n + 1)`
                text = String(
                    "(", self.val_str(self.targ[t], ctx.param_names), ")"
                )
            return self.add(E_VALN, 0, ty, [], [t], text^)

        if rule == R_K:  # an associated constant: τ.K<t>
            var i = pick(data, len(c.k_recv))
            var text = String(self.cty(c.k_recv[i], ctx), ".K", c.k_trait[i])
            return self.add(E_K, c.k_trait[i], ty, [], [c.k_recv[i]], text^)

        # R_CALL: a free or generic function; T-UCast's counterpart is
        # passing a conforming type for a bounded parameter
        var f = c.call_fn[pick(data, len(c.call_fn))]
        var r = self.fns[f].raise_ty
        if r != -1 and ctx.catching > 0 and not has(ctx.raised, r):
            ctx.raised.append(r)
        var targs = List[Int]()
        var n_tp = len(self.fns[f].bounds)
        if n_tp > 0:
            targs = self.call_assignment(f, ty, ctx)
            for i in range(n_tp):
                if targs[i] < 0:
                    var ok = self.targ_choices(ctx, f, i)
                    # (the vwhere near miss wants a value only an assert
                    # gives evidence for)
                    if self.wants_near(NR_VWHERE):
                        var by_assert = List[Int]()
                        for v in ok:
                            if self.vw_by_assert(f, v):
                                by_assert.append(v)
                        if len(by_assert) > 0:
                            ok = by_assert^
                    targs[i] = ok[pick(data, len(ok))]
        # MU_BOUND: a type argument that doesn't conform, (i, type)
        var bad_i = -1
        var bad_t = -1
        if n_tp > 0 and self.wants(MU_BOUND):
            var cands = List[Int]()
            for i in range(n_tp):
                if self.fns[f].bounds[i] < 0:
                    continue
                for t in ctx.pool:
                    if not self.conforms(t, self.fns[f].bounds[i], ctx.bounds):
                        cands.append(i * 1024 + t)
            if len(cands) > 0 and self.chance(data, MU_BOUND):
                var x = cands[pick(data, len(cands))]
                bad_i = x // 1024
                bad_t = x % 1024
                self.mutated = True
        # MU_WHERE: a type argument that would conform only through a
        # conditional conformance whose condition fails, or that fails the
        # function's `where`
        if (
            n_tp > 0
            and self.wants(MU_WHERE)
            and not self.in_branch(ctx)
            and not self.in_const_if(ctx)
        ):
            var cands = List[Int]()
            for i in range(n_tp):
                var b = self.fns[f].bounds[i]
                if b < 0:
                    continue
                var w = self.fns[f].wheres[i]
                for t in ctx.pool:
                    if self.cond_only(t, b, ctx.bounds) or (
                        w >= 0
                        and self.conforms(t, b, ctx.bounds)
                        and not self.conforms(t, w, ctx.bounds)
                    ):
                        cands.append(i * 1024 + t)
            if len(cands) > 0 and self.chance(data, MU_WHERE):
                var x = cands[pick(data, len(cands))]
                bad_i = x // 1024
                bad_t = x % 1024
                self.mutated = True
        # MU_VALUE: another value given explicitly for a value parameter
        if self.wants(MU_VALUE):
            var vs = List[Int]()
            for i in range(n_tp):
                if self.fns[f].bounds[i] < 0:
                    vs.append(i)
            if len(vs) > 0 and self.chance(data, MU_VALUE):
                bad_i = vs[pick(data, len(vs))]
                bad_t = self.offset(targs[bad_i], data.draw(integers(1, 3)))
                self.mutated = True
        # MU_VWHERE: a value argument that breaks the function's `where`
        # (the arguments have the types it makes, so that's the only
        # error; not when the result's type would change); NR_VWHERE: one
        # that only a `comptime assert` gives evidence for
        var vbad = False
        var vnear = False
        var vi = self.vw_fn_index(f)
        if vi >= 0 and len(self.fns[f].vwhere) > 0:
            # (not in a ternary's branch: Mojo doesn't check a `where` in
            # the dead branch of one with a constant condition, like the
            # implicit copies of modular/modular#7770)
            if (
                self.wants(MU_VWHERE)
                and not self.in_branch(ctx)
                and not self.mentions(self.fns[f].ret, vi)
            ):
                var cands = List[Int]()
                var vs = self.tid[self.fns[f].params[vi]]
                for v in self.value_args(ctx, vs):
                    if not self.vw_holds(f, v):
                        cands.append(v)
                if len(cands) > 0 and self.chance(data, MU_VWHERE):
                    targs[vi] = cands[pick(data, len(cands))]
                    vbad = True
                    self.mutated = True
            elif (
                self.wants_near(NR_VWHERE)
                and self.vw_by_assert(f, targs[vi])
                and self.near_chance(data, NR_VWHERE)
            ):
                vnear = True
        var params = self.fns[f].params.copy()
        if n_tp > 0:
            params = self.subst_all(params, targs)
        var convs = self.fns[f].convs.copy()
        var mut_call = has(convs, CONV_MUT)
        var mutated_before = self.mutated
        var kids = self.gen_args(data, ctx, params, convs, half, mut_call)
        # an argument of another type might change what the type
        # arguments are inferred to be, so they're explicit then
        var forced = bad_i >= 0 or (self.mutated and not mutated_before)
        # MU_INFER: a value or type that can't be inferred left out
        var no_infer = False
        var wp = self.fns[f].wparam
        # (only for a value: Mojo matches `V[k + 1]` with `V[n + 1]`, n =
        # k, though not `V[1 + k]`, modular/modular#7816)
        if (
            ((self.noninfer(f) and self.tkind[targs[vi]] == VAL) or wp >= 0)
            and not forced
            and self.chance(data, MU_INFER)
        ):
            no_infer = True
            self.mutated = True
        var text = self.fns[f].name
        var explicit = self.noninfer(f) or wp >= 0
        if (
            n_tp > 0
            and (data.draw(booleans()) or forced or explicit)
            and not no_infer
        ):
            if (
                wp >= 0
                and not forced
                and not self.noninfer(f)
                and data.draw(booleans())
            ):
                # only W, by keyword (the others are inferred)
                text += String(
                    "[",
                    self.fn_names(f)[wp],
                    "=",
                    self.cty(targs[wp], ctx),
                    "]",
                )
            else:
                text += "["
                for i in range(n_tp):
                    if i > 0:
                        text += ", "
                    text += self.targ_str(
                        f, i, bad_t if i == bad_i else targs[i], ctx
                    )
                text += "]"
        text += String("(", self.args_text(kids, 0), ")")
        var e = self.add(E_CALL, f, ty, kids^, targs^, text^)
        if vnear:
            return self.mark_near(e)
        return self.mark(e) if bad_i >= 0 or vbad or no_infer else e

    def targ_str(self, f: Int, i: Int, t: Int, ctx: Ctx) -> String:
        """Type argument i of a call of function f: a type, or a value."""
        if self.fns[f].bounds[i] < 0:
            return self.val_str(t, ctx.param_names)
        return self.cty(t, ctx)

    def bad_type_text(
        mut self, mut data: ConjectureData, ctx: Ctx, ty: Int
    ) raises -> String:
        """For MU_BOUND, ty (a generic struct type) written with a type
        argument that doesn't conform to its bound; otherwise ""."""
        if (
            not self.wants(MU_BOUND)
            or self.tkind[ty] != STRUCT
            or not self.structs[self.tid[ty]].generic
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

    def call_assignment(mut self, f: Int, ty: Int, ctx: Ctx) -> List[Int]:
        """Type arguments making generic function f return ty (-1 where
        free), or [] if there are none."""
        var n_tp = len(self.fns[f].bounds)
        if n_tp == 0:
            return []
        var assign = List[Int]()
        for _ in range(n_tp):
            assign.append(-1)
        self.pend_p = []
        self.pend_t = []
        self.pend_ty = []
        if not self.unify(self.fns[f].ret, ty, assign):
            return []
        # `-> T.E0`: a T whose E0 is the type wanted (the first one; T is
        # inferred from the arguments)
        for j in range(len(self.pend_p)):
            var p = self.pend_p[j]
            var pat = self.pend_t[j]
            var want = self.pend_ty[j]
            if assign[p] >= 0:
                if self.subst_one(pat, p, assign[p]) != want:
                    return []
                continue
            for c in self.targ_choices(ctx, f, p):
                if self.subst_one(pat, p, c) == want:
                    assign[p] = c
                    break
            if assign[p] < 0:
                return []
        for i in range(n_tp):
            var b = self.fns[f].bounds[i]
            if assign[i] >= 0:
                if b >= 0 and not self.conforms(assign[i], b, ctx.bounds):
                    return []
                if b < 0 and not self.vw_holds(f, assign[i]):
                    return []
                var w = self.fns[f].wheres[i]
                if w >= 0 and not self.conforms(assign[i], w, ctx.bounds):
                    return []
            elif len(self.targ_choices(ctx, f, i)) == 0:
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
                raise Error(
                    String(
                        "evaluator: read of a moved variable (",
                        self.exprs[e].text,
                        ")",
                    )
                )
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
            self.stats[STAT_REF] += len(self.exprs[e].tys)
            return self.read_place(e, frame)
        if kind == E_FMOVE:  # (the field is reassigned before any use)
            self.stats[STAT_MOVE] += 1
            return self.read_place(kids[0], frame)
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
            if self.condition(a, kids[0], kids[1], frame, targs):
                return self.eval(kids[2], frame, targs)
            return self.eval(kids[3], frame, targs)
        if kind == E_FIELD:
            self.stats[STAT_REF] += len(self.exprs[e].tys)
            var v = self.eval(kids[0], frame, targs)
            return self.vkids[v][a]
        if kind == E_NEW:
            var ty = self.subst(self.exprs[e].ty, targs)
            var vals = List[Int]()
            var moved = List[Int]()
            for k in kids:
                vals.append(self.eval_arg(k, frame, targs, moved))
            for v in moved:
                frame[v] = -1
            if self.tkind[ty] == RES:
                self.stats[STAT_RES] += 1
                return self.new_value(-2, 0, vals^)
            return self.new_value(self.tid[ty], 0, vals^)
        if kind == E_METHOD:
            if self.tkind[self.exprs[kids[0]].ty] == ASSOC:
                self.stats[STAT_ASSOC] += 1
                if self.is_nested(self.exprs[kids[0]].ty):
                    self.stats[STAT_NESTED] += 1
            var recv_ty = self.subst(self.exprs[kids[0]].ty, targs)
            var convs: List[Int] = [self.methods[a].self_conv]
            if convs[0] == CONV_DEINIT:
                self.stats[STAT_DEINIT] += 1
                convs[0] = CONV_VAR  # (the receiver is passed owned)
            convs += self.methods[a].convs.copy()
            var m_targs = self.subst_all(self.exprs[e].tys.copy(), targs)
            if len(m_targs) > 0:
                self.stats[STAT_GENERIC_METHOD] += 1
                if self.methods[a].mvalue >= 0:
                    self.stats[STAT_VALUE_CALL] += 1
                if self.is_both(a):
                    self.stats[STAT_OWN2] += 1
            return self.call(a, -1, recv_ty, kids, convs, frame, targs, m_targs)
        if kind == E_STATIC:
            if self.tkind[self.exprs[e].tys[0]] == ASSOC:
                self.stats[STAT_ASSOC] += 1
                if self.is_nested(self.exprs[e].tys[0]):
                    self.stats[STAT_NESTED] += 1
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return self.call(a, -1, ty, kids, [CONV_READ], frame, targs, [])
        if kind == E_VALN:
            self.stats[STAT_VALUE] += 1
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return self.new_int(self.tid[self.targ[ty]])
        if kind == E_K:
            self.stats[STAT_K] += 1
            if self.tkind[self.exprs[e].tys[0]] == ASSOC:
                self.stats[STAT_ASSOC] += 1
                if self.is_nested(self.exprs[e].tys[0]):
                    self.stats[STAT_NESTED] += 1
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return self.new_int(self.k_value(ty, a))
        # E_CALL
        if len(self.fns[a].bounds) > 0:
            self.stats[STAT_GENERIC] += 1
        if has(self.fns[a].bounds, -1):
            self.stats[STAT_VALUE_CALL] += 1
        for w in self.fns[a].wheres:
            if w >= 0:
                self.stats[STAT_WHERE] += 1
                break
        if len(self.fns[a].vwhere) > 0:
            self.stats[STAT_VWHERE] += 1
        var f_targs = self.subst_all(self.exprs[e].tys.copy(), targs)
        var convs = self.fns[a].convs.copy()
        return self.call(-1, a, -1, kids, convs, frame, targs, f_targs)

    def eval_arg(
        mut self,
        e: Int,
        mut frame: List[Int],
        targs: List[Int],
        mut moved: List[Int],
    ) raises -> Int:
        """An argument of a call: `x^` moves x at the call, after the other
        arguments are evaluated (they may use x), so x goes on `moved`."""
        if self.exprs[e].kind != E_MOVE:
            return self.eval(e, frame, targs)
        self.stats[STAT_MOVE] += 1
        var a = self.exprs[e].a
        if frame[a] < 0:
            raise Error("evaluator: move of a moved variable")
        moved.append(a)
        return frame[a]

    def condition(
        mut self,
        op: Int,
        l: Int,
        r: Int,
        mut frame: List[Int],
        targs: List[Int],
    ) raises -> Bool:
        """The comparison `l op r`. Mojo computes an expression of literals
        exactly (IntLiteral) and truncates it only when it becomes an Int,
        which wrapping at each step matches, except when both sides of a
        comparison are such expressions: then it compares exact values.
        Raises LITERAL when the result is uncertain: an exact value beyond
        Int128, or an associated constant that changes the answer (one on
        a concrete struct is a literal, one on a type parameter an Int)."""
        var x = self.vint[self.eval(l, frame, targs)]
        var y = self.vint[self.eval(r, frame, targs)]
        var wrapped = self.compare(op, x, y)
        if not (self.literal_expr(l) and self.literal_expr(r)):
            return wrapped
        var uses_k = False
        var ex = self.exact(l, targs, uses_k)
        var ey = self.exact(r, targs, uses_k)
        var exact: Bool
        if op == 0:
            exact = ex < ey
        else:
            exact = ex == ey if op == 1 else ex != ey
        if uses_k and exact != wrapped:
            raise Error("LITERAL")
        return exact

    def literal_expr(self, e: Int) -> Bool:
        """Whether e is built from literals, the arithmetic operators and
        associated constants of structs (not of type parameters)."""
        ref x = self.exprs[e]
        if x.kind == E_LIT:
            return True
        if x.kind == E_K:
            var k = self.tkind[x.tys[0]]
            return k != PARAM and k != ASSOC
        if x.kind != E_BIN:
            return False
        return self.literal_expr(x.kids[0]) and self.literal_expr(x.kids[1])

    def exact(
        mut self, e: Int, targs: List[Int], mut uses_k: Bool
    ) raises -> Int128:
        """The exact value of a literal_expr (LITERAL beyond Int128)."""
        var kind = self.exprs[e].kind
        var a = self.exprs[e].a
        if kind == E_LIT:
            return Int128(a)
        if kind == E_K:
            uses_k = True
            var ty = self.subst(self.exprs[e].tys[0], targs)
            return Int128(self.k_value(ty, a))
        var l = self.exact(self.exprs[e].kids[0], targs, uses_k)
        var r = self.exact(self.exprs[e].kids[1], targs, uses_k)
        comptime LIM = Int128(1) << 100
        if l >= LIM or l <= -LIM or r >= LIM or r <= -LIM:
            raise Error("LITERAL")
        if a == 2:  # *
            comptime HALF = Int128(1) << 63
            if l >= HALF or l < -HALF or r >= HALF or r < -HALF:
                raise Error("LITERAL")
            return l * r
        if a == 0:
            return l + r
        if a == 1:
            return l - r
        if a == 3:
            return l & r
        if a == 4:
            return l | r
        return l ^ r

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
        """Calls method m (receiver type recv_ty) or function f, with type
        arguments f_targs (a generic method's U): evaluates the arguments
        in order (in the caller's targs), runs the body, then writes the
        `mut` ones back."""
        var callee = List[Int]()
        var has_mut = False
        var moved = List[Int]()
        for i in range(len(args)):
            if convs[i] == CONV_MUT:
                self.stats[STAT_REF] += len(self.exprs[args[i]].tys)
                callee.append(self.read_place(args[i], frame))
                has_mut = True
            else:
                callee.append(self.eval_arg(args[i], frame, targs, moved))
        for v in moved:
            frame[v] = -1
        var result: Int
        try:
            if f >= 0:
                result = self.run_body(self.fns[f].body, callee, f_targs)
            else:
                result = self.call_method(m, recv_ty, callee, f_targs)
        except err:
            # (`mut` arguments are references: what the callee did to them
            # before it raised stays)
            if String(err) == "RAISE" and has_mut:
                for i in range(len(args)):
                    if convs[i] == CONV_MUT:
                        self.write_place(args[i], callee[i], frame)
            if String(err) == "RAISE" and f >= 0 and self.fns[f].raise_ty == -2:
                # (out of a function that `raises`, the error is an Error:
                # only `except:` catches it)
                self.err_type = -2
            raise err^
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
            if self.exec(s, frame, targs) == SIG_RETURN:
                return self.ret_value
        return self.eval(self.bodies[b].ret, frame, targs)

    def exec_block(
        mut self, stmts: List[Int], mut frame: List[Int], targs: List[Int]
    ) raises -> Int:
        """What the block did: SIG_NONE, or the SIG_* of the statement that
        ended it (a return's value is in ret_value)."""
        var n = len(frame)
        var sig = SIG_NONE
        for s in stmts:
            sig = self.exec(s, frame, targs)
            if sig != SIG_NONE:
                break
        while len(frame) > n:
            _ = frame.pop()
        return sig

    def match_pat(
        mut self, p: Int, val: Int, mut frame: List[Int], targs: List[Int]
    ) raises -> Bool:
        """Whether the value val matches pattern p; each binding that adds
        a variable adds its value to the frame."""
        var node = self.pats[p].copy()
        if node.kind == PK_WILD:
            return True
        if node.kind == PK_BIND or node.kind == PK_VAR:
            if node.push:
                frame.append(val)
            return True
        if node.kind == PK_LIT:
            return self.vint[val] == self.literal_values[node.a]
        if node.kind == PK_OR:
            var x = self.vint[val]
            return (
                x == self.literal_values[node.a]
                or x == self.literal_values[node.b]
            )
        if node.kind == PK_EQ:
            var y = self.vint[self.eval(node.a, frame, targs)]
            return self.vint[val] == y
        # PK_STRUCT (fields) or PK_TUPLE (elements)
        for i in range(len(node.kids)):
            var f = node.fields[i] if node.kind == PK_STRUCT else i
            if not self.match_pat(
                node.kids[i], self.vkids[val][f], frame, targs
            ):
                return False
        return True

    def run_clauses(
        mut self,
        cs: Int,
        mut frame: List[Int],
        targs: List[Int],
        subject: Int = -1,
    ) raises -> Bool:
        """Whether the clauses of set cs all hold, left to right (a
        `match`'s case against its subject's value); the bindings of those
        that held are on the frame."""
        for c in self.csets[cs].copy():
            var cl = self.clauses[c].copy()
            if cl.kind == CL_BOOL:
                if not self.condition(cl.op, cl.l, cl.r, frame, targs):
                    return False
                continue
            var val = subject
            if cl.subj >= 0:
                val = frame[cl.subj]
                if val < 0:
                    raise Error("evaluator: match of a moved variable")
            elif len(cl.sexprs) > 0:
                var moved = List[Int]()
                var vals = List[Int]()
                for e in cl.sexprs:
                    vals.append(self.eval_arg(e, frame, targs, moved))
                for v in moved:
                    frame[v] = -1
                if self.pats[cl.l].kind == PK_TUPLE:
                    val = self.new_value(-5, 0, vals^)
                else:
                    val = vals[0]
            if not self.match_pat(cl.l, val, frame, targs):
                return False
            self.stats[STAT_PATTERN] += 1
        return True

    def try_part(
        mut self, s: Int, mut frame: List[Int], targs: List[Int]
    ) raises -> Int:
        """A `try` statement s without its `finally`: the body, then the
        first handler for the error's type, with it bound (an error from
        the handler goes on); or, if the body finished without an exit,
        the `else` clause (likewise)."""
        var n = len(frame)
        var sig = SIG_NONE
        var finished = False
        try:
            sig = self.exec_block(self.stmts[s].body.copy(), frame, targs)
            finished = True
        except err:
            if String(err) != "RAISE":
                raise err^
        if finished:
            if sig != SIG_NONE:
                return sig
            for h in self.stmts[s].orelse.copy():
                if self.stmts[h].target == H_ELSE:
                    self.stats[STAT_ELSE] += 1
                    return self.exec_block(
                        self.stmts[h].body.copy(), frame, targs
                    )
            return SIG_NONE
        # (the try body's locals are gone)
        while len(frame) > n:
            _ = frame.pop()
        var t = self.err_type
        var v = self.err_value
        for h in self.stmts[s].orelse.copy():
            var ht = self.stmts[h].target
            if ht != t and ht != -1:
                continue
            self.stats[STAT_CATCH] += 1
            if ht >= 0 or self.stmts[h].e2 == 1:
                frame.append(v)
            var hsig = self.exec_block(self.stmts[h].body.copy(), frame, targs)
            while len(frame) > n:
                _ = frame.pop()
            return hsig
        raise Error("evaluator: an uncaught error type in a try")

    def exec(
        mut self, s: Int, mut frame: List[Int], targs: List[Int]
    ) raises -> Int:
        """What s did: SIG_NONE, SIG_RETURN (the value is in ret_value),
        SIG_BREAK or SIG_CONTINUE."""
        self.steps += 1
        if self.steps > STEP_LIMIT:
            raise Error("STEP_LIMIT")
        var kind = self.stmts[s].kind
        var e = self.stmts[s].e
        if kind == S_VAR:
            # (`var x: T` starts moved)
            frame.append(self.eval(e, frame, targs) if e >= 0 else -1)
        elif kind == S_ASSIGN:
            self.stats[STAT_ASSIGN] += 1
            self.stats[STAT_REF] += len(self.exprs[self.stmts[s].target].tys)
            var v = self.eval(e, frame, targs)
            self.write_place(self.stmts[s].target, v, frame)
        elif kind == S_EXPR:
            if self.exprs[e].kind == E_MOVE:  # `_ = x^` keeps x alive
                self.stats[STAT_MOVE] += 1
                return SIG_NONE
            _ = self.eval(e, frame, targs)
        elif kind == S_USE:
            var n = len(frame)
            for st in self.stmts[s].body.copy():
                var sig = self.exec(st, frame, targs)
                if sig != SIG_NONE:
                    return sig
            if self.stmts[s].target == 1:  # (a try body with nothing to catch)
                while len(frame) > n:
                    _ = frame.pop()
        elif kind == S_RETURN:
            self.stats[STAT_RETURN] += 1
            self.ret_value = self.eval(e, frame, targs)
            return SIG_RETURN
        elif kind == S_REF:  # (another spelling of a place)
            self.stats[STAT_REF] += 1
        elif kind == S_RAISE:
            self.stats[STAT_RAISE] += 1
            var slot = self.stmts[s].target
            if slot >= 0:  # `raise eN^`: the handler's error, as its type
                self.stats[STAT_RERAISE] += 1
                self.err_type = self.stmts[s].a
                self.err_value = frame[slot]
                raise Error("RAISE")
            var code = self.eval(e, frame, targs)
            var kids: List[Int] = [code]
            if self.stmts[s].e2 >= 0:  # (X2's value)
                self.stats[STAT_CARRY] += 1
                var moved = List[Int]()
                kids.append(
                    self.eval_arg(self.stmts[s].e2, frame, targs, moved)
                )
                for v in moved:
                    frame[v] = -1
            self.err_type = self.stmts[s].a
            self.err_value = self.new_value(-3, 0, kids^)
            raise Error("RAISE")
        elif kind == S_TRY:
            var n = len(frame)
            var fin = -1
            for h in self.stmts[s].orelse:
                if self.stmts[h].target == H_FINALLY:
                    fin = h
            var sig: Int
            try:
                sig = self.try_part(s, frame, targs)
            except err:
                if fin < 0 or String(err) != "RAISE":
                    raise err^
                # (`finally` runs, then the error goes on; an exit in it
                # drops the error)
                while len(frame) > n:
                    _ = frame.pop()
                var t = self.err_type
                var v = self.err_value
                self.stats[STAT_FINALLY] += 1
                var fsig = self.exec_block(
                    self.stmts[fin].body.copy(), frame, targs
                )
                if fsig != SIG_NONE:
                    return fsig
                self.err_type = t
                self.err_value = v
                raise err^
            while len(frame) > n:
                _ = frame.pop()
            if fin >= 0:
                # (a pending return's value survives calls in it)
                var ret = self.ret_value
                self.stats[STAT_FINALLY] += 1
                var fsig = self.exec_block(
                    self.stmts[fin].body.copy(), frame, targs
                )
                if fsig != SIG_NONE:
                    return fsig
                self.ret_value = ret
            return sig
        elif kind == S_BREAK:
            self.stats[STAT_BREAK] += 1
            return SIG_BREAK
        elif kind == S_CONTINUE:
            self.stats[STAT_BREAK] += 1
            return SIG_CONTINUE
        elif kind == S_CIF:
            self.stats[STAT_CIF] += 1
            var key = self.stmts[s].a
            var k = key % 4096 - 2048
            var rest = key // 4096
            var c = rest % 4096 - 2048
            var p = rest // 4096 // 2
            var ge = (rest // 4096) % 2 == 1
            var n = self.tid[targs[p]]
            if Self.prop_holds(n, Prop(c, ge, k, 0)):
                return self.exec_block(self.stmts[s].body.copy(), frame, targs)
            return self.exec_block(self.stmts[s].orelse.copy(), frame, targs)
        elif kind == S_MATCH:
            self.stats[STAT_MATCH] += 1
            var val: Int
            if self.stmts[s].target >= 0:
                val = frame[self.stmts[s].target]
                if val < 0:
                    raise Error("evaluator: match of a moved variable")
            else:
                var moved = List[Int]()
                val = self.eval_arg(e, frame, targs, moved)
                for v in moved:
                    frame[v] = -1
            for c in self.stmts[s].body.copy():
                var n = len(frame)
                if self.run_clauses(self.stmts[c].a, frame, targs, val):
                    var sig = self.exec_block(
                        self.stmts[c].body.copy(), frame, targs
                    )
                    while len(frame) > n:
                        _ = frame.pop()
                    return sig
                while len(frame) > n:
                    _ = frame.pop()
        elif kind == S_IFC:
            self.stats[STAT_MATCH] += 1
            var n = len(frame)
            if self.run_clauses(self.stmts[s].a, frame, targs):
                var sig = self.exec_block(
                    self.stmts[s].body.copy(), frame, targs
                )
                while len(frame) > n:
                    _ = frame.pop()
                return sig
            while len(frame) > n:
                _ = frame.pop()
            return self.exec_block(self.stmts[s].orelse.copy(), frame, targs)
        elif kind == S_GUARD or kind == S_DESTR:
            self.stats[STAT_MATCH] += Int(kind == S_GUARD)
            var n = len(frame)
            if self.run_clauses(self.stmts[s].a, frame, targs):
                return SIG_NONE  # (the bindings stay on the frame)
            if kind == S_DESTR:
                raise Error("evaluator: a destructuring that didn't match")
            while len(frame) > n:
                _ = frame.pop()
            self.stats[STAT_GUARD] += 1
            var sig = self.exec_block(self.stmts[s].orelse.copy(), frame, targs)
            if sig == SIG_NONE:
                raise Error("evaluator: a guard's else fell through")
            return sig
        elif kind == S_IF:
            if self.condition(
                self.stmts[s].a, e, self.stmts[s].e2, frame, targs
            ):
                return self.exec_block(self.stmts[s].body.copy(), frame, targs)
            return self.exec_block(self.stmts[s].orelse.copy(), frame, targs)
        else:
            var body = self.stmts[s].body.copy()
            # (a `while` loop's counter is incremented first)
            var first = 1 if self.stmts[s].target == 1 else 0
            for i in range(self.stmts[s].a):
                self.stats[STAT_LOOP] += 1
                frame.append(self.new_int(i + first))
                var sig = self.exec_block(body, frame, targs)
                _ = frame.pop()
                if sig == SIG_RETURN:
                    return SIG_RETURN
                if sig == SIG_BREAK:
                    break
        return SIG_NONE

    def call_method(
        mut self,
        m: Int,
        recv_ty: Int,
        mut frame: List[Int],
        m_targs: List[Int] = [],
    ) raises -> Int:
        """Static dispatch on the receiver's type, resolved: the struct's
        own body, its implementation, or the trait's default. m_targs is
        a generic method's [U]."""
        if self.tkind[recv_ty] != STRUCT:
            raise Error("evaluator: receiver type not resolved")
        var s = self.tid[recv_ty]
        var targs = List[Int]()
        if self.structs[s].generic or self.structs[s].valued:
            targs.append(self.targ[recv_ty])
        if len(m_targs) > 0:
            if len(targs) == 0:
                targs.append(self.int_ty)  # (PARAM 0 isn't used)
            targs += m_targs.copy()
        if self.methods[m].struct_id >= 0:
            self.stats[STAT_OWN] += 1
            return self.run_raising(
                self.methods[m].body, frame, targs, self.methods[m].raise_ty
            )
        if self.methods[m].is_static:
            self.stats[STAT_STATIC] += 1
        var i = index_of(self.structs[s].impl_methods, m)
        if i >= 0 and self.is_gated(s, m):
            self.stats[STAT_WHERE] += 1
        if i >= 0:
            self.stats[
                STAT_OVERRIDE if self.methods[m].has_default else STAT_REQUIRED
            ] += 1
            return self.run_raising(
                self.structs[s].impl_bodies[i],
                frame,
                targs,
                self.impl_raise(s, m),
            )
        self.stats[STAT_DEFAULT] += 1
        var d_targs: List[Int] = [recv_ty]
        d_targs += m_targs.copy()
        return self.run_raising(
            self.methods[m].body, frame, d_targs, self.methods[m].raise_ty
        )

    def run_raising(
        mut self, b: Int, mut frame: List[Int], targs: List[Int], r: Int
    ) raises -> Int:
        """Runs a method's body b, which raises r (FnDecl.raise_ty): an
        error leaving a `raises` one is an Error."""
        try:
            return self.run_body(b, frame, targs)
        except err:
            if String(err) == "RAISE":
                self.stats[STAT_RAISING_METHOD] += 1
                if r == -2:
                    self.err_type = -2
            raise err^

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
        elif source == -2:  # `Self.n + v`
            self.stats[STAT_VALUE] += 1
            v += self.tid[self.targ[ty]]
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

    def pat_text(self, p: Int) -> String:
        ref node = self.pats[p]
        if node.kind == PK_WILD:
            return "_"
        if node.kind == PK_BIND:
            return node.name.copy()
        if node.kind == PK_VAR:
            return String("var ", node.name)
        if node.kind == PK_LIT:
            return self.literals[node.a].copy()
        if node.kind == PK_OR:
            return String(self.literals[node.a], " | ", self.literals[node.b])
        if node.kind == PK_EQ:
            return String("== ", self.exprs[node.a].text)
        var parts = List[String]()
        for i in range(len(node.kids)):
            var kid = self.pat_text(node.kids[i])
            if node.kind == PK_STRUCT:
                # (`f= == e`: `f=== e` doesn't parse)
                var eq = " " if self.pats[node.kids[i]].kind == PK_EQ else ""
                var field = self.field_name(node.ty, node.fields[i])
                if node.b == -7 and i == 0:  # (a pat_field mutant)
                    field = "z"
                kid = String(field, "=", eq, kid)
            parts.append(kid^)
        var inner = String(", ").join(parts)
        if node.kind == PK_STRUCT:
            return String(node.name, "(", inner, ")")
        return String("(", inner, ")")

    def bool_text(self, c: Int) -> String:
        var ops = materialize[CMP_OPS]()
        ref cl = self.clauses[c]
        return String(
            self.exprs[cl.l].text, " ", ops[cl.op], " ", self.exprs[cl.r].text
        )

    def clauses_text(self, cs: Int) -> String:
        """The clauses of set cs, separated by `; `."""
        var parts = List[String]()
        for c in self.csets[cs]:
            ref cl = self.clauses[c]
            if cl.kind == CL_BOOL:
                parts.append(self.bool_text(c))
                continue
            var text = String("case ", self.pat_text(cl.l))
            if cl.subj >= 0:
                text += String(" = ", cl.text)
            elif len(cl.sexprs) > 0:
                var es = List[String]()
                for e in cl.sexprs:
                    es.append(self.exprs[e].text)
                var subject = String(", ").join(es)
                if self.pats[cl.l].kind == PK_TUPLE:
                    subject = String("(", subject, ")")
                text += String(" = ", subject)
            parts.append(text^)
        return String("; ").join(parts)

    def stmt_lines(self, st: Int, indent: String) -> String:
        ref s = self.stmts[st]
        if s.kind == S_VAR and s.e < 0:
            return String(indent, "var ", s.name, "\n")
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
        if s.kind == S_RETURN:
            var died = String(indent, "_died()\n") if s.a == 1 else String()
            return String(died, indent, "return ", self.exprs[s.e].text, "\n")
        if s.kind == S_REF:
            return String(
                indent, "ref ", s.name, " = ", self.exprs[s.e].text, "\n"
            )
        if s.kind == S_RAISE:
            if s.target >= 0:  # (a re-raise; e2 = 1 for the mutant)
                return String(
                    indent,
                    "raise ",
                    s.name,
                    "^",
                    MARK if s.e2 == 1 else "",
                    "\n",
                )
            var val = String()
            if s.e2 >= 0:
                val = String(", ", self.exprs[s.e2].text)
            return String(
                indent, "raise X", s.a, "(", self.exprs[s.e].text, val, ")\n"
            )
        if s.kind == S_BREAK:
            return String(indent, "break\n")
        if s.kind == S_CONTINUE:
            return String(indent, "continue\n")
        if s.kind == S_USE:
            if s.e >= 0:
                return String(indent, "_use(", self.exprs[s.e].text, ")\n")
            var group = String()
            for st in s.body:
                group += self.stmt_text(st, indent)
            if len(s.body) == 0:
                # (an empty `try` body as a group; not `pass`, which a trait
                # method's default body can't have)
                group = String(indent, "_ = 0\n")
            return group^
        if s.kind == S_DESTR:
            ref cl = self.clauses[self.csets[s.a][0]]
            var names = List[String]()
            for k in self.pats[cl.l].kids:
                names.append(self.pats[k].name)
            var es = List[String]()
            for e in cl.sexprs:
                es.append(self.exprs[e].text)
            return String(
                indent,
                "var (",
                String(", ").join(names),
                ") = (",
                String(", ").join(es),
                ")\n",
            )
        var inner = String(indent, "    ")
        if s.kind == S_MATCH:
            var subject = (
                s.name.copy() if s.target >= 0 else self.exprs[s.e].text.copy()
            )
            var text = String(indent, "match ", subject, ":\n")
            for c in s.body:
                ref set = self.csets[self.stmts[c].a]
                var head = String(
                    "case ", self.pat_text(self.clauses[set[0]].l)
                )
                if len(set) > 1:  # (a guard)
                    head += String(" if ", self.bool_text(set[1]))
                text += String(inner, head, ":\n")
                text += self.block_text(
                    self.stmts[c].body, String(inner, "    ")
                )
            return text^
        if s.kind == S_IFC:
            var text = String(indent, "if ", self.clauses_text(s.a), ":\n")
            text += self.block_text(s.body, inner)
            if len(s.orelse) > 0:
                text += String(indent, "else:\n")
                text += self.block_text(s.orelse, inner)
            return text^
        if s.kind == S_GUARD:
            var text = String(
                indent, "guard ", self.clauses_text(s.a), " else:\n"
            )
            text += self.block_text(s.orelse, inner)
            return text^
        if s.kind == S_TRY:
            var text = String(indent, "try:", MARK if s.a == 1 else "", "\n")
            text += self.block_text(s.body, inner)
            for h in s.orelse:
                ref hs = self.stmts[h]
                var mark = MARK_NEAR if hs.a == 1 else ""
                if hs.target == H_ELSE:
                    text += String(indent, "else:\n")
                elif hs.target == H_FINALLY:
                    text += String(indent, "finally:\n")
                elif hs.target >= 0:
                    text += String(
                        indent,
                        "except X",
                        hs.target,
                        " __as ",
                        hs.name,
                        ":",
                        mark,
                        "\n",
                    )
                elif hs.e2 == 1:
                    text += String(indent, "except ", hs.name, ":", mark, "\n")
                else:
                    text += String(indent, "except:", mark, "\n")
                text += self.block_text(hs.body, inner)
            return text^
        if s.kind == S_CIF:
            var text = String(indent, "comptime if ", s.name, ":\n")
            text += self.block_text(s.body, inner)
            if len(s.orelse) > 0:
                text += String(indent, "else:\n")
                text += self.block_text(s.orelse, inner)
            return text^
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
        if s.target == 1:
            var text = String(indent, "var ", s.name, " = 0\n")
            text += String(indent, "while ", s.name, " < ", s.a, ":\n")
            text += String(inner, s.name, " = ", s.name, " + 1\n")
            for st in s.body:
                text += self.stmt_text(st, inner)
            return text^
        var text = String(indent, "for ", s.name, " in range(", s.a, "):\n")
        text += self.block_text(s.body, inner)
        return text^

    def body_text(self, b: Int, indent: String) -> String:
        ref body = self.bodies[b]
        var s = String()
        for st in body.stmts:
            s += self.stmt_text(st, indent)
        if body.died:
            s += String(indent, "_died()\n")
        s += String(indent, "return ", self.exprs[body.ret].text, "\n")
        return s^

    def sig_text(
        self,
        m: Int,
        params: List[Int],
        ret: Int,
        names: List[String],
        self_print: Int,
        where_clause: String = "",
        raise_ty: Int = -9,
    ) -> String:
        """Method m's signature; it raises raise_ty (-9: as declared)."""
        if self.methods[m].is_static:
            return String(
                "    @staticmethod\n    def ",
                self.methods[m].name,
                "(x: Int) -> ",
                self.ty_str(ret, names, self_print),
                where_clause,
                ":\n",
            )
        var prefixes = materialize[CONV_PREFIX]()
        var s = String("    def ", self.methods[m].name)
        var renamed = False
        if self.is_generic_method(m):
            var u = names[1] if len(names) > 1 else String("U")
            renamed = u != "U" and self.methods[m].mbound >= 0
            if self.is_both(m):
                s += String(
                    "[",
                    u,
                    ": Tr",
                    self.methods[m].mbound,
                    ", ",
                    names[2],
                    ": Int]",
                )
            elif self.methods[m].mvalue >= 0:
                s += String("[", u, ": Int]")
            else:
                s += String("[", u, ": Tr", self.methods[m].mbound, "]")
        s += String("(", prefixes[self.methods[m].self_conv], "self")
        for i in range(len(params)):
            s += String(
                ", ",
                prefixes[self.methods[m].convs[i]],
                "p",
                i,
                ": ",
                self.ty_str(params[i], names, self_print),
            )
        var r = self.methods[m].raise_ty if raise_ty == -9 else raise_ty
        s += String(
            ")",
            raises_text(r),
            " -> ",
            self.ty_str(ret, names, self_print),
            where_clause,
        )
        s += ":"
        if renamed:
            s += MARK_NEAR
        s += "\n"
        return s^

    def counted_text(self, st: Int, names: List[String]) -> String:
        """A counted struct's field-wise `__init__`, copy constructor (if
        `Copyable`) and `__deinit__`."""
        ref fields = self.structs[st].fields
        var s = String("\n    def __init__(out self")
        for f in range(len(fields)):
            s += String(", var f", f, ": ", self.ty_str(fields[f], names, -1))
        s += "):\n"
        for f in range(len(fields)):
            s += String("        self.f", f, " = f", f, "^\n")
        s += "        _born()\n"
        if self.structs[st].cap == CAP_C:
            s += "\n    def __init__(out self, *, copy: Self):\n"
            for f in range(len(fields)):
                var dot = "" if fields[f] == self.int_ty else ".copy()"
                s += String("        self.f", f, " = copy.f", f, dot, "\n")
            s += "        _born()\n"
        s += "\n    def __deinit__(deinit self):\n        _died()\n\n"
        return s^

    def declarations_text(mut self) -> String:
        var s = String()
        if self.exceptions:
            for k in range(N_ERR):
                s += String(
                    "struct X",
                    k,
                    "(Copyable, Writable):\n    var code: Int\n\n",
                    "    def __init__(out self, code: Int):\n",
                    "        self.code = code\n        _born()\n\n",
                    "    def __init__(out self, *, copy: Self):\n",
                    "        self.code = copy.code\n        _born()\n\n",
                    "    def __deinit__(deinit self):\n        _died()\n\n\n",
                )
            if self.carry_ty >= 0:
                # (Writable by hand: `val`'s type isn't)
                var t = self.ty_str(self.carry_ty, [], -1)
                s += String(
                    "struct X",
                    N_ERR,
                    "(Copyable, Writable):\n    var code: Int\n",
                    "    var val: ",
                    t,
                    "\n\n    def __init__(out self, code: Int, var val: ",
                    t,
                    "):\n",
                    "        self.code = code\n        self.val = val^\n",
                    "        _born()\n\n",
                    "    def __init__(out self, *, copy: Self):\n",
                    "        self.code = copy.code\n",
                    "        self.val = copy.val.copy()\n        _born()\n\n",
                    "    def write_to(self, mut writer: Some[Writer]):\n",
                    '        writer.write("X',
                    N_ERR,
                    '(", self.code, ")")\n\n',
                    "    def __deinit__(deinit self):\n        _died()\n\n\n",
                )
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
            if self.traits[t].assoc >= 0:
                s += String(
                    "    comptime E", t, ": Tr", self.traits[t].assoc, "\n"
                )
            for m in self.traits[t].methods:
                s += "\n"
                s += self.sig_text(
                    m,
                    self.methods[m].params,
                    self.methods[m].ret,
                    self.trait_names(m),
                    -1,
                )
                if self.methods[m].body >= 0:
                    s += self.body_text(self.methods[m].body, "        ")
                else:
                    s += "        ...\n"
            s += "\n\n"
        for st in range(len(self.structs)):
            var generic = self.structs[st].generic
            var valued = self.structs[st].valued
            var names = ["Self.T"] if generic else (
                ["Self.n"] if valued else List[String]()
            )
            var self_ty = self.self_type(st)
            var marked = st == self.mark_struct
            var counted = self.is_counted(st)
            var bindings = String()
            for i in range(len(self.structs[st].a_traits)):
                bindings += String(
                    "    comptime E",
                    self.structs[st].a_traits[i],
                    " = ",
                    self.ty_str(self.structs[st].a_types[i], names, self_ty),
                    "\n",
                )
            if st == self.alias_struct:
                self.alias_ty = self.alias_saved
                self.alias_text = self.alias_saved_text
            if not counted:
                s += "@fieldwise_init\n"
            s += String("struct ", self.structs[st].name)
            if generic:
                s += String("[T: Tr", self.structs[st].bound, "]")
            elif valued:
                s += "[n: Int]"
            s += String("(", cap_names[self.structs[st].cap])
            for t in self.structs[st].traits:
                s += String(", Tr", t)
            if self.structs[st].cond >= 0:
                s += String(
                    ", Tr",
                    self.structs[st].cond,
                    " where conforms_to(T, Tr",
                    self.structs[st].cond_req,
                    ")",
                )
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
            if counted:
                s += self.counted_text(st, names)
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
                elif self.structs[st].k_sources[i] == -2:
                    s += "Self.n + "
                s += String("(", self.structs[st].k_values[i], ")\n")
            s += bindings
            for f in range(len(self.structs[st].fields)):
                if not self.structs[st].refs[f]:
                    continue
                var bad = self.bad_ref == st * 64 + f
                var origin = self.bad_origin if bad else String("self.f", f)
                var mark = MARK if bad else ""
                s += String(
                    "\n    def f",
                    f,
                    "_ref(ref self) -> ref[",
                    origin,
                    "] ",
                    self.ty_str(self.structs[st].fields[f], names, -1),
                    ":",
                    mark,
                    "\n        return self.f",
                    f,
                    mark,
                    "\n",
                )
            for i in range(len(self.structs[st].impl_methods)):
                var m = self.structs[st].impl_methods[i]
                var b = self.structs[st].impl_bodies[i]
                var args = self.impl_args(st, m)
                var params = self.subst_all(self.methods[m].params.copy(), args)
                var ret = self.subst(self.methods[m].ret, args)
                s += "\n"
                var where_clause = self.where_text(st, m)
                if self.bad_where == st * 64 + i:
                    where_clause = String(
                        " where conforms_to(Self.T, Tr", self.bad_where_req, ")"
                    )
                var sig = self.sig_text(
                    m,
                    params,
                    ret,
                    self.bodies[b].names,
                    self.bodies[b].self_print,
                    where_clause,
                    self.impl_raise(st, m),
                )
                if marked and i == self.mark_impl:
                    sig = sig.replace("\n", String(MARK, "\n"))
                s += sig
                s += self.body_text(b, "        ")
            for m in self.structs[st].own.copy():
                var b = self.methods[m].body
                s += "\n"
                var conds = List[String]()
                var names = self.bodies[b].names.copy()
                for pr in self.methods[m].vwhere.copy():
                    conds.append(self.prop_text(pr, 0, names))
                var where_clause = String()
                if len(conds) > 0:
                    where_clause = " where " + " and ".join(conds)
                s += self.sig_text(
                    m,
                    self.methods[m].params,
                    self.methods[m].ret,
                    self.bodies[b].names,
                    self.bodies[b].self_print,
                    where_clause,
                )
                s += self.body_text(b, "        ")
            s += "\n\n"
            self.alias_ty = -1
        var prefixes = materialize[CONV_PREFIX]()
        for f in range(len(self.fns)):
            var fn_names = self.fn_names(f)
            ref fd = self.fns[f]
            s += String("def ", fd.name)
            if len(fd.bounds) > 0:
                s += "["
                for i in range(len(fd.bounds)):
                    if i > 0:
                        s += ", "
                    if fd.bounds[i] < 0:
                        s += String(fn_names[i], ": Int")
                    else:
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
            s += String(
                ")",
                raises_text(fd.raise_ty),
                " -> ",
                self.ty_str(fd.ret, fn_names, -1),
            )
            var conds = List[String]()
            for i in range(len(fd.wheres)):
                if fd.wheres[i] >= 0:
                    conds.append(
                        String(
                            "conforms_to(",
                            fn_names[i],
                            ", Tr",
                            fd.wheres[i],
                            ")",
                        )
                    )
            var vi = index_of(fd.bounds, -1)
            var vwhere = fd.vwhere.copy()
            var asserts = fd.asserts.copy()
            var body = fd.body
            for pr in vwhere:
                conds.append(self.prop_text(pr, vi, fn_names))
            if len(conds) > 0:
                s += " where " + " and ".join(conds)
            s += ":\n"
            for pr in asserts:
                s += String(
                    "    comptime assert ",
                    self.prop_text(pr, vi, fn_names),
                    "\n",
                )
            s += self.body_text(body, "    ")
            s += "\n\n"
        for i in range(len(self.entries)):
            s += String("def run_f", i, "(a: Int, b: Int, c: Int) -> Int:\n")
            s += self.body_text(self.entries[i], "    ")
            s += "\n\n"
        return s^


def lit(x: Int) -> String:
    return String(x) if x >= 0 else String("(", x, ")")


def resolve_values(
    mut data: ConjectureData, text: String, near: Bool, mut made: Bool
) raises -> String:
    """Spells each value argument `@@=<k>@@` as an expression equal to k
    (Mojo folds it), drawn per occurrence: `V[3]`, `V[(1 + 2)]`, ...; and
    `@@=n;c@@` as one equal to `n + c`: `V[n + 1]`, `V[1 + n]`, .... With
    near (the value_expr near miss), `@@=n;0@@` may be spelled `n * 1`,
    ... (marked, and made says so); else it's `n`."""
    var out = String()
    var rest = text
    while True:
        var found = rest.find("@@=")
        if not found:
            break
        var i = found.value()
        var j = rest.find("@@", i + 3).value()
        var inner = String(rest[byte = i + 3 : j])
        out += rest[byte=:i]
        var semi = inner.find(";")
        if semi:
            var name = String(inner[byte = : semi.value()])
            var c = Int(inner[byte = semi.value() + 1 :])
            out += spell_sym(data, name, c, near, made)
            var tail = String(rest[byte = j + 2 :])
            rest = tail^
            continue
        var k = Int(inner)
        var form = data.draw(integers(0, 3))
        if form == 0:
            out += String(k) if k >= 0 else String("(", k, ")")
        elif form == 1:
            var a = data.draw(integers(-3, 3))
            out += String("(", a, " + ", k - a, ")")
        elif form == 2:
            var a = data.draw(integers(0, 6))
            out += String("(", k + a, " - ", a, ")")
        else:
            out += String("(", k, " * 1)")
        var tail = String(rest[byte = j + 2 :])
        rest = tail^
    out += rest
    return out^


def spell_sym(
    mut data: ConjectureData, name: String, c: Int, near: Bool, mut made: Bool
) raises -> String:
    """An expression equal to `name + c`, for resolve_values."""
    if c == 0:
        if not near or data.draw(integers(0, 2)) > 0:
            return name
        made = True
        var forms: List[String] = [
            "{} + 0",
            "0 + {}",
            "{} * 1",
            "1 * {}",
            "{} - 0",
            "({} + 2) - 2",
            "2 + {} - 2",
        ]
        return String(
            MARK_NEAR, forms[pick(data, len(forms))].replace("{}", name)
        )
    var form = data.draw(integers(0, 3))
    if form == 0:
        return String(name, " + ", c) if c > 0 else String(name, " - ", -c)
    if form == 1:
        return String(lit(c), " + ", name)
    if form == 2:
        var a = data.draw(integers(1, 3))
        return String("(", name, " + ", a, ") + ", lit(c - a))
    return String(name, " - ", lit(-c))


def resolve_marks(text: String) -> String:
    """Moves each line's marks to a `# MUTANT` (or `# NEAR`) comment at
    its end."""
    var out = String()
    var lines = text.split("\n")
    for i in range(len(lines)):
        var line = String(lines[i])
        if i > 0:
            out += "\n"
        if MARK in line:
            out += String(line.replace(MARK, ""), "  # MUTANT")
        elif MARK_NEAR in line:
            out += String(line.replace(MARK_NEAR, ""), "  # NEAR")
        else:
            out += line
    return out^


def kinds_from_env(var_name: String, names: List[String]) raises -> List[Int]:
    """The kinds (mutation or near miss) the environment variable asks
    for: none if it's unset, every kind for 1 or `all`, else the kinds
    named (comma-separated)."""
    var spec = getenv(var_name)
    var out = List[Int]()
    if spec == "":
        return out^
    if spec == "1" or spec == "all":
        for k in range(len(names)):
            out.append(k)
        return out^
    for part in spec.split(","):
        var found = False
        for k in range(len(names)):
            if names[k] == String(part):
                out.append(k)
                found = True
        if not found:
            raise Error(String("unknown kind in ", var_name, ": ", part))
    return out^


def draw_program(
    mut data: ConjectureData, kinds: List[Int], near_kinds: List[Int]
) raises -> Tuple[String, String, String]:
    """The program, its compile-time twin, and the expected output; with
    mutation kinds, an ill-typed mutant (and no twin or output); with near
    miss kinds, a program with a near miss."""
    var p = Program()
    if len(kinds) > 0:
        p.mutant = kinds[pick(data, len(kinds))]
    if len(near_kinds) > 0:
        p.near = near_kinds[pick(data, len(near_kinds))]
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
                String("chances=", p.chances),
            )
        if not p.mutated:  # no chance was taken
            assume(False)
    # (spelling the value arguments may make a value_expr near miss)
    var decls = resolve_values(
        data, p.declarations_text(), p.near == NR_VALUE_EXPR, p.near_made
    )
    if p.near == NR_ASSOC and MARK_NEAR not in decls:
        p.near_made = False  # (the alias was never written)
    if p.near >= 0:
        if getenv("DECL_FUZZ_STATS") != "":
            var names = materialize[NR_NAMES]()
            print(
                "near" if p.near_made else "no_near",
                names[p.near],
                String("chances=", p.chances),
            )
        if not p.near_made:
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
                # (LITERAL: a comparison of literals whose result is
                # uncertain)
                if String(e) == "STEP_LIMIT" or String(e) == "LITERAL":
                    assume(False)
                # (a generator bug: the program follows the message)
                raise Error(String(e, "\n", program))
            expected += String("c ", i, " ", v, "\n")
            expected += String("b ", i, " ", v, "\n")
    if p.mutant >= 0:
        var names = materialize[MU_NAMES]()
        var text = String("# FM mutant: ", names[p.mutant], "\n", program)
        return (resolve_marks(text), String(), String())
    if p.near >= 0:
        var names = materialize[NR_NAMES]()
        var head = String("# FM near miss: ", names[p.near], "\n")
        program = resolve_marks(head + program)
        comptime_program = resolve_marks(head + comptime_program)
    if getenv("DECL_FUZZ_STATS") != "":
        var line = String("stats")
        var names = materialize[STAT_NAMES]()
        for i in range(N_STATS):
            line += String(" ", names[i], "=", p.stats[i])
        print(line)
    return (program^, comptime_program^, expected^)


def log_verdict(log: String, first: String) raises:
    """Appends a verdict's first line to a campaign's log (DECL_FUZZ_LOG;
    worker processes share it)."""
    with open(log, "a") as f:
        f.write(first, "\n")


def keep_case(log: String, suffix: String, first: String) raises -> String:
    """Logs a campaign's verdict that isn't OK, and makes a directory for
    its case in <log><suffix>/, which it returns."""
    log_verdict(log, first)
    var out = run(
        String(
            "mkdir -p ", log, suffix, " && mktemp -d ", log, suffix, "/XXXXXX"
        )
    )
    return String(out.strip())


def process_dir(work_dir: String) raises -> String:
    """A directory of this process's own in `work_dir` (worker processes)."""
    var dir = String(work_dir, "/p", external_call["getpid", Int32]())
    _ = run(String("mkdir -p ", dir))
    return dir^


def main() raises:
    var work_dir = (
        String(argv()[1]) if len(argv()) > 1 else "build/decl_fuzz_work"
    )
    var kinds = kinds_from_env("DECL_FUZZ_MUTANTS", materialize[MU_NAMES]())
    var near_kinds = kinds_from_env("DECL_FUZZ_NEAR", materialize[NR_NAMES]())
    if len(kinds) > 0 and len(near_kinds) > 0:
        raise Error("DECL_FUZZ_MUTANTS and DECL_FUZZ_NEAR exclude each other")
    var script = String(
        "examples/decl_fuzz/check_rejected.sh" if len(kinds)
        > 0 else "examples/decl_fuzz/build_and_compare.sh"
    )
    if len(argv()) > 2:
        script = String(argv()[2])
    _ = run(String("mkdir -p ", work_dir))

    var log = getenv("DECL_FUZZ_LOG")

    def differential(
        mut data: ConjectureData,
    ) raises {imm work_dir, imm script, imm kinds, imm near_kinds, imm log}:
        var programs: Tuple[String, String, String]
        try:
            programs = draw_program(data, kinds, near_kinds)
        except e:
            var msg = String(e)
            if log == "" or msg.startswith("proptest."):
                raise e^
            # a campaign: log the generator error and go on
            var first = String(msg.split("\n")[0])
            var bad = keep_case(log, ".bad", String("GEN_ERROR ", first))
            with open(String(bad, "/gen_error.txt"), "w") as f:
                f.write(msg)
            return
        var dir = process_dir(work_dir)
        with open(String(dir, "/program.mojo"), "w") as f:
            f.write(programs[0])
        with open(String(dir, "/comptime.mojo"), "w") as f:
            f.write(programs[1])
        with open(String(dir, "/expected.txt"), "w") as f:
            f.write(programs[2])
        var verdict = run(String("bash ", script, " ", dir, " 2>&1"))
        if log != "":
            # a campaign: log the verdict, keep the case unless it's OK,
            # and go on
            var first = String(verdict.split("\n")[0])
            if first == "OK":
                log_verdict(log, first)
            else:
                var bad = keep_case(
                    log,
                    ".known" if first.startswith("KNOWN") else ".bad",
                    first,
                )
                _ = run(String("cp ", dir, "/*.mojo ", dir, "/*.txt ", bad))
                with open(String(bad, "/verdict.txt"), "w") as f:
                    f.write(verdict)
            return
        if not verdict.startswith("OK") and not verdict.startswith("KNOWN"):
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
    if len(kinds) > 0 or len(near_kinds) > 0:
        # a program where the mutation wasn't made is filtered out (and
        # the vwhere kinds' bigger programs overrun often)
        settings.suppress_health_check = [
            HealthCheck.filter_too_much,
            HealthCheck.data_too_large,
        ]
    if getenv("DECL_FUZZ_NO_SHRINK") != "":
        settings.phases = Phases(shrink=False, explain=False)
    if getenv("DECL_FUZZ_FORK") != "":
        # (a crash in the generator becomes a failure, shrunk)
        settings.fork = True
    var blob = getenv("DECL_FUZZ_REPRODUCE")
    if blob != "":
        # replay a failure from its `reproduce=` blob
        settings.reproduce = blob^
    given_data(differential, settings)
    print("no differences")
