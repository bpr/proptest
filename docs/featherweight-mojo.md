# Featherweight Mojo

Featherweight Mojo (FM) is a small calculus of Mojo's traits, structs and
generics. It exists to generate random well-typed Mojo programs for
testing the compiler (`examples/decl_fuzz/`). It follows the approach of
Feitosa, Ribeiro and Du Bois, *Generating Random Well-Typed Featherweight
Java Programs Using QuickCheck* (CLEI 2018; code at
https://github.com/sfeitosa/fj-qc). They read each typing rule of
Featherweight Java backwards as a generation rule, generate a class
table and then expressions of a type wanted, and so produce only
well-typed programs.

FM is to the declaration side of Mojo what FJ is to Java: traits with
refinement, required and default methods, static constructors and
associated constants; concrete and generic structs conforming to them;
and generic functions over trait bounds. Every program terminates.

FM comes in four stages, all implemented:
- **Stage 1** (the sections from "Syntax" to "Differences from fj-qc")
  is the purely functional core. Every type is `ImplicitlyCopyable`.
- **Stage 2** ("Stage 2: ownership") adds ownership on top:
  - `Copyable` and `Movable`-only types, with `.copy()` and moves (`^`);
  - `mut` and `var` arguments and `mut self`;
  - statements that assign variables and fields, `if`, and bounded `for`;
  - a resource type that counts its destructions.

- **Stage 3** ("Stage 3: ill-typed mutants") turns the generator around:
  each program gets exactly one error, and the compiler must reject it,
  on the line of the error, without crashing.
- **Stage 4** ("Stage 4: near misses") is stage 3's converse: each
  program gets one valid construct close to an error, and the compiler
  must accept it and run it correctly.

"Paths" adds mutants and near misses whose variable is initialized on
some paths only, after an `if`. "Deferred initialization" does the same
for variables declared without a value (`var x: T`), and "Early
returns" for `return` in a branch, and "Loops: `while`, `break` and
`continue`" for the other exits. "Partial moves and counted structs"
moves fields out and gives structs their own `__deinit__`.

Stage 2 found two compiler bugs in its first rounds, stage 3 two more,
stage 4 a new form of one of stage 2's, and the path kinds an -O3 crash
(see each section's "Findings").

## Syntax

```text
P  ::= TD* SD* FD* E*                                   program

TD ::= trait Tr_t(ImplicitlyCopyable, Deinitable | Tr_p, ...):
           [comptime K_t: Int]
           [@staticmethod def make_t(x: Int) -> Self: ...]
           MS*                                          trait

MS ::= def m_i(self, p0: τ, ...) -> τ: ...              required method
     | def m_i(self, p0: τ, ...) -> τ: BODY             default method

SD ::= @fieldwise_init
       struct S_s(Tr_t, ... | ImplicitlyCopyable):      concrete struct
           var f0: τ ...
           comptime K_t = n ...
           M*
     | @fieldwise_init
       struct B_s[T: Tr_b](Tr_t, ... | ImplicitlyCopyable):   generic struct
           var f0: Self.T
           var f1: τ ...
           comptime K_t = n | Self.T.K_u + n ...
           M*

M  ::= def m_i(self, p0: τ, ...) -> τ: BODY             method
     | @staticmethod def make_t(x: Int) -> Self: BODY   static constructor

FD ::= def g_f[T: Tr_t, U: Tr_u](p0: T, p1: U, p2: τ, ...) -> τ: BODY
                                                        0 to 2 type parameters

E  ::= def run_fN(a: Int, b: Int, c: Int) -> Int: BODY  entry point

BODY ::= var v0 = e  ...  return e

τ  ::= Int | S | B[τ] | X           X: T, U, Self, Self.T

e  ::= x | n | (e ⊕ e) | (e if e ⋈ e else e)
     | e.f_k | e.m_i(e, ...) | τ.make_t(e) | τ.K_t
     | S(e, ...) | B[τ](e, ...) | g_f(e, ...) | g_f[τ, ...](e, ...)

⊕  ::= + | - | * | & | | | ^        ⋈ ::= < | == | !=
```

Every name is unique (`m_i` is numbered across the program, and `make_t`
and `K_t` carry their trait's number). So there is no overloading and no
shadowing. fj-qc does the same by appending the class name to each
method name.

## Auxiliary definitions

**Refinement.** `R ≤ R'` is the reflexive, transitive closure of the
trait parent lists.

**Conformance.** `Δ ⊢ τ ◁ R`, where Δ maps the type parameters in scope
to their bounds:

```text
  S (or B) declares conformance to R_1..R_n,  R_i ≤ R
  --------------------------------------------------- [C-Struct]
       Δ ⊢ S ◁ R        Δ ⊢ B[σ] ◁ R   (for every σ)

        Δ(X) ≤ R
  ------------------ [C-Param]
      Δ ⊢ X ◁ R
```

`Int` conforms to nothing. Conformance of a generic struct does not
depend on its argument (no `where` clauses in stage 1).

**Fields.** `fields(S)` is S's field types. `fields(B[σ])` is
`[T ↦ σ]` applied to B's field types.

**Method types.** `mtype(m, τ)`:
- for an own method of `S`: its signature;
- for an own method of `B`, with τ = `B[σ]`: `[T ↦ σ]` applied to its
  signature;
- for a method declared in trait R, with `Δ ⊢ τ ◁ R`: `[Self ↦ τ]`
  applied to its signature.

**Associated constants.** `kval(K_t, τ)` for a struct type τ:
- `n` when τ's struct defines `comptime K_t = n`;
- `kval(K_u, σ) + n` when τ = `B[σ]` and B defines
  `comptime K_t = Self.T.K_u + n`.

**Method bodies.** `mbody(m, τ)` for a closed struct type τ:
- own methods: their body;
- trait methods: the body in τ's struct if it implements m (required, or
  an override of a default), otherwise the trait's default.

## Well-formed programs

1. **Traits come in order.** A trait's parents are earlier traits, so `≤`
   is acyclic (FJ: no cycles in `<:`). A root trait refines
   `ImplicitlyCopyable, Deinitable`. Copyable lets values be reused
   without `^`, which keeps the calculus pure. `Deinitable` is needed
   for a generic struct to hold a `Self.T` field.
2. **Struct fields mention only earlier structs.** So the types have
   finite values and `T-New` terminates at size 0 (FJ's `genAttrs` picks
   field types from the classes generated so far). Field 0 of a generic
   struct has type `Self.T`.
3. **Conformance is complete.** A struct conforming to `R_1..R_n`
   implements every method that has no default (including `make_t`) in
   every trait `R` with `R_i ≤ R`. It defines `K_t` for every such trait
   that declares one. It may override any default.
4. **Bodies are well typed.** Each body types with the judgment below,
   at the result type of its signature. Its context is:

   | Body | Δ | Γ |
   |---|---|---|
   | trait default | `Self: Tr_t` | `self: Self`, `p_i` |
   | concrete struct method | (empty) | `self: S`, `p_i` (`x: Int` for make) |
   | generic struct method | `Self.T: Tr_b` | `self: B[Self.T]`, `p_i` (`x: Int` for make) |
   | function | `T: Tr_t, U: Tr_u` | `p_i` |
   | entry point | (empty) | `a, b, c: Int` |

   In a struct, a trait signature's `Self` becomes the struct's type
   (`S` or `B[Self.T]`). The generator writes that type either as
   `Self` or by name.
5. **Ranks.** Every method signature and function has a rank in
   `0..MAX_RANK`, and entry points rank above. A body of rank r calls
   only methods and functions of rank < r (`T-Invk`, `T-Static` and
   `T-Call` check this). A trait method's implementations and its
   default all share its rank. So every call lowers the rank, the call
   depth is at most `MAX_RANK + 1`, and every program terminates. fj-qc
   gets termination differently: a method body sees only the classes
   before it, plus its own class without methods.
6. **Static constructors of generic structs.** `B[T: Tr_b]` conforms to a
   trait that requires `make_t` only if some trait `R` with
   `Tr_b ≤ R` declares a `make_u` of lower rank than `make_t`. `make_t`
   has no `self` to take a `T` from, so it must build its `Self.T` field
   with `Self.T.make_u(...)`.

## Typing

`Δ; Γ; r ⊢ e : τ`, where r is the rank of the body:

```text
  Γ(x) = τ                          n an Int literal
  -------------- [T-Var]            ------------------ [T-Lit]
  Δ;Γ;r ⊢ x : τ                     Δ;Γ;r ⊢ n : Int

  e1, e2 : Int                      e1, e2 : Int    e3, e4 : τ
  ----------------- [T-Bin]         ---------------------------- [T-Cond]
  (e1 ⊕ e2) : Int                   (e3 if e1 ⋈ e2 else e4) : τ

  e : τ0    fields(τ0) = τ̄          τ ∈ {S, B[σ]}   fields(τ) = τ̄   ē : τ̄
  -------------------- [T-Field]    -------------------------------------- [T-New]
  e.f_k : τ_k                                 τ(ē) : τ

  e0 : τ0   mtype(m, τ0) = τ̄ → τ   ē : τ̄   rank(m) < r
  ------------------------------------------------------ [T-Invk]
                    e0.m(ē) : τ

  Δ ⊢ τ ◁ Tr_t   Tr_t declares make_t   e : Int   rank(make_t) < r
  ---------------------------------------------------------------- [T-Static]
                       τ.make_t(e) : τ

  Δ ⊢ τ ◁ Tr_t   Tr_t declares K_t
  -------------------------------- [T-K]
           τ.K_t : Int

  g[X̄: R̄](τ̄) -> τ0   Δ ⊢ σ̄ ◁ R̄   ē : [X̄ ↦ σ̄]τ̄   rank(g) < r
  ----------------------------------------------------------- [T-Call]
     g[σ̄](ē) : [X̄ ↦ σ̄]τ0       (also written g(ē): σ̄ inferred)
```

There is no subsumption rule. Mojo has no subtyping between these
types. FJ's `T-UCast` turns into the conformance premise of `T-Call`:
passing an `S` where a `T: Tr` is expected is what passing an object
where a superclass is expected is in FJ. FJ's downcasts and "stupid
casts" have no counterpart in stage 1. (fj-qc doesn't generate them
either.)

## Evaluation

FM is big-step and call by value. Values are `n` (a 64-bit Int that
wraps on overflow, as Mojo's does) and `S(v̄)`. ρ maps variables to
values. θ maps the type parameters in scope to closed types.

One exception to wrapping: Mojo computes an expression built only from
literals exactly (`IntLiteral`), and truncates it when it becomes an
`Int`. Truncation commutes with `+`, `-`, `*` and the bitwise operators,
so wrapping at each step gives the same `Int`. A comparison whose two
sides are both such expressions compares the exact values, though:
`(100 * 2) < (100 * 4611686018427387904)` is true. The evaluator compares
those exactly, in `Int128`. An associated constant is a literal on a
concrete struct (`S0.K0 * 2^62 > 0` is true) but an `Int` on a type
parameter (`T.K0 * 2^62 > 0` is false). A program where that or `Int128`
overflow could change a comparison is rejected.

```text
  ρ,θ ⊢ e.f_k      ⇓ v_k                 if e ⇓ S(v̄)
  ρ,θ ⊢ τ(ē)       ⇓ S(v̄)                if ē ⇓ v̄
  ρ,θ ⊢ e0.m(ē)    ⇓ v    where e0 ⇓ v0, ē ⇓ v̄, τ0 = θ(type of e0),
                          and BODY = mbody(m, τ0) runs with
                          ρ' = [self ↦ v0, p ↦ v̄] and
                          θ' = [T ↦ σ] if τ0 = B[σ], or
                               [Self ↦ τ0] for a trait default
  ρ,θ ⊢ τ.make_t(e) ⇓ v   the same, with τ0 = θ(τ) and ρ' = [x ↦ v]
  ρ,θ ⊢ τ.K_t      ⇓ kval(K_t, θ(τ))
  ρ,θ ⊢ g[σ̄](ē)    ⇓ v    g's BODY with ρ' = [p ↦ v̄], θ' = [X̄ ↦ θ(σ̄)]
  ρ,θ ⊢ var v = e; BODY ⇓ the body with ρ[v ↦ value of e]
```

Dispatch is resolved from the static type of the receiver under θ, not
from the value. Mojo monomorphizes generics, so the two agree. Entry
points return Ints, which `main` prints.

## Generation

Generation runs in the order of the well-formedness conditions:

1. **Trait headers:** parents (among earlier traits), whether there is
   a `K_t`, and whether there is a `make_t` and its rank.
2. **Struct headers, in order:** generic or not, the bound, fields over
   earlier structs, and conformances. Each trait is picked with
   probability 1/2, subject to condition 6. Then the `K_t` definitions.
3. **Trait method signatures:** whether each has a default, and its rank.
4. **Struct own method signatures.**
5. **Function signatures.**
6. **Bodies:** trait defaults, then each struct's implementations
   (required, plus overrides drawn with probability 1/2), then own
   methods, then functions, then 1 to 4 entry points.

Signatures (steps 3 to 5) come before all bodies, so any body can call
any method or function of lower rank, whichever struct it belongs to.

Parameter and result types are `Int` a third of the time and the
declaration's own type (`Self`, the struct's type, `T`) a third of the
time. The rest come from the context's *type pool*: `Int`, the concrete
structs, the type parameters in scope, and generic structs applied to
conforming types, two levels deep, capped at 40 types. The bias makes
calls returning the type wanted common.

**Expressions.** `gen(Δ, Γ, r, τ, size)` reads the typing rules
backwards. For each rule it collects the candidates that produce a τ:
- `T-Var`: the variables of type τ, and fields of variables of type τ;
- `T-Field`: (type, field) pairs from the pool with a field of type τ;
- `T-Invk`: (receiver type, method) pairs whose `mtype` result is τ;
- `T-Call`: functions whose result unifies with τ, with conforming type
  arguments for the parameters it doesn't fix;
- and so on for the other rules.

It keeps the rules that have a candidate, picks one, picks a candidate,
and generates the premises recursively. Like fj-qc, it never
backtracks.

It differs from fj-qc in three ways:
- **Weights.** fj-qc picks among the possible rules uniformly. Here a
  rule appears in the list as many times as its weight: `T-Invk` 4,
  `T-Call` 3, `T-Static` and `T-K` 2, the rest 1. With uniform choice,
  the dispatch paths were rarely reached (see "Coverage").
- **Order.** The rule list starts with the simplest rules (variables and
  literals, then `T-New`). proptest shrinks the choice toward 0, so
  shrinking leads to simple programs.
- **Entry roots.** At the root of an entry point, only `T-Invk`,
  `T-Call` and `T-K` are allowed when they have candidates. Otherwise
  many entry points were just `return a`.

**Size.** Receivers get `size - 1`. Operands, arguments and branches get
`size / 2`. Bodies start at size 4 and entry points at 6. At size 0 only
the ground rules apply:
- **Int:** a literal or a variable;
- **struct type:** `T-New`, finite by condition 2;
- **type parameter:** a variable, a field of one (`self.f0` in a generic
  struct), or `T-Static`.

Every context has a ground term of every type in its pool. Functions
have a parameter of each type parameter's type. Trait defaults and
methods have `self`. A static make of a generic struct has
`Self.T.make_u`, by condition 6.

**Shrinking keeps programs well typed.** proptest shrinks the generator's
choice sequence and replays the generator. So every shrunk program is
one the generator could have drawn, and is well typed by construction.
QuickCheck would need a type-aware shrinker on the AST, and fj-qc has
none.

## Oracles

`examples/decl_fuzz/build_and_compare.sh` builds the program at -O0 and
-O3, and builds a twin that evaluates the entry points with `comptime`.
It runs all three and compares them with the generator's own
evaluation:

| Verdict | Meaning |
|---|---|
| `BUILD_FAIL` | The compiler rejected the program: a generator bug, or a front-end bug rejecting a well-typed program |
| `BUILD_CRASH`, `BUILD_TIMEOUT` | The compiler crashed or ran too long |
| `KNOWN #<issue> ...` | It crashed the way a filed bug does (`known_crashes.txt`); not a failure |
| `RUN_FAIL` | A build crashed or hung |
| `UNBALANCED` | (Stage 2) A `Res` was destroyed fewer or more times than it was made |
| `DIFF_O3` | -O0 and -O3 disagree: an optimizer bug |
| `DIFF_COMPTIME` | The compile-time interpreter disagrees with -O0 |
| `DIFF_EXPECTED` | All three builds agree, but with each other, not with the reference semantics |

`DIFF_EXPECTED` is what FM adds over `examples/compiler_fuzz`. A
front-end bug in dispatch, parameter substitution or associated
constants happens before optimization. So -O0, -O3 and probably
`comptime` agree on the wrong answer, and only an independent evaluator
sees it. The generator's own type checker plays no part. The compiler is
the type checker, and fj-qc's `prop_genwelltypedexpr` corresponds to
"every program builds".

## Coverage

FJ's authors measured coverage of their interpreter with HPC. Here,
`DECL_FUZZ_STATS=1` prints for each program how often evaluation reached
each path: own methods, required implementations, overrides, trait
defaults, static constructors, generic functions, associated constants,
and constants defined through `Self.T`.

Number of programs, out of 200 (seed 1), reaching each path:

| Path | Uniform rules (fj-qc) | Weighted, call roots | Plus biased signatures |
|---|---|---|---|
| own method | 65 | 121 | 110 |
| required impl | 59 | 89 | 102 |
| override | 11 | 21 | 32 |
| trait default | 15 | 7 | 33 |
| static make | 47 | 65 | 76 |
| generic fn | 33 | 31 | 35 |
| `τ.K_t` | 42 | 54 | 86 |
| `Self.T.K_u` | 0 | 0 | 14 |

Each column is a single run, so the numbers are noisy: one generator
change alters every program drawn from the seed. The first column also
drew conformances differently (0 to 2 traits instead of each trait with
probability 1/2).

**Validation.** An evaluator broken on purpose, which ignores overrides,
was caught as `DIFF_EXPECTED` within 200 programs. The program shrank to
an entry point `S1(a, a).m0(a)`, where `S1` overrides `m0`'s default.
With uniform rules, the same broken evaluator went unnoticed in 100
programs.

**First rounds.** 210 programs on the pinned 1.3.0.dev2026111705, and 600
(seeds 101 to 103) on nightly 1.3.0.dev2026112316: all built, and all four
results agreed.

## Differences from fj-qc

- fj-qc never prints Java or runs `javac`. It tests its own interpreter
  against progress and preservation. FM programs are compiled and run.
- fj-qc never overrides methods, so dynamic dispatch is never exercised.
  FM structs override trait defaults half the time.
- fj-qc picks among the possible rules uniformly. FM weights them and
  forces calls at the roots of entry points.
- fj-qc doesn't shrink. FM programs shrink through proptest's choice
  sequence and stay well typed.
- fj-qc's `T-DCast` and `T-SCast` candidates are computed but never used.
  FM has no casts.

## Stage 2: ownership

Stage 2 extends every part of stage 1: the syntax, Γ, the typing rules,
the evaluator and the generator. Its environment is close to the
effect-tracking one of Midtgaard et al., *Effect-driven QuickChecking of
compilers* (ICFP 2017): the generator knows, at each point, which
variables are live and what the current statement has done with them.

### Syntax

```text
TD  ::= trait Tr_t(Copyable, Deinitable | ImplicitlyCopyable, Deinitable
                   | Tr_p, ... [, ImplicitlyCopyable]): ...
SD  ::= @fieldwise_init struct S_s(κ, Tr_t, ...): ...
κ   ::= Movable | Copyable | ImplicitlyCopyable          capability

MS, M ::= def m_i(ς self, c p0: τ, ...) -> τ: ...
ς   ::= (read) | mut                                    self convention
c   ::= (read) | mut | var                              argument convention

τ   ::= ... | Res          prelude: Copyable, one field `val: Int`

BODY ::= s* return e
s   ::= var v = e | x = e | x.f_k = e | _ = e
      | if e ⋈ e: s* else: s*
      | for i in range(n): s*                            n in 0..3

e   ::= ... | x^ | e.copy() | Res(e)
```

### Capabilities

A type's capability is one of `Movable`, `Copyable` and
`ImplicitlyCopyable`, ordered from weakest to strongest:
- `Int` is `ImplicitlyCopyable` and `Res` is `Copyable`;
- a struct has the capability it declares;
- a type parameter has its bound's.

Well-formedness gains three conditions:

7. **Traits are copyable.** A root trait refines `Copyable` or
   `ImplicitlyCopyable` (and `Deinitable`). A refining trait inherits
   the strongest capability of its parents and may add
   `ImplicitlyCopyable`. So type parameters are always at least
   `Copyable`: a read variable of type `T` gives a `T` with `.copy()`,
   and every context has ground terms of its type parameters.
8. **Fields are at least as capable as their struct.** A struct's field
   types have its capability or a stronger one. A generic struct is at
   most as capable as its bound.
9. **Conformance needs capability.** A struct conforms only to traits
   whose capability is no stronger than its own. So `Movable` structs
   conform to no trait, and are never type arguments.

### Γ and positions

Γ maps each variable to its type, a **kind** and a **liveness**:

| Kind | Variables | Assignable | Movable |
|---|---|---|---|
| read | read arguments, read `self`, loop variables | no | no |
| mut | `mut` arguments, `mut self` | yes | no |
| owned | `var` locals, `var` arguments | yes | yes |

Every expression is drawn for a **position**:
- **read (borrowed):** a read argument, a receiver, an operand.
- **owned (consumed):** a `var` argument, a field of `τ(ē)`, the value
  of a `var` or an assignment, a result, or a ternary branch.

A place `x` or `x.f_k` of type τ can be used as follows:

| Position | `ImplicitlyCopyable` | `Copyable` | `Movable` |
|---|---|---|---|
| read | `x` | `x` | `x` |
| owned | `x` | `x.copy()` or `x^` | `x^` |

Only a live variable of kind owned can be moved, and only as a whole
(no partial moves in stage 2). Moving it makes it dead. Assigning a dead
variable makes it live again.

### Exclusivity within a statement

Each statement keeps two sets: the variables it has **touched**
(used in any way), and the ones it has passed as **`mut`**. Arguments
are drawn left to right, receiver first, the same order Mojo evaluates
them in. The rules:
- **Reading** `x` needs x live and not passed as `mut`.
- **Moving** `x` needs x untouched (and then kills it).
- **Passing** `x` or `x.f_k` as `mut` needs x untouched. It then marks
  x as passed, so the rest of the statement can't use it.

So `g(x, x^)`, `x.m(x^)` and `g(x.f0, x)` with a `mut x` are never
generated. A call with a `mut` argument (or `mut self`) appears only at
the root of a statement, so its arguments contain no other `mut` calls.

Moves happen only where they're unconditional: never inside a ternary
branch.

### Statements

- `var v = e`: e is owned; v enters Γ as owned and live.
- `x = e`: x is assignable, and live (or moved in the current block). e
  may use x, and even move it (`x = g(x^)`). Then x is live.
- `x.f_k = e`: x is live and assignable. Before e is drawn, x is marked
  touched, so e may read x but not move it or pass it as `mut`.
- `_ = e`: drawn as a call with `mut` arguments when one is possible.
- **Blocks** (`if` branches and `for` bodies, nested at most twice):
  - their locals go out of scope at the end;
  - an outer variable live at a block's start is live at its end: a
    variable the block moved gets reassigned at its end;
  - outer variables that were dead at the start can't be reassigned in
    the block.

  So after an `if` every variable is either surely live or surely dead.
  Mojo would have to track a "maybe moved" state, which FM avoids.

### Evaluation with a store

The evaluator keeps a frame of variable slots, with a hole for a moved
variable. Values are immutable trees, so a field assignment rebuilds
the path to the field.
- **`mut` arguments:** the callee gets a copy, and when it returns,
  the copy is written back to the caller's place (copy-in/copy-out).
  Mojo's exclusivity rules make that the same as passing by reference.
- **`var` arguments and `.copy()`** just pass the value. With value
  semantics, a copy is indistinguishable from the original.
- **Block locals** are popped at the end of the block.
- **Moves** read the slot and empty it, so a generator bug that uses a
  moved variable shows up as an evaluator error.

**Checksums.** An entry point keeps its result in a variable. It then
returns that result plus every Int reachable from its live owned
variables (field paths up to 3 deep, at most 8 per variable), as Csmith
does. Without this, `mut` calls and field assignments rarely reached the
printed output: an evaluator that never wrote `mut` arguments back went
unnoticed in 400 programs.

**Destruction.** The evaluator doesn't model destruction. `Res`
counts its constructions and copies minus its destructions, at a fixed
address (`mmap`, since Mojo has no globals). `main` checks the count
after each entry point and prints `UNBALANCED` if it isn't zero. The
`comptime` twin gets a `Res` without the count.

### Generation

Stage 2 adds the following to the generator:
- **Capabilities:** a struct's capability is drawn first (its
  strongest possible one is where shrinking leads), then its fields and
  conformances to match.
- **Conventions:** read 1/2, `var` 1/3 and `mut` 1/6 for arguments,
  and `mut self` 1/4. `mut` arguments are rarer because they confine a
  call to the roots of statements.
- **Statements:** bodies have 0 to 3 statements before the result, and
  entry points up to 5. A `var` picks a type with `mut` methods half
  the time. `_ = e` statements are weighted up when a `mut` call is
  possible.
- **Backtracking:** after a statement has moved or `mut`-borrowed the
  only variable of some type, a later argument of that type can get
  stuck. `gen` then restores Γ and tries another rule; a statement that
  still gets stuck becomes `var vN = <an Int>`. This is the backtracking
  fj-qc avoids and Pałka et al. use. It brought rejected test cases
  from 22% down to 1 to 3%.

Coverage, number of programs out of 200 (seed 1) whose evaluation
reached each path (`DECL_FUZZ_STATS=1`), after the tuning above:

| own | required | override | default | static | generic | K | `mut` call | move | copy | assign | loop | Res |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 92 | 55 | 12 | 16 | 33 | 4 | 47 | 38 | 60 | 81 | 101 | 101 | 138 |

### Findings

**Loop field-store double destroy.** The first stage-2 round on nightly
1.3.0.dev2026112316 printed `UNBALANCED 0 -3`. Reduced by hand:

```mojo
def f():
    var v = Res(1)
    for i in range(2):
        v.val = i + 10      # last use of v
```

When a variable's last use is a field assignment in a loop, Mojo
destroys it at the end of every iteration and once more after the loop.
A struct holding a `List` gets a double free (AddressSanitizer
confirms). It happens at -O0 and -O3 and on 1.3.0.dev2026111705 too.
Filed as [#7759](https://github.com/modular/modular/issues/7759).

The generator works around it: each `for` loop is followed by
`_use(v)` (a no-op generic function) for every live owned or `mut`
variable. `DECL_FUZZ_NO_LOOP_STORE_WORKAROUND=1` turns this off.

At first the workaround covered owned variables only. Two rounds later
(stage 2, seed 821) it gave `UNBALANCED 1 -3` again, through a `mut
self`: a method stored a field of `self` in a loop, then assigned
`self` whole after it. The stored values are destroyed twice each, and
the same happens to a local assigned whole after the loop:

```mojo
def f(mut s: S):            # S has one field f0: R
    for i in range(3):
        s.f0 = R(i)         # each R(i) is destroyed twice
    s = S(R(7))
```

That is #7759's bug, in forms the issue doesn't show (a `mut` argument,
and a reassignment after the loop), posted as a
[comment](https://github.com/modular/modular/issues/7759#issuecomment-7170310106)
on it. Now the workaround reads `mut` variables too.

**Self-assignment.** With that workaround off, the next round found a
`DIFF_O3` instead (-O3 printed 3 and 0, -O0 and the evaluator 4):

```mojo
@fieldwise_init
struct P1(ImplicitlyCopyable):
    var x: Int


def f1(a: Int) -> Int:
    var v = P1(a)
    v = v               # garbage at -O1 and above
    return v.x
```

Only a whole local variable of a struct type is affected. `Int`,
`v = v.copy()`, `v = w`, `o.p = o.p`, a `mut` argument, and generic code
are fine. Filed as [#7760](https://github.com/modular/modular/issues/7760).
The generator writes `_use(v)` instead of `v = v`;
`DECL_FUZZ_NO_SELF_ASSIGN_WORKAROUND=1` turns this off.

With both workarounds on, 600 more programs (seeds 201 to 203, nightly
1.3.0.dev2026112316) were clean.

## Stage 3: ill-typed mutants

Stages 1 and 2 test that the compiler accepts every well-typed program
and runs it correctly. Stage 3 tests the converse: that it rejects
ill-typed ones. A soundness hole in the type or ownership checker, such
as a missed use after `^` or an aliased `mut` argument, lets through a
program with undefined behavior. A well-typed generator never produces
one.

A **mutant** is a stage-2 program with exactly one error. Its kind is
drawn first. The generator then draws the program as usual, and at each
place where it could make that error, it does so with probability 1/6
(`MU_ODDS`), at most once. Reading the typing rules backwards also
tells it which places those are. This follows the type-overwriting
mutations of Hephaestus (Chaliasos et al., *Finding typing compiler
bugs*, PLDI 2022), but the generator makes the error while it draws the
program, so it knows Γ at the mutation. A program where no chance came
up is rejected (`assume(False)`), at no compile cost. The shrinker moves
the mutation to the first chance and shrinks the rest of the program
around it, as in stage 2.

### Mutation kinds

Each kind breaks one rule from stages 1 and 2:

| Kind | Rule broken | Example | Mojo's error |
|---|---|---|---|
| `type` | an expression of type τ where τ' ≠ τ is expected (argument, field, operand, condition, ternary branch, result, assigned value, `mut` place) | `g0(S1(1))` for `p0: S0` | cannot be converted from 'S1' to 'S0' |
| `use_moved` | use of a dead variable | `var y = x^` then `_use(x)` | use of uninitialized value 'x' |
| `implicit_copy` | an owned place of a type that isn't `ImplicitlyCopyable`, without `.copy()` or `^` | `var y = x` for a `Copyable` x | cannot be implicitly copied |
| `assign_read` | assignment to a read variable or its field | `p0.f0 = 1` for a read `p0` | expression must be mutable in assignment |
| `mut_read` | a read variable passed as `mut` (or as `mut self`) | `h(p0)` | value passed to mutable argument must be mutable |
| `alias` | an argument overlapping a `mut` argument of the same call | `hm(x, x)`, `h(x, x.f1)` | aliasing values passed mutably to 'a' argument and ... to 'b' argument |
| `move_read` | `^` on a read variable | `var y = p0^` | cannot transfer out of immutable reference |
| `loop_move` | a loop moves an outer variable without reinitializing it | `for i in range(2): var y = x^` | use of uninitialized value 'x' |
| `no_method` | a method the receiver's type doesn't have (for a type parameter: one its bound doesn't give) | `p0.m1()` for `p0: T`, `T: Tr0` | 'T' value has no attribute 'm1' |
| `bound` | a type argument that doesn't conform to its bound | `g0[S1](...)`, `B0[Res](...)` | parameter 'T' has 'Tr0' type, but value has type ... |
| `missing` | a struct without a required method or associated constant | `S0` conforming to `Tr0` without `m0` | 'S0' does not implement all requirements for 'Tr0' |
| `sig` | an implementation whose result type, parameter type, or convention of `self` or a parameter differs from the trait's | `def m0(mut self, ...)` for a read `self` | 'S0' does not implement all requirements for 'Tr0' |
| `cap` | a struct declared more capable than a field | `struct S0(Copyable)` with a `Movable` field | cannot synthesize copy constructor because field 'f0' has non-copyable type |

A mutant is only useful where FM is no stricter than Mojo: a program FM
rejects and Mojo rightly accepts says nothing. Small probes settled the
first rules below before any mutant was made. The `ACCEPTED` verdicts of
the first rounds found the rest, each time a rule of Mojo's that FM
didn't have:
- **A read `Int` is passed by value.** So `h(x, x.f0)` with `mut x` and
  a read `Int` parameter is accepted, and `a^` on a read `Int` argument
  too. `alias` and `move_read` leave `Int` out.
- **Disjoint fields don't alias.** `f(q.a, q.b)`, with `q.a` passed as
  `mut`, is accepted. Stage 2 never generates it (it treats a `mut`
  argument as using its whole root variable). `alias` overlaps only a
  whole variable with its fields, or a field with itself.
- **Type inference.** `g0(S2(1))` is well typed for `g0[T: Tr0](p0: T)`
  when `S2` conforms to `Tr0`. A generic call with a mutated argument is
  always written with explicit type arguments.
- **Receivers.** Another type's receiver may well have the same method
  (two structs conforming to one trait), so `type` never changes a
  receiver.
- **No implicit conversions.** None of the types in a pool converts to
  another: Int's `@implicit` constructors take only literals, `Bool` and
  SIMD values.
- **An implementation may take read where its trait says `mut` or
  `var`**, for a parameter or for `self` (found by `ACCEPTED`). A read
  parameter can take a `mut` reference or an owned value, so this is
  sound, though the manual doesn't say so. `sig` changes a convention
  only to `mut` or `var`.
- **A method with another signature than a trait default is an
  overload** (`ACCEPTED`), and the default still satisfies the trait.
  `sig` changes only methods without defaults.
- **`^` on an `Int` has no effect** (`ACCEPTED`; Mojo warns "transfer
  from a value of trivial register type 'Int' has no effect"). The
  variable stays initialized, so `use_moved` and `loop_move` leave Ints
  out.
- **`_ = x^` doesn't move x** (`ACCEPTED`). The manual says so: "`_ =
  t^` keeps `t` alive exactly as `_ = t` does." For the same reason,
  `_ = x.f` needs no `.copy()`. Mutants have no moves, and no
  `implicit_copy`, at the root of `_ = e`.
- **An argument `x^` is moved at the call**, after the other arguments
  are evaluated (`ACCEPTED`). So `f(x^, x.copy())` is fine, and
  `use_moved` leaves out variables moved in the current statement.
- **The dead branch of a constant `if` isn't checked for uses of moved
  values** (`ACCEPTED`), as for a ternary (see Findings). With a
  condition of literals and associated constants (`if S0.K1 ==
  S0.K1:`), Mojo drops the dead branch first. `x < x` and `Res(1).val <
  0` aren't folded. `use_moved` and `loop_move` mutants aren't made
  inside either branch of such an `if`. An `implicit_copy` there is
  still rejected.

Other things that are errors in FM proved to be errors in Mojo too:
`return x` of a local `Copyable` variable (no implicit move on return),
and comparing two structs (no synthesized `__eq__`).

### Oracle

`examples/decl_fuzz/check_rejected.sh` builds the mutant at -O0 (where
an error is found doesn't depend on optimization). The generator marks
the mutation's line by putting a marker in the mutated expression's
text, which then appears in every expression that contains it. When the
program is printed, each line holding the marker gets a `# MUTANT`
comment. A `loop_move` marks the whole loop, since Mojo reports the
first use in the next iteration, which may be on any line of the body.
Declaration kinds mark the struct's header, plus its fields (`cap`) or
the changed signature (`sig`).

| Verdict | Meaning |
|---|---|
| `OK` | Rejected, with an error on a marked line |
| `ACCEPTED` | The compiler accepted the mutant: a soundness bug, or a rule FM has that Mojo doesn't |
| `BUILD_CRASH`, `BUILD_TIMEOUT` | The compiler crashed or ran too long |
| `KNOWN #<issue> ...` | It crashed the way a filed bug does (`known_crashes.txt`); not a failure |
| `WRONG_LINE` | Rejected, but with no error on a marked line: a generator bug, or a misplaced error |
| `NO_MARK` | No line is marked: a generator bug |

`DECL_FUZZ_MUTANTS=1` turns stage 3 on, and `DECL_FUZZ_MUTANTS=alias,sig`
restricts it to the kinds named. `DECL_FUZZ_STATS=1` prints each
program's kind and whether a chance came up. Each program starts with a
`# FM mutant: <kind>` comment.

Mutants are cheap: the compiler rejects most of them while parsing, so
600 take about a minute on 16 cores. Rejected programs (no chance
came up) cost no build.

Four kinds need a `mut` call (`alias`, `mut_read`) or a moved non-Int
variable (`use_moved`, `loop_move`). Few stage-2 bodies have those: at
first, only 4 to 13% of programs of these kinds got their mutation, and
nearly all the others had no chance at all. A mutant of these kinds now
steers the program toward them:
- **`alias`, `mut_read`:** `mut` parameters and `mut self` are drawn
  half the time (instead of 1/6 and 1/4). A call with `mut` arguments
  may go ahead with one `mut` place missing, if a read place of its type
  (`mut_read`) or one overlapping another argument (`alias`) is there
  instead; that argument is then the mutation.
- **`use_moved`:** a block may move a live owned variable itself (`var
  vN = x^`, and x isn't reinitialized before the block's end). If no
  chance to use x was taken when the block ends, a use of it goes there.
- **`loop_move`:** loops are drawn more often where an outer owned
  variable is live. If no chance was taken in a loop body, a move goes
  at its end. It never moves a variable the body assigns before the move
  (the assignment would reinitialize it on every iteration).
- **`use_moved`, `loop_move`:** a new local variable isn't an `Int`
  (redrawn once).

`DECL_FUZZ_STATS=1` prints how many chances each program had. In 3000
mutants (seeds 305 to 309), the number of programs of each kind that
got their mutation, and the number rejected (with the share made before
tuning):

| Kind | Made | No chance | Made, before |
|---|---|---|---|
| `type` | 372 | 7 | 89% |
| `cap` | 316 | 95 | 76% |
| `assign_read` | 310 | 25 | 89% |
| `loop_move` | 279 | 100 | 13% |
| `no_method` | 253 | 141 | 66% |
| `move_read` | 248 | 49 | 81% |
| `bound` | 223 | 164 | 51% |
| `implicit_copy` | 199 | 124 | 54% |
| `missing` | 195 | 137 | 66% |
| `mut_read` | 188 | 143 | 11% |
| `use_moved` | 188 | 66 | 4% |
| `sig` | 179 | 244 | 48% |
| `alias` | 81 | 201 | 5% |

A run restricted to a few kinds rejects many programs, so stage 3 turns
off proptest's `filter_too_much` health check.

**Validation.** The oracle found two generator bugs on its own. The
first was a `WRONG_LINE`: an outer loop's `loop_move` marked a loop
nested in its body instead. The second was a `NO_MARK`: stage 2's
`v = v` workaround (#7760) dropped a mutated `v = v` (`implicit_copy`),
taking the mark with it. The `ACCEPTED` verdicts above found the five
rules FM lacked. With all of them fixed, 4200 mutants (seeds 305 to
311, nightly 1.3.0.dev2026112316) were all rejected on a marked line.

Tuning the rare kinds made them common enough to show two more
problems. `ACCEPTED` verdicts showed the constant `if` rule above, and
`loop_move` mutants whose body assigned the variable before moving it.
A `WRONG_LINE` showed a compiler bug in the well-typed part of a
program (see Findings). With these fixed, 1200 mutants of the four tuned
kinds (seeds 601 and 602), 900 `loop_move` mutants (seeds 601 to 603)
and 2400 of all kinds (seeds 621 to 624) were all rejected on a marked
line. 200 well-typed programs (seed 221) passed stage 2.

### Findings

**A generic implicit copy in a dead ternary branch.** Among the first
`ACCEPTED` verdicts were two `implicit_copy` mutants that matched none
of the rules above. Reduced by hand:

```mojo
def take[T: Tr](var x: T) -> T:
    return x^


def g[T: Tr](p: T) -> T:       # Tr refines only Copyable
    return T.make(1) if 1 == 1 else take(p)   # accepted
```

Passing `p` to a `var T` parameter implicitly copies a value that isn't
`ImplicitlyCopyable`. Mojo accepts this, warning only that the branch
is dead. The same call is rejected in a live branch, in a dead `if 1 ==
0:` statement, and for a concrete type. A generic struct's constructor
in the dead branch (`B[T](p)`) is accepted too: the generator's own
shrunk program has `B3[Self](self)` in a trait default method. Filed as
[#7770](https://github.com/modular/modular/issues/7770). #7664 is the
same construct the other way around: there, valid code in the dead
branch is rejected.

Uses of a moved variable in a dead branch are accepted for any type,
which may be by design. The generator makes neither `use_moved` nor
`implicit_copy` mutants inside ternary branches.
`DECL_FUZZ_NO_DEAD_BRANCH_WORKAROUND=1` lets it. With that set,
`DECL_FUZZ_MUTANTS=implicit_copy` found and shrank the bug in six
minutes (seed 401).

**A ternary of two places is taken for a `mut` argument.** A
`loop_move` mutant was rejected for the wrong reason (`WRONG_LINE`).
The error was on an unmarked line, in a well-typed method body. Reduced
(first with a line-deletion script, then by hand):

```mojo
def h(x: B, y: String) -> Int:   # both read
    return 0


def main():
    var q = B("a", "b")             # B: two String fields
    var c = q.f0.byte_length()
    print(h(q, q.f1 if c < 0 else q.f0))
    # error: aliasing values passed immutably to 'x' argument and
    # passed mutably to 'y' argument in 'h' call
```

It needs both branches to be different places, one of them overlapping
another argument, and a read parameter: the same place twice, an
rvalue branch (`.copy()`), a `var` parameter or `Int` fields all
compile. It happens on 1117 and 1123, for a concrete struct, an
`ImplicitlyCopyable` struct, a type parameter, and with `self` as the
overlapping argument. Filed as
[#7781](https://github.com/modular/modular/issues/7781). In stage 2,
only branches of an `ImplicitlyCopyable` type other than `Int` can both
be places. The generator now copies the else branch when both are
(`DECL_FUZZ_NO_TERN_PLACE_WORKAROUND=1` turns that off).

## Stage 4: near misses

Stage 2 plays safe: it treats a `mut` argument as using its whole root
variable, never reads a variable in the call that moves it, and treats
`_ = x^` as a move. A checker that is too strict in those places goes
unnoticed, since stage 2 never writes the valid programs it would
reject. #7781, found by luck in stage 3, is such a false rejection.

A **near miss** is a stage-2 program with one construct that is valid
but close to an error, made as a mutant is (its kind drawn first, then
made at a chance, 1/6 each). Unlike a mutant, it is still well typed,
so the evaluator gives its meaning and `build_and_compare.sh` checks it
as in stage 2: `BUILD_FAIL` is a false rejection, and the differences
are miscompiles. The near miss's line is marked `# NEAR`, and the
program starts with `# FM near miss: <kind>`. `DECL_FUZZ_NEAR=1` (or
`=disjoint,reinit`) turns stage 4 on.

| Kind | Construct | Next to the error |
|---|---|---|
| `disjoint` | `g(v.f0, v.f1)`, a `mut` field and another field (`mut` or read), or `v.f1.m(v.f0)` | `alias`: `g(v, v.f0)` |
| `read_alias` | `g(x, x)`, `g(x, x.f)`, `x.m(x)`, all read (not Ints, which are passed by value) | `alias` with a `mut` argument |
| `reinit` | `var y = x^` then, later in the block, `x = e` and a use of x; in a loop, of an outer x in one iteration | `use_moved`, `loop_move` |
| `move_copy` | `g(x^, x.copy())`, `g(x^, x.f)` (an Int field), `S(x^, x.f.copy())`: x moves at the call, after the other arguments are evaluated | `g(x^, x)`, which borrows x: an aliasing error |
| `discard_move` | `_ = x^` then a use of x: Mojo keeps x alive | `use_moved` |

Probes settled each construct (and the errors beside them) before the
generator made any. Two changes to the evaluator follow Mojo:
- An argument `x^` moves x only when the call is made, so arguments
  after it may still read x.
- `_ = x^` leaves x alive.

Neither changes the meaning of a stage 2 program, which never reads x
afterwards.

Waiting for a chance was enough for `reinit` and `discard_move`, but
not for the three that need a call. The calls, the variables and their
types they need seldom meet in a body: at first, 9 to 18% of programs
got the near miss. For those three, a block may build the statement:
`_ = g(...)` with the near miss's two arguments fixed and the others
drawn as usual, none of them using its variable. It picks a function
that isn't generic, a method with a read receiver, or (for `move_copy`)
a constructor, and writes `var vN = e` first if no variable of the type
it needs is there. In 3000 programs (seeds 305 to 309), the number of
each kind that got its near miss, and the number rejected:

| Kind | Made | No chance |
|---|---|---|
| `reinit` | 974 | 268 |
| `discard_move` | 891 | 226 |
| `move_copy` | 790 | 380 |
| `read_alias` | 522 | 730 |
| `disjoint` | 181 | 930 |

`disjoint` needs a struct with two fields of a callee's parameter
types, which few programs declare. Later, its callees grew to include
generic functions (instantiated with each choice of conforming types
from the pool, up to 64, with the type arguments written out) and
methods with a `mut self` receiver, which is then one of the two
fields (`v.f0.m(v.f1)`). That barely changed how often it's made (18%
of 1135 programs, seed 902) but varied the calls: of 60 near misses
(seed 901), 9 called a generic function and 33 a `mut self` method.

**Validation.** The first round, 600 programs of all kinds (seed 743,
nightly), gave one `DIFF_EXPECTED`. It was an evaluator bug, not a near
miss: the evaluator wrapped `100 * 4611686018427387904` in a comparison
of two literal expressions, which Mojo computes exactly (see
"Evaluation"). Stages 1 and 2 had never hit it. With the evaluator
fixed, seed 743 and 600 more (seed 744) gave no differences, and nor
did 300 on 1117 (seed 742). 400 well-typed programs (seeds 223 and 224)
and 600 mutants (seed 632) passed too.

### Findings

**`v = v if c else w` (#7760 again).** On 1117, a `move_copy` program
gave a `DIFF_O3`. The near miss had nothing to do with it: the cause was
`v0 = (v0 if a == a else v0)` on an `ImplicitlyCopyable` struct, the
self-assignment of #7760 through a ternary, which stage 2's `v = v`
workaround didn't catch. Reduced:
- `v = v if c else w` gives garbage at -O3 when `c` is true, as `v = v`
  does.
- `v = v if c else w.copy()` and `v = v if c else P(9, 9)` give the
  other branch's value instead, though `c` is true.
- `v = w if c else v` with `c` false is wrong too.

`v.copy()` in the branch, or a temporary, gives the right value. Both
1117 and 1123 do this. Reported in a
[comment on #7760](https://github.com/modular/modular/issues/7760#issuecomment-7153833750)
(11-24). The generator now copies a branch that is the assigned variable
itself (under the same `DECL_FUZZ_NO_SELF_ASSIGN_WORKAROUND`).

## Paths: errors on some paths only

Stage 2 keeps every variable's state the same on all paths: a block
that moves a variable live at its start reinitializes it at its end, so
after an `if` each variable is either live or moved, whichever branch
ran. Mojo's checker is path-sensitive. After an `if`, a variable can be
initialized on some paths and not others, and a `mut` argument has to
be initialized on every path to the return. Two mutant kinds and three
near-miss kinds test this. They are made by a **plan** that an `if`
draws for one variable, before its branches. In the plan, the branches
either move the variable (it was live), or reinitialize it (it was
moved). They do so in the then branch, the else branch, or both, at a
drawn point in the branch (or wherever a statement of the branch
already does).

Probes on the nightly settled Mojo's rules first:
- A use after an `if` that moved x on only some paths is an error at
  the use ("use of uninitialized value"), as after a move on all paths.
- `x = e` after such an `if` is fine, and so is never using x again.
  Mojo then destroys x at the end of the `if` on the paths that didn't
  move it.
- A field assignment `x.f = e` after such an `if` is an error at the
  move ("cannot be consumed, because 'x.f' is used later"). The plans
  never write one.
- A `mut` argument (or `mut self`) may be moved out (`var y = p0^`)
  if it's reinitialized on every path. Otherwise the error is at the
  `return` ("'p0' is uninitialized at return from this function"),
  or at the `def` line when there is no `return`.
- In a loop, a move on some paths of a variable from outside the loop
  is an error at the move, from the next iteration. Mutant plans are
  made only on variables declared inside the innermost loop body.

| Kind | Construct | Mojo's error |
|---|---|---|
| mutant `maybe_moved` | an `if` moves x in some branches (or reinitializes a moved x in one), then `_use(x)` | use of uninitialized value 'x' |
| mutant `mut_uninit` | a `mut` argument moved out and not reinitialized: in some branches, or after a move and reinitialized in one branch, or not at all; the `return` is marked | 'p0' is uninitialized at return from this function |
| near `maybe_moved` | an `if` moves x (owned or `mut`) in some branches, then perhaps `x = e` and a use; otherwise x is left alone, to be reinitialized later or destroyed on the other paths | |
| near `reinit_paths` | x moved before an `if` that reinitializes it in both branches, or in one and then after the `if`, then a use | |
| near `mut_reinit` | a `mut` argument moved out, then reinitialized on every path: in the same branch, in both branches, after the `if`, or at the end of the body | |

Mutants and near misses on these kinds use `DECL_FUZZ_MUTANTS` and
`DECL_FUZZ_NEAR` as before (`DECL_FUZZ_MUTANTS=maybe_moved,mut_uninit`).
As for the other kinds, a mutant plan isn't made in an `if` with a
constant condition or inside one. The near misses check destruction on
every path through the `Res` ledger: a compiler that destroys a
maybe-moved `Res` on the wrong paths gives `UNBALANCED`.

To give the plans something to reinitialize, these kinds sometimes move
a variable at the start of a statement (an owned one, or a `mut` one
for `mut_uninit` and `mut_reinit`). A plan can also move one itself just
before its `if`, if the condition doesn't use it. A body ends by
reinitializing each `mut` argument that is still moved. That is a
`mut_reinit` near miss, or for `mut_uninit` a chance to leave it moved.
Stage 2 never moves a `mut` argument. In 400 to 1400 programs per kind
(seeds 305 and 306), the share that got the construct:

| Kind | Made |
|---|---|
| near `mut_reinit` | 61% |
| near `maybe_moved` | 54% |
| mutant `mut_uninit` | 43% |
| mutant `maybe_moved` | 40% |
| near `reinit_paths` | 33% |

**Validation.** On the nightly, after the fix below:
- 400 path near misses (seed 502) and 300 path mutants (seed 502) were
  all OK.
- So were 200 stage 2 programs (seed 225), 300 mutants of all kinds
  (seed 633), and 200 near misses of the stage 4 kinds (seed 745).

Before the fix, the first round (seed 501) gave 300 OK mutants, and 9
`BUILD_FAIL`s and 3 `BUILD_CRASH`es among 300 near misses.

The first round showed that a plan can't simply assume its outcome. A
branch ends by reinitializing the variables it moved, and the value it
assigns one of them can move another, even the plan's variable after
the plan reinitialized it (`v2 = v3^`, then `v3 = v2^`). After the `if`,
the generator now takes the state each branch actually left: the
variable is live only if both branches left it live.

### Findings

**An -O3 crash.** Three `mut_reinit` programs of the first round, all
variants of one program, crashed the compiler at -O3 (a segmentation
fault, with no pass named in the backtrace). The near miss had nothing
to do with it: it was in a method no entry point called. Reduced, the
crash needs a method whose `if` condition is known only after inlining
(a call of a function returning `False`), a dead branch that copies a
two-level `ImplicitlyCopyable` struct argument into a local, a live
branch that builds and drops a value with a `__deinit__`, and three
chained calls of the method. -O0 to -O2 are fine. Both 1117 and 1123
crash. Filed as
[#7783](https://github.com/modular/modular/issues/7783). The generator
has no workaround. The crash is rare, and the program it needs is too
specific to avoid.

## Deferred initialization

A variable can be declared without a value (`var x: T`) and assigned
later. Until then it's like a moved variable. Two more kinds test
this, using the same plans as the path kinds: a plan whose `if`
declares x just before it (`PRE_DECL`), and assigns it in the then
branch, the else branch, or both. A `for` loop can also declare x
before it and assign it in its body. A third of the time the
assignment is itself an `if` with an assignment in each branch
(`if c: x = e1 else: x = e2`).

Probes on the nightly:
- After an `if` that assigns x in only some branches, a use is an
  error at the use ("use of uninitialized value 'x'"). Assigning x
  after the `if`, or never using x, is fine. Mojo then destroys x on
  the paths that assigned it.
- An assignment in a loop's body leaves x uninitialized after the
  loop, even with a constant count (`range(3)`). In the body, after
  the assignment, x is initialized, and the next iteration's
  assignment destroys the old value.
- Deferred variables of a type parameter (`var x: T`) and of `Int`
  behave the same.
- A field assignment to a variable without a value (`var x: Q;
  x.f0 = R(1)`) is accepted, and then destroys the fields never set.
  See "Findings" below. The generator assigns fields of live variables
  only.

| Kind | Construct | Mojo's error |
|---|---|---|
| mutant `uninit` | `var x: T`, assigned in one branch of an `if` (or in a loop's body), then `_use(x)` | use of uninitialized value 'x' |
| near `deferred` | `var x: T` (marked), assigned in both branches of an `if` and then used; or in one, then perhaps `x = e` and a use; or in a loop's body, used there, and perhaps assigned and used after the loop | |

`DECL_FUZZ_MUTANTS=uninit` and `DECL_FUZZ_NEAR=deferred` ask for them.
In 200 programs of each (seed 801), 63% of the mutants and 64% of the
near misses got the construct.

**Validation.** On the nightly, 300 `uninit` mutants and 400
`deferred` near misses (seed 811) were all OK. With the same build, so
were 300 mutants and 300 near misses of all kinds (seed 821). Of 200
stage 2 programs (seed 821), one was `UNBALANCED`, which was #7759
through a `mut self` that the workaround didn't cover yet (see stage
2's "Findings").

### Findings

**Field-by-field initialization destroys uninitialized fields.** The
probes found this before the generator did. `var x: Q; x.f0 = R(1)`
is accepted when the other fields are never set. When x goes out of
scope, Mojo destroys every field of Q, including `x.f1`, which was
never initialized (`R.__deinit__` prints garbage; with `List` fields
the program segfaults at -O0). If the struct has a custom
`__deinit__`, it runs on a value no `__init__` built. After `if c: x =
Q(...)` on some paths, a later `x.f0 = R(3)` makes the assignment in
the branch destroy the uninitialized x it replaces first. Mojo does
reject the case where every field is set this way ("used with all
fields manually initialized but without calling an '__init__'
method"). Both 1117 and 1123 do this. Filed as
[#7785](https://github.com/modular/modular/issues/7785).

## Early returns

A branch of an `if` can end with `return e`, of the body's result type.
One `if` in six gets one, in any mode. Before it, the branch
reinitializes every `mut` argument still moved. To the generator, the
branch then doesn't fall through: after the `if`, each variable is as
the other branch left it. The evaluator stops the body at the `return`,
from inside any loops.

Probes on the nightly:
- A `mut` argument still moved at an early `return` is an error at
  that `return` ("'p' is uninitialized at return from this function").
- A variable moved only on the returning path is live after the `if`,
  and so is one assigned only on the other path. One assigned only on
  the returning path is uninitialized after the `if`.
- A statement after a `return` in the same block only gets a warning
  ("unreachable code"). The generator never writes one.

An `if` with a constant condition never returns early: if its live
branch returned, Mojo would drop the code after it, and with it the
errors of a mutant placed there. The path kinds' plans pick the
returning branch so that the mutant stays a mutant: when the plan
moves x in one branch, the other branch may return, and when it
reinitializes x in one branch, that branch may return.

| Kind | Construct | Mojo's error |
|---|---|---|
| mutant `ret_uninit` | an early `return` (marked) with a `mut` argument moved out: moved just before it, or earlier | 'p0' is uninitialized at return from this function |
| near `early_return` | a plan whose returning branch is the one that leaves x moved: x moved in that branch, or reinitialized in the other; then a use of x after the `if` | |

`DECL_FUZZ_MUTANTS=ret_uninit` and `DECL_FUZZ_NEAR=early_return` ask
for them. Both make the early returns more frequent (one `if` in two)
and `mut` arguments more common. `ret_uninit` also gets a chance at
every statement: an `if` (on a condition that isn't constant) whose
branch moves a `mut` argument and returns. In 200 programs of each
(seeds 831 and 851), 70% of the mutants and 45% of the near misses got
the construct, and 10% of stage 2 programs executed an early return.

**Validation.** On the nightly, all OK: 300 `ret_uninit` mutants and
400 `early_return` near misses (seed 841), 300 stage 2 programs (seed
842) and 200 more of seed 821 (the round of the `mut self` form of
#7759, now clean), 400 mutants and 400 near misses of all kinds (seed
843).

## Loops: `while`, `break` and `continue`

A third of the loops are now `while` loops on a counter, a `var`
incremented first, so that a `continue` can't loop forever:

```mojo
var i2 = 0
while i2 < 3:
    i2 = i2 + 1
    ...
```

Inside a loop, the exit that ends a branch of an `if` can also be
`break` or `continue`. Before either, the branch reinitializes every
variable from outside the loop that was live at the start of the body
and has been moved since. The evaluator runs both, and a `while`
loop's counter starts at 1 in the body.

Probes on the nightly:
- A variable moved before a `break` is maybe-moved after the loop: a
  use there is an error at the use, and `x = e` or no use is fine.
- A variable moved before a `continue` (and not reinitialized) is an
  error at the first use the next iteration reaches, which may be the
  move itself. The same holds for a move in a branch of an `if` in the
  loop.
- Reinitializing before the `continue` or `break` is fine, and so is
  a `break` from an inner loop followed by `x = e` in the outer one.

| Kind | Construct | Mojo's error |
|---|---|---|
| mutant `break_moved` | x, from outside the loop (and not used by an enclosing loop), moved before a `break`; `_use(x)` after the loop | use of uninitialized value 'x' |
| mutant `loop_move` (extended) | the loop's move of an outer x can now be `if i == k: var v = x^`, perhaps followed by `continue` | as before, the whole loop is marked |
| near `loop_exit` | x moved (marked) before a `break`, then perhaps `x = e` and a use after the loop; or x moved and reinitialized before a `continue` | |

The mutants that assign or mut-borrow a read variable make no `while`
loops: the counter is a `var`, and would look like a read variable to
them. `break_moved` and `loop_exit` get a chance at every statement of
a loop's body (an `if` on the loop variable whose branch moves x and
exits), and a non-`Int` variable before the loop if it has none. In 200
programs of each (seed 851), 55% of the `break_moved` mutants, 64% of
the `loop_move` mutants and 64% of the `loop_exit` near misses got the
construct.

**Validation.** The first round (seed 861, nightly) gave 300 OK
`loop_move` mutants, 200 OK `ret_uninit` mutants, 300 OK stage 2
programs and 400 OK mutants of all kinds, but 57 `WRONG_LINE`s among
300 `break_moved` mutants and 14 build failures among 400 `loop_exit`
near misses. Both were one generator bug: the variable moved before a
`break` was recorded in the context, and a loop nested in the same
body, drawn after the `break`, took it as its own, so the outer loop
treated it as live after it. Each loop now keeps the outer loop's
record aside while it draws its body. After the fix, 300 `break_moved`
mutants and 400 `loop_exit` near misses (seed 881) were all OK, and so
were 400 near misses of all kinds (seed 882).

## Partial moves and counted structs

A field can be moved out of a variable (`var v = x.f^`). Probes on the
nightly settled the rules:
- The field has to be reassigned (`x.f = e`) on every path before x is
  used whole, before the field is read, and before x's lifetime ends or
  x is assigned whole. Otherwise the error is at the use ("use of
  uninitialized value 'x.f0'"), or at the move ("field 'x.f0' destroyed
  out of the middle of a value, preventing the overall value from being
  destroyed"), or at the `if` whose branches disagree.
- Reading another field in between is fine, and so is reassigning the
  field in both branches of an `if`, in a loop, or for a `mut` argument.
- `^` moves an `ImplicitlyCopyable` field too. A struct with its own
  `__deinit__` allows a partial move if the field is reassigned.
- A `deinit self` method replaces the destructor: the struct's
  `__deinit__` doesn't run, its remaining fields are destroyed.

| Kind | Construct | Mojo's error |
|---|---|---|
| mutant `partial_use` | `var v = x.f^` (marked), then `_use(x)` or `_use(x.f)` (marked) | use of uninitialized value 'x.f' |
| near `partial_move` | `var v = x.f^` (marked), up to two statements that don't use x, `x.f = e` (a third of the time in both branches of an `if`), then a use of x | |

x is a live owned or `mut` variable, and the field isn't an `Int`. The
statements in between don't exit: a `return`, `break` or `continue`
would reassign x whole, which is an error with a field moved out. A
mutant's x is declared in the innermost loop body. Each kind gets a
chance at every statement. In 200 programs of each (seed 871), 50% of
the mutants and 41% of the near misses got the construct.

A third kind, a mutant that never reassigns the field, didn't work.
Mojo reports "destroyed out of the middle of a value" where x would
otherwise have been destroyed, which is often at x's last use before
the move, on another line: 294 of 300 such mutants were `WRONG_LINE`.
And when the field moved is x's only one with a destructor, the rest
of x needs no destruction, so the program is valid: the other 6 were
`ACCEPTED`.

Half of the `Movable` and `Copyable` structs are now **counted**: they
have their own field-wise `__init__`, a copy constructor if they are
`Copyable`, and a `__deinit__`. These call `_born()` and `_died()`,
which keep the same ledger as `Res`, so a struct value destroyed twice
or never gives `UNBALANCED` as a `Res` would. (In the comptime twin
they do nothing.) A struct that a mutant marks isn't counted: its copy
constructor would fail on an unmarked line.

**Validation.** On the nightly, with the workaround below and counted
structs, all OK: 400 `partial_move` near misses (seed 881), 200
`partial_use` mutants (seed 914), 400 `disjoint` near misses (seed
911), 400 stage 2 programs (seed 912), 400 mutants and 400 near misses
of all kinds (seed 913). With the workaround off, 200 `partial_move`
near misses (seed 881) were OK too: counted structs change what a seed
draws, and the nested loop the bug needs is rare (18 in the 400 of the
first round).

### Findings

**A nested loop after a partial move.** The first round of 400
`partial_move` near misses (seed 881) gave 18 build failures, all
"value 'self.f1' cannot be consumed, because 'self' is used later" at
the move, though the field was reassigned before any use. Reduced:

```mojo
var q = Q(R(1), R(2))
var v = q.f0^
for i in range(2):
    for j in range(1):
        pass
q.f0 = R(5)
```

A single loop in between is fine, and so is a loop in an `if` or an
`if` in a loop; a loop nested in a loop (`for` or `while`) is
rejected, for locals, `mut` arguments and `mut self`. Both 1117 and
1123 reject it. Filed as
[#7787](https://github.com/modular/modular/issues/7787). The generator works
around it: a loop drawn while a field is moved out gets no loop inside
it. `DECL_FUZZ_NO_PARTIAL_LOOP_WORKAROUND=1` turns this off.

## An all-kinds campaign

With every kind above in place, a longer run on nightly
1.3.0.dev2026112505, without shrinking: three rounds of 2,000 stage 2
programs, 2,000 near misses of all kinds and 3,000 mutants of all kinds
(seeds 100i, 101i and 102i for round i), 2.5 hours in all.

| Run | Programs | Result |
|---|---|---|
| Stage 2 | 6,000 | all OK |
| Near misses | 3,204 | 3,201 OK; 3 `BUILD_CRASH` at -O3 (round 1); round 3 stopped by a generator error |
| Mutants | 9,000 | 8,992 OK; 8 `ACCEPTED` (round 3) |

A near-miss run stops at its first failure, so rounds 1 and 3 made 562
and 642 programs.

- **The -O3 crashes** are one program, tried three times. Its
  backtrace is the one of
  [#7783](https://github.com/modular/modular/issues/7783), at the same
  place in `mojo`, and it has a method chain like the one in that issue.
- **The accepted mutants** were all `mut_uninit`, in three distinct
  programs, and all valid: a generator bug. The plan's `if` left the
  `mut` argument moved inside a branch of an outer `if`. That branch then
  ended with an early return, which reinitialized the argument before
  the `return`. A block that returns leaves the variables as they were
  before it, so the argument was live at the body's marked `return`.
  Now an early return leaves the mutant's argument moved and is
  marked too, since Mojo reports the error there.
- **The generator error** ("evaluator: read of a moved variable") was a
  `loop_exit` near miss. Before its `continue`, the reinitialization of
  one variable moved another (`S0(p0^, ...)`) that the loop had already
  passed over. For Mojo, `^` on an `Int` is a copy; for the evaluator,
  `p0` was moved, and the code after the loop read it. The
  reinitializations before a `break` or `continue`, and at the end of a
  loop's body, now make no moves.

`DECL_FUZZ_REPRODUCE=<blob>` replays a failure from the `reproduce=`
blob it printed. An evaluator error now prints the program.

**Going on past failures.** The rounds that stopped early did so because
a run ends at its first failure. (The mutant runs only went on because
the wrapper script around the oracle printed `OK` for every verdict; for
the -O3 crash, bash's "Segmentation fault" message got past it on
stderr.) Three changes make a campaign count in full:
- `DECL_FUZZ_LOG=<file>` makes a run a campaign. Each program's
  verdict's first line is appended to the file, and each case that
  isn't OK is kept in `<file>.bad/` with its program and verdict. An
  error in the generator is logged as `GEN_ERROR`, with the program, and
  the run goes on.
- `known_crashes.txt` lists filed crashes, each as an issue, a build (O0,
  O3 or comptime) and a pattern in the build log. The oracles report a
  crash that matches as `KNOWN #<issue> ...`, which isn't a failure, so
  an ordinary run doesn't stop at it either. A campaign keeps those
  cases in `<file>.known/`. A pattern could also match a new bug with
  the same top frames, so the kept cases are worth a look now and then.
  `DECL_FUZZ_NO_KNOWN=1` turns the list off. For now it holds #7783,
  matched on its top frame at -O3.
- The oracles send their own stderr to `oracle_stderr.txt` in the case's
  directory, so only the verdict is printed.

`examples/decl_fuzz/campaign.sh BINARY OUT [ROUNDS]` runs the rounds
above. It writes the logs and kept cases to OUT, and prints each run's
verdict counts. A one-round smoke test on the nightly (60 programs of
each, seed 2000) was all OK. With fake oracles, campaign runs logged
and kept every case, a `KNOWN` verdict didn't stop an ordinary run,
and a generator with the loop fix reverted logged `GEN_ERROR` for the
near_3 program and kept it.

**Validation.** After both fixes, on the same nightly, all OK:
2,000 `mut_uninit` mutants (seed 1023, round 3's mutant seed), 2,000
near misses of all kinds (seed 1013, round 3's near-miss seed), 600
`loop_exit` near misses (seed 1041), 1,000 mutants of all kinds (seed
1042) and 600 stage 2 programs (seed 1043).

## Consuming methods (`deinit self`)

A method can take `deinit self`: it consumes its receiver, and the
struct's `__deinit__` doesn't run for it. Probes on the nightly:
- The receiver must be owned: `x^.m()`, `x.copy().m()` or `S(...).m()`;
  `x.m()` copies x implicitly if the type is `ImplicitlyCopyable`, and is
  an error ("cannot be implicitly copied") otherwise. On a `read`
  argument, `p^.m()` is "cannot transfer out of immutable reference".
- After `x^.m()`, a use of x is "use of uninitialized value 'x'", and
  `x = e` makes it live again. A `mut` argument consumed this way must be
  reassigned before the return. In one call, `h(x.f, x^.m())` and
  `h(x^.m(), x.f)` are both errors, as they are with `x^`.
- In the body, self is like an owned variable: its fields can be
  assigned, mut-borrowed and moved out, and `mut self` methods called.
  A field moved out needn't be reassigned: the remaining fields are
  destroyed at the end. Even `var v = self^` is fine; v is then a value
  like any other, destroyed with the struct's `__deinit__`.
- `deinit self` works in a trait requirement, and a generic function can
  call it (`x^.m()` with `x: T`). In a generic struct, the fields of type
  `T` need `Deinitable` (every FM trait refines it).

FM declares 1/6 of the methods that would take `self` with `deinit
self` instead, both a struct's own methods and trait requirements (with
no default body). A call's receiver is drawn as an owned value, so it is
`x^`, a copy, a new value, or an implicit copy, and the evaluator moves
x for `x^`. In the body, self has the kind of a `mut` argument, so the
generator assigns, borrows and moves it as it would one, and
reinitializes it before each return (not needed, but valid). The
mut_uninit and ret_uninit mutants leave self alone there, since a moved
self isn't an error.

A counted struct's `deinit self` method calls `_died()` before each
return, because its `__deinit__` won't. If Mojo ran both, or neither,
the ledger would be off and `main` would print `UNBALANCED`.

Two near misses do what only a `deinit self` method may, at the end of
its body:

| Kind | Construct | Why it's valid |
|---|---|---|
| near `deinit_drop` | `var v = self.f^` (marked), never reassigned; the return doesn't use self | the rest of self is destroyed field by field |
| near `deinit_move` | `var v = self^` (marked), never reassigned; no `_died()` | v is destroyed with `__deinit__` |

Their mutant counterparts in any other method are the ones of the
partial-moves and paths sections: `partial_drop` (dropped, since Mojo's
line for it is unpredictable) and `mut_uninit`. For these two near
misses, half of the methods take `deinit self`.

In 300 stage 2 programs (seed 3001), 41 evaluated a `deinit self`
call, 990 in all.

**Validation.** The first round gave `UNBALANCED` in 3 of 300 stage 2
programs and 20 of 200 near misses, with more deaths than births. That
was the generator: it decided whether a struct was counted from the
drawn flag alone, while the printer also requires `Movable` or
`Copyable`, so `ImplicitlyCopyable` structs' `deinit self` methods
called `_died()`. After the fix (`is_counted`, used by both), on
nightly 1.3.0.dev2026112505, all OK:
- 300 stage 2 programs, 200 deinit near misses and 300 mutants of all
  kinds (seeds 3002-3004);
- 1,000 stage 2 programs, 1,000 near misses of all kinds, 400 deinit
  near misses and 1,000 mutants of all kinds (seeds 3021-3024).

No compiler bugs so far: Mojo destroyed every consumed value exactly
once, at -O0, at -O3 and at compile time.

## `ref` results and bindings

A method can return a reference, `-> ref[origin] T`, and `ref r = e`
binds a name to a place. Probes on the nightly:
- The origin must be exactly the returned place's: `def get(ref self)
  -> ref[self] Int: return self.f1` is "cannot return reference with
  incompatible origin: 'origin_of(self.f1)' vs 'origin_of(self)'", and
  so is `ref[self.f2]`. `ref[self.f1]` is right.
- With `ref self`, the result is as mutable as the receiver: through a
  `read` argument or a temporary (`S(1, 2).get() = 5`), an assignment is
  "expression must be mutable in assignment", and passing it `mut` is
  "value passed to mutable argument must be mutable".
- A binding is to the place, not to its value. After `ref r = x.get()`,
  `x = S(5, 6)` makes r read 5. If x is moved and then reassigned, r
  reads the new value, even when the move is in a branch. A use of r
  while x is moved is "use of uninitialized value 'x'", and so is an
  assignment through r, though `x = e` would be fine there. If x's
  field `s` is moved out, a binding to `x.s.f1` is "use of uninitialized
  value 'x.s.f1'", and one to another field is fine.
- `r^` and `x.get()^` are "expression does not designate a value with
  an origin": nothing moves through a ref.
- Exclusivity is checked through refs, and precisely: `f(w, t)` with
  `ref t = w.s` (w passed `mut`, t read) is "aliasing values passed
  mutably ... and passed immutably", as `f(w, w.s)` is, and so is
  `f(w, w.s_ref())`. Disjoint fields through two bindings, or two
  accessors, are fine. (Ints passed read are copies, so they never
  alias.)
- Copies are as for the place itself: `var y = r` of a type that isn't
  `ImplicitlyCopyable` is "cannot be implicitly copied", and
  `r.copy()` is fine.
- A read Int argument has no memory: `ref r = a` is "value of type
  'Int' doesn't have a memory origin in 'ref' binding". Read struct
  arguments, even `ImplicitlyCopyable` ones, and loop variables can be
  bound.
- Bindings work in `deinit self` methods, in generic functions and on a
  generic struct's `Self.T` field.

Since a binding names a place, FM treats `ref` as spelling. Half of the
fields have an accessor `def fK_ref(ref self) -> ref[self.fK] T: return
self.fK`, and before each statement of a block there is a 1 in 6 chance
of `ref rN = <place>`, for a place of a live variable (the variable, or
one of its fields). The binding is in scope until the end of its block.
Where the generator would write a place of a live variable, `spell`
may write it another way: `x.fK_ref()`, a binding to the place, or a
binding to x followed by `.fK` or `.fK_ref()`. R_FIELD also uses an
accessor on any receiver, half the time. This applies to reads, copies,
`mut` arguments and receivers, assignment targets, and the near-miss
and mutant places, but not to:
- moves, which go through a ref by name only;
- assignments to a moved variable;
- the paths' reinitializations and uses.

The expression stays a variable or a field to the generator and the
evaluator. So Γ, exclusivity within a statement, the paths and the
evaluator need no change, and the probes show that Mojo agrees: it
checks a use through a ref as a use of the place.

Mutants and near misses then come almost for free. Through a binding to
a moved variable, a use_moved mutant is a ref used after its origin
moved. Through a binding to a read argument, mut_read and assign_read
mutate through an immutable ref. An alias mutant may alias through a
binding. Three new mutants and one near miss cover the rest:

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `ref_origin` | an accessor declared `-> ref[self]`, or another field's origin | cannot return reference with incompatible origin |
| `ref_move` | `rN^`, `rN.fK^` or `x.fK_ref()^` in an owned position | expression does not designate a value with an origin |
| `ref_rvalue` | `T(...).fK_ref() = e` (or a copy's, or `x^`'s) | expression must be mutable in assignment |
| near `ref_reinit` | `ref rN = x` (or `x.fK`), `var v = x^`, `x = e`, then `_use(rN)` | the binding is to the place, which is initialized again |

In 1,000 stage 2 programs (seed 5201), 597 evaluated a place spelled
through a ref, 65,804 in all.

**Validation.** At first, 26 of 60 stage 2 programs failed to build:
`ref rN = a` on read Int arguments (the generator's mistake; see the
last probe). After the fix, on nightly 1.3.0.dev2026112505, all OK:
- 1,000 stage 2 programs, 400 ref_reinit near misses and 600 ref
  mutants (seeds 5201-5203);
- 1,000 near misses and 1,000 mutants of all kinds (seeds 5204-5205).

No compiler bugs so far: through accessors and bindings, Mojo's
initialization, mutability and exclusivity checks matched the
generator's, and every program computed the evaluator's result.

## Value parameters

A struct can take a comptime value, `struct V[n: Int]`; `V[3]` and
`V[4]` are different types. Probes on the nightly:
- Arguments are folded: `V[1 + 2]`, `V[(5 - 2)]` and `V[6 // 2]` are all
  `V[3]`, as an argument, a field's type or a type argument
  (`B[V[2 * 1 + 1]]`).
- Symbolic arguments are canonicalized: in V's body, `V[Self.n + 0]`,
  `V[0 + Self.n]` and `V[Self.n * 1]` are `Self`, and `V[1 + Self.n]` is
  `V[Self.n + 1]`.
- Mismatches are errors: `take3(V[4](1))` with `take3(x: V[3])` is
  "cannot be converted from 'V[Int(4)]' to 'V[Int(3)]'", and returning
  `W[Self.n + 1](...)` as Self is "cannot implicitly convert 'W[(n +
  Int(1))]' value to 'W[n]'".
- `Self.n` and `V[3].n` are Int expressions, also in static methods and
  in associated constants (`comptime K0 = Self.n + (5)`), which a generic
  function reads through `T.K0`.

In FM a quarter of the structs that aren't generic take `[n: Int]`
(three quarters for the value kinds), with one or two values from -2 to
5. Types outside V's bodies are `V[k]` for those values; in its bodies,
Self is `V[Self.n]`. A value is a type of its own kind (VAL), so `V[3]`
is the type `STRUCT V` with argument `VAL 3`, and substitution,
unification and dispatch work as they do for `B[T]`: a call on a `V[3]`
runs V's bodies with `Self.n = 3`. An Int position can be `V[k].n` or
`Self.n` (rule R_VALN), and half of V's associated constants are
`Self.n + (v)`.

The printer writes each value as a marker, which `resolve_values`
replaces, occurrence by occurrence, with an expression equal to it:
`3`, `(1 + 2)`, `(5 - 2)` or `(3 * 1)`. So one program names the same
type several ways, and Mojo has to fold each one to see that they're
the same.

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `value` | `V[k + d](...)` where `V[k]` is expected, or `V[Self.n + d](...)` where Self is (d from 1 to 3) | cannot be converted, or cannot implicitly convert |
| near `value_expr` | Self written `V[e](...)` with e `Self.n + 0`, `0 + Self.n`, `Self.n * 1`, `1 * Self.n`, `Self.n - 0`, `(Self.n + 2) - 2` or `2 + Self.n - 2` | e is canonicalized to `Self.n` |

In 1,000 stage 2 programs (seed 6201), 300 read a value parameter,
144,999 times in all.

**Validation.** On nightly 1.3.0.dev2026112505 the results were:
- 1,000 stage 2 programs, 400 value mutants, and 1,000 near misses and
  1,000 mutants of all kinds (seeds 6201, 6203-6205): all OK;
- 400 value_expr near misses (seed 6202): 398 OK, and 2
  `DIFF_COMPTIME` (the same program twice).

**Found: a compile-time Int loses its upper 32 bits** (filed as
[#7798](https://github.com/modular/modular/issues/7798)). In that
program, `run_f1(-3, 0, 17)` printed 4611686027017322496 at compile time
instead of 4611686018427387904: two fields that held `a = -3` read as
4294967293 (0xFFFFFFFD). The trigger was an uncalled function, `run_f0`,
with the condition `(9223372036854775807 * V0[(3 * 1)].n) !=
V0[(1 + 2)].K0`. Reduced by hand to 20 lines, with no value parameter
left:

```mojo
struct S(Copyable):
    var x: Int

    def __init__(out self, var x: Int):
        self.x = x


comptime N: Int = 3


def unused() -> Int:
    if (9223372036854775807 * N) != 11:
        return 1
    return 0


def f(a: Int) -> Int:
    return S(a).x


def main():
    comptime k = f(-3)
    print(k, f(-3))  # 4294967293 -3
```

The wrapped product, 0x7FFFFFFFFFFFFFFD, has the low 32 bits of -3. With
`N = 5`, `f(-5)` is the one that's wrong. `N = 2`, `< 0` instead of
`!= 11`, returning the product instead of comparing it,
`@fieldwise_init` instead of the explicit `__init__`, or removing
`unused` or `S` each make it right. Nightly 1117 has it too. The value
parameters only brought the overflowing product into a condition that
folds.

### On functions, and arithmetic

Functions take value parameters too, next to type parameters, and
types can do arithmetic on them. Probes on the nightly:
- `def h[n: Int](p0: V[n], p1: V[n]) -> Int` infers n from its
  arguments: `h(V[3](1), V[(1 + 2)](2))` is fine, and `h(V[3](1),
  V[4](2))` is "cannot be converted from 'V[Int(4)]' to 'V[Int(3)]'". So
  is an explicit `h[4](V[3](1), ...)`.
- `def g[T: Tr0, n: Int](p0: T, p1: V[n]) -> V[n]` mixes the two kinds.
- A result can be `V[n + 1]`: `succ(succ(V[1](0)))` is a `V[3]`, and a
  method `-> V[Self.n + 1]` chains (`V[3](7).up().up()` is a `V[5]`).
  `V[1 + n + 1]` and `V[(n + 1) + 1]` are the same type.
- A parameter `p0: V[n + 0]` (or `V[n * 1]`) still lets Mojo infer n, but
  `p0: V[n + 1]` doesn't: "it depends on an unresolved parameter 'n'".

In FM a third of the functions (two thirds for the value kinds) have a
value parameter `n` over one struct V with one, at position 0 or 1 of
their parameters; its first argument has type `V[n]`, from which Mojo
infers it. Their signatures and bodies draw from `V[n]`, `V[n + 1]` and
`V[n - 1]` as well as the usual types, and so do V's own methods and
bodies, with `Self.n`. A new type kind OFF is `n + c`: substituting a
value k for n gives `V[k + c]`, and substituting another parameter m
(the caller's) gives `V[m + c]`, folded (`(m - 1) + 1` is m). To call a
function for a wanted result `V[n + 1]` in a context where that's
`V[k]`, unification solves n = k - 1; where it's `V[m]`, n = m - 1, so
the argument is a `V[m - 1]` and Mojo must see that the result `V[(m -
1) + 1]` is `V[m]`. Where nothing fixes n, it's drawn from the
arguments of V in the context's pool. A second value of a struct is
often a neighbor of the first, so that results `V[k + 1]` are wanted.

`n + c` is printed `n + c`, `c + n`, `(n + a) + (c - a)` or `n - (-c)`,
drawn per occurrence, and Int positions can read `n`, `(n + 1)` or
`V[n + 1].n`. A call prints its parameters explicitly half the time
(`g0[(1 + 2), S1](...)`).

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `value` | also `V[n + d](...)` where `V[n]` is expected, and a call with another value explicitly, `g0[4](V[3](...))` or `g0[n + 1](p0)` | cannot be converted |
| near `value_expr` | also, anywhere `V[n]` or `V[Self.n]` is written (signatures too, including the parameter n is inferred from): `V[n * 1]`, `V[2 + n - 2]`, ... | canonicalized to n |

A function gets a value parameter only when some struct has one, so in
1,000 stage 2 programs (seed 7211) 61 called one while running, 1,643
times in all; for the value kinds, struct and function odds are higher.
In 400 value mutants (seed 7223), 68 were an explicit call.

**Validation.** On nightly 1.3.0.dev2026112505 everything was OK: 2,200
stage 2 programs, 1,000 value_expr near misses and 1,000 value mutants
(seeds 7201-7203, 7211-7213, 7221-7223), and 1,000 near misses and 1,000
mutants of all kinds (seeds 7214, 7215). No new compiler bug: Mojo
folded every `(m - 1) + 1`, and inferred every n.

## Generic methods

A method can have type parameters of its own, in a trait or a struct:
`def m1[U: Tr0](self, p0: U, p1: Int) -> U`. Probes on the nightly:
- Calls infer U from the arguments (`s.m1(S0(1), 2)`) or write it
  (`s.m1[S0](S0(1), 2)`), also through a type parameter (`x.m1[S0](...)`
  with `x: T`, `T: Tr1`), and at compile time.
- A struct's implementation of a generic trait method must repeat the
  bound exactly. A stricter bound (`U: Tr2` for `U: Tr0`, Tr2 refining
  Tr0) or a looser one is "'S0' does not implement all requirements for
  'Tr1'". Renaming the parameter (`[V: Tr0]`) is fine.
- A type argument that doesn't conform is "'m1' parameter 'U' has 'Tr0'
  type, but value has type 'AnyStruct[B[S0]]'".

In FM a quarter of the methods that aren't static, in traits and structs
(half for the rename near miss), take `[U: TrN]` with any trait N. U is
PARAM 1 in every context: in a trait, PARAM 0 is Self; in a generic
struct, `Self.T`; in a struct with a value parameter, `Self.n`; in other
structs PARAM 0 is unused (its bound is -1, like a value parameter's,
so the pool leaves it out). The first parameter has type U, so that
Mojo can infer it, and the other parameters and the result are often U
too. Parameters whose types mention U are never `mut`.

A call's U comes from the result type wanted. The method's signature,
instantiated for the receiver, has a new kind HOLE where U is, and
`match_hole` matches it against the type wanted (everything else in the
signature is fixed, unlike in `unify`, where a function's parameters are
variables). If nothing fixes U it's drawn from the types that conform to
the bound. The call writes `[U]` half the time, and always when a mutant
changed an argument's type. The evaluator adds U to the callee's type
arguments (`[Self, U]`, `[T, U]`, or `[_, U]`).

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `bound` | also `x.m[X](...)` with X not conforming to m's bound | parameter 'U' has 'TrN' type, but value has type |
| `sig` | also an implementation of a generic method with another trait as its bound | does not implement all requirements |
| near `rename` | an implementation of a generic trait method names its parameter W | the name isn't part of the signature |

In 1,000 stage 2 programs (seed 7311), 139 called a generic method
while running, 8,580 times in all. Of 200 sig mutants, 21 were on a
generic method, and of 200 bound mutants, 43 (seed 7303).

**Validation.** On nightly 1.3.0.dev2026112505 everything was OK: 1,300
stage 2 programs, 600 rename near misses, 200 sig, 200 bound and 400
bound-or-sig mutants (seeds 7301-7304, 7311, 7312, 7316), and 1,000 near
misses and 1,000 mutants of all kinds (seeds 7314, 7315). No new
compiler bug.

## Conditional conformance

A generic struct can conform to a trait only for some type arguments:
`struct B[T: Tr0](Tr0, Tr1 where conforms_to(T, Tr2))`. Probes on the
nightly:
- `B[A]` conforms to Tr1 when A conforms to Tr2, also through a
  refinement, and in a generic context when T's bound refines Tr2 (Mojo
  proves it from the bound). Tr1's defaults then apply to `B[A]`.
- `B[C]` with C not conforming to Tr2 doesn't: passing it for a `T: Tr1`
  is "argument type 'B[C]' does not conform to trait 'Tr1'", and so is
  `B[T]` with T's bound not implying Tr2.
- The methods only Tr1 needs may be gated by the same condition, `def
  m1(self) -> Int where conforms_to(Self.T, Tr2)`, or not (then their
  bodies can't use it). Calling a gated method on `B[C]` is "violated
  constraint", or in a generic context "lacking evidence to prove
  correctness". A stricter condition on the method than on the
  conformance is "'B[T]' does not implement all requirements for 'Tr1'".
- Tr1's parents need implementations too, gated as well; a constant
  (`comptime K1 = 9`) needs no condition. A missing implementation or
  constant is reported at the struct even if nothing uses it.
- In the struct's header the condition names `T`; `Self.T` is "'Self'
  type is not available in this context".
- A function can have conditions too, `def w[T: Tr0, U: Tr0](x: T, y: U)
  -> Int where conforms_to(T, Tr1) and conforms_to(U, Tr2)`, joined with
  `and` (a comma is a syntax error), and its body can use them. A call
  that fails one is "violated constraint".

In FM a third of the generic structs (all of them for the where kinds,
which also make more structs generic and give them fewer unconditional
traits) get one conditional conformance, to a trait not already implied
by their unconditional ones, with a condition the bound usually doesn't
imply. They implement the methods of that trait and its parents that
their other conformances don't need, gated (half the time, always for
the where kinds) by the same condition. A quarter of the type
parameters of functions (half for the where kinds) get a `where
conforms_to(T, TrN)` with a trait the bound doesn't imply.

A body with a `where` (a gated implementation's, or a function's) uses
its condition: while it's drawn, `Program.facts` holds "PARAM p conforms
to TrN", which `conforms` consults besides the bound, so T values get
the condition trait's methods, static methods and constants, and
`B2[T]` types whose bound only the condition gives. That also keeps the
where mutant honest: inside a gated method, a gated call on `self`
isn't a violation (a first version counted it as one, and Mojo rightly
accepted those 7 "mutants"). A gated implementation whose signature has
Self as a type argument (`-> B2[Self]`, with Self substituted by
`B[Self.T]`) needs the condition to be well formed, so it always prints
its `where`.

`conforms(B[X], t)` is true if an unconditional conformance gives t, or
if the conditional one does and `conforms(X, Y)`; for X a type parameter
that's whether its bound refines Y, as Mojo proves it. Everything that
draws a type or a method goes through `conforms` and `methods_on`, so a
gated method is only called on receivers whose condition holds, and a
function's type arguments are drawn from the types that meet both its
bound and its `where`.

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `where` | a gated method called on `B[X]` with X failing the condition; `B[X]` (explicitly) as the type argument of a function or generic method whose bound only the conditional conformance would give; a type argument meeting a function's bound but not its `where`. Never in a ternary's branch or a constant `if` (Mojo drops a dead branch before checking constraints: 2 of 400 were accepted there) | violated constraint, lacking evidence, or does not conform |
| `where_impl` | a gated implementation of a required method, with a condition on a trait refining the conformance's (and not implied by the bound) | does not implement all requirements |
| near `where` | a gated method called on `B[X]` with X meeting the condition (half the time, a condition the bound implies) | the condition holds |

**Found: Mojo gives T a refined type under a `where` that it doesn't
identify with T** (filed as
[#7811](https://github.com/modular/modular/issues/7811)).
The first stage 2 and near miss rounds failed to build with "cannot
implicitly convert 'T(Tr3)' value to 'T(Tr3)'". Reduced, in `def f[T:
Tr0](p: T) -> Int where conforms_to(T, Tr1)`:
- `B[T](p)`, an implicit copy into a struct's constructor, is "cannot
  implicitly convert 'T(Tr1)' value to 'T(Tr1)'" (`B(p)`, `B[T](p.copy())`
  and `take(p)` are fine);
- `p if True else b.f0` is "ambiguous merge: left value has type 'T(Tr1)'
  and right value has type 'T'";
- `T.make1(1) if True else T.make1(2)`, with make1 a static method of
  Tr1, is "'Tr0' value has no attribute 'make1'", as if the second
  branch were checked without the `where`; so is an Int ternary `1 if
  True else T.make1(2).m()`.

The same happens in gated methods. The first is on 1117 too; the
ternaries compile on 1117, so they're a regression in 2026112505
(still there in 2026112605). The
workaround (`where_workaround`; DECL_FUZZ_NO_WHERE_WORKAROUND=1
disables it) draws no ternaries in bodies with a `where`, and passes
variables and fields whose types mention a type parameter with
`.copy()` there, to constructors and to every non-`mut` argument (the
generated programs also hit it through ref accessors in calls with
explicit type arguments, `g1[Self.T](self.f0_ref())`).

Two more generator bugs showed up as accepted mutants: an
implicit_copy mutant that the workaround's `.copy()` undid (it now
leaves marked expressions alone), and one that wasn't a mutant at all,
an implicit copy of a T whose bound is only `Copyable` but whose `where`
trait is `ImplicitlyCopyable` (`cap_of` now consults the facts too).

In 1,000 stage 2 programs (seed 7442), 15 called a gated method or a
function with a `where` while running, 2,220 times in all; the where
kinds make most of these constructs. With the final generator, on
nightly 1.3.0.dev2026112505, everything was OK: 1,000 stage 2 programs,
400 where near misses, 400 where, 267 where_impl and 300
implicit_copy-or-where mutants, and 1,000 near misses and 1,000 mutants
of all kinds (seeds 7436, 7441-7446). Without the workaround, 34 of 100
where near misses failed to build (seed 7437).

## Associated types

A trait can require a type, `comptime E0: Tr1`, and use it in its
signatures as `Self.E0`. Probes on the nightly:
- A struct binds it with `comptime E0 = A` (or `Self.T`, or `Self`); its
  implementations can write either `A` or `Self.E0`, and `S.E0(3)` and
  `var z: S.E0` work outside it.
- Generic code uses `T.E0` as a type (`def g[T: Tr0](x: T) -> T.E0`,
  `y: T.E0`), with Tr1's methods, static methods and constants
  (`T.E0.make1(3)`, `T.E0.K1`), at compile time too.
- A binding that doesn't conform to the bound (`comptime E0 = Int`, or a
  struct without Tr1), or a missing one, is "'S' does not implement all
  requirements for 'Tr0'". `T.E0` where T is wanted is "cannot implicitly
  convert 'T.E0' value to 'T'"; a C passed for `y: T.E0` with T = S is
  "cannot be converted from 'C' to 'S.E0'".

In FM a third of the traits (two thirds for the assoc kinds) declare
`comptime E<t>: TrU`, with any trait as the bound. A new type kind ASSOC
is `X.E<t>`, and `assoc(t, X)` normalizes it: for a struct X, it's X's
binding (substituted for a generic struct's argument), so `B[A].E0` and
`A` are the same type id; for a type parameter (or HOLE) it stays
symbolic. Substitution goes through `assoc`, so a trait method's
`Self.E0` becomes the binding for a receiver, and `T.E0` in a generic
function becomes the binding of the type argument. An ASSOC type
conforms to its bound's refinements, has the bound's capability, and has
no fields, so it's used like a type parameter: through the bound's
methods, makes and constants, never `X.E0(...)`. The pool of a context
holds `T.E<x>` for each type parameter T and each trait x its bound
implies that has one; signatures, fields of generic structs
(`Self.T.E0`) and bodies draw from it.

After the struct headers, each struct binds the associated types of
every trait it conforms to (conditionally too), to a type of its pool
that conforms to the bound, Self included. A struct with no such type
gives up the conformances that need it, repeated until nothing changes
(giving one up can leave another struct without candidates), and its
constants for those traits. A call of a function with result `T.E0`
can't infer T from the result type: unification records the pair, and
`call_assignment` takes the first T allowed whose E0 is the type wanted
(Mojo then infers T from the arguments).

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `assoc` | a struct binding E<t> to a concrete type that doesn't conform to the bound | does not implement all requirements |
| `missing` | also a binding left out | does not implement all requirements |
| near `assoc` | one struct writes one of its bindings as `Self.E<t>` in its signatures, fields and bodies | it's the same type |

Three generator bugs showed up on the way:
- Dropping a conformance in the binding pass could leave a field type
  drawn earlier ill formed (`B0[S2]` with S2 no longer conforming to
  B0's bound): 5 BUILD_FAILs and 2 evaluator errors. Such programs are
  now discarded.
- A missing mutant that left out a binding named by an implementation's
  signature (`-> Self.E0`) made Mojo stop at "'V1[n]' value has no
  attribute 'E0'" on that line, before reporting the struct: it now
  leaves out only bindings no signature names.
- A near miss whose alias was never printed wasn't one; such programs are
  discarded.

In 1,000 stage 2 programs (seed 7511), 565 declare an associated type
and 310 write one (`T.E0`, `Self.T.E0`, `Self.E0`), but only 14 call a
method, a make or a constant through one while running, 568 times in
all.

**Validation.** On nightly 1.3.0.dev2026112605 everything was OK, over
the last three versions of the generator (each fixing one of the bugs
above): 1,900 stage 2 programs, 700 assoc near misses, 400 assoc, 900
missing, 600 assoc-or-missing and 300 missing-or-type mutants, and
1,000 near misses and 1,000 mutants of all kinds (seeds 7511-7516,
7521-7523, 7531, 7532). No new compiler bug.

**Found later: a stack overflow on a nested recursive binding** (filed
as [#7814](https://github.com/modular/modular/issues/7814)). In the exceptions
step's rounds, 5 maybe_moved near misses (without any `try`) crashed the
compiler after parsing, with 256 frames cycling through the same
addresses. Reduced: `struct B1[T: Tr0](ImplicitlyCopyable, Tr0)` with a
field `var f1: Self.T.E0` and `comptime E0 = B1[B1[Self.T.E0]]` (one
level, `B1[Self.T.E0]`, compiles), on 1117, 1125 and 1126. The
workaround: a binding doesn't nest its own struct twice around an
associated type (DECL_FUZZ_NO_ASSOC_NEST_WORKAROUND=1 disables it).

## Value parameters on methods

Like a generic method's `U`, a method's own value parameter `[k: Int]`
is PARAM 1 (`k`, so it can't clash with a struct's `n`), and its first
parameter is `V[k]`, from which Mojo infers it. Signatures and bodies
also use `V[k + 1]` and `V[k - 1]`; `match_hole` solves `k + c = ty`
for the result type wanted. A call writes `x.m[k]` half the time, and
the value mutant also gives one explicitly another value. An eighth of
the methods take one (more for the value kinds) when some struct has a
value parameter. Validation on nightly 1.3.0.dev2026112605: 300 stage 2
programs, 300 value_expr near misses, 300 value mutants and 200 rename
near misses, all OK (seeds 7601-7604). One generator bug on the way: a
value method's `k` made `sig_text` mark its signature as a rename near
miss.

## Exceptions: typed `raises` and multiple `except` clauses

The nightly changelog adds experimental typed errors: `def f() raises
E1 -> Int`, and `try` blocks with several typed handlers, `except E1
__as e:`, then perhaps an untyped one. Probes on 2026112605 (1117 doesn't
parse `__as`):
- The first handler whose type matches runs; nested `try`s, `else`,
  `finally`, `continue`/`break` in handlers, re-raising `e^` and moving
  `e` out all agree at -O0, -O3 and compile time, and error values with
  destructors are destroyed exactly once.
- A typed `try` must be exhaustive, even in a function that could let
  the error propagate (`raises E2`), and even when an outer `try` would
  catch it: "unhandled error types in try body: 'E2'". A handler for a
  type the body doesn't raise, a duplicate, or anything after `except:`
  is "unreachable 'except' clause" (a warning).
- Error types needn't be Writable, except to become an `Error`: an
  untyped `raises` function lets an E1 out as an Error (which only an
  untyped handler catches), and that needs E1 Writable ("cannot
  implicitly convert 'X0' value to 'Error'").
- A function that `raises E2` can't raise or propagate an E1: "cannot
  implicitly convert 'E1' value to 'E2'". A `mut` argument must be
  initialized at every raise point, and what the callee did to it before
  raising stays.

In FM, error types X0 and X1 are counted structs (`_born`/`_died`, so the
ledger checks that every error is destroyed once) with one field `code`.
A new type kind ERR is the type of a handler's binding; it's in no pool.
Half of the functions raise (none for the kinds that move `mut`
arguments, which a raise would leave uninitialized), `raises` or `raises
Xk`, and their bodies get `if c: raise Xk(e)` statements. A raising call
goes only where its error goes somewhere (`raise_ok`): a `try` body, or
a function raising Error or the same Xk, and not where a field is moved
out (unless a `try` begun inside that region catches it). A `try`
statement freezes the variables from outside it (read-only: a raise can
come anywhere, so a move would leave them maybe moved), and its body may
also `raise` directly. Its handlers cover exactly the types the body
raised (`Ctx.raised`): typed handlers in a random order, then `except:`
for the rest (at least one, and always for Error). A `try` whose body
raises nothing is printed as its statements.

The evaluator raises an Error "RAISE" (with `err_type`, `err_value`):
`call` writes `mut` arguments back first, and retypes the error as Error
when it leaves a `raises` function; `S_TRY` runs the first matching
handler with the error bound.

| Kind | Construct | Mojo's error, or why it's valid |
|---|---|---|
| `unhandled` | a `try` with typed handlers only, one left out | unhandled error types in try body |
| `raise_ctx` | a call of a raising function where nothing catches it | cannot call function that may raise in a context that cannot raise, or cannot implicitly convert |
| `raise_type` | `raise Xj(...)` in a function that `raises Xk` | cannot implicitly convert 'X1' value to 'X0' |
| near `unreachable` | a handler for a type caught before, or not raised, or after `except:` (body `pass`) | a warning only |

**Found: an unreachable handler can't use anything** (filed as
[#7812](https://github.com/modular/modular/issues/7812)). A handler
Mojo warns is unreachable, whose body uses its binding `e` or a local
variable from before the `try`, is rejected with "use of uninitialized
value". The generator hit it with a bare `except:` after handlers for
every raised type, and with a `try` whose body raised nothing. The
workaround: a bare handler always catches at least one type, a `try`
needs a raising body, and the near miss's handler is `pass`
(DECL_FUZZ_NO_UNREACHABLE_WORKAROUND=1 lets it use its binding).

**Found: a compiler crash on a `try` with a raising call in a dead
branch** (filed as
[#7813](https://github.com/modular/modular/issues/7813)). The
compiler segfaults ("Crash parsing statement" at the `try`, in
`mlir::Attribute::getContext`) when a `try` body's raising call is in an
`if False:` (or `if 1 != 1:`, or the `else` of `if True:`) and another
statement follows. Plain `raises` and `except e:` crash too, on 1125 and
1126 but not 1117: a regression. Reduced from 9 crashes in the first
rounds (valid programs and mutants) with a statement-level reducer
(scratchpad `red/reduce.py`, which also needs the crash to come without
errors, or it reduces to a broken program). The workaround: no raising
calls in a constant `if` or a ternary's branch inside a `try`
(DECL_FUZZ_NO_DEAD_RAISE_WORKAROUND=1 disables it).

In 1,000 stage 2 programs (seed 7771), 184 raise and catch while
running: 961 `raise` statements executed and 955 handlers run (a raise
whose code expression raises first counts, but isn't the one caught).

**Validation.** With the final generator on nightly 1.3.0.dev2026112605
everything was OK: 1,000 stage 2 programs, 2,600 near misses and 1,000
mutants of all kinds, 300 unreachable and 300 assoc near misses, and 400
unhandled-raise_ctx-raise_type mutants (seeds 7762, 7771-7776). Without
the dead-raise workaround, 100 stage 2 programs were OK too (seed 7756,
an earlier version): the crash needs a raise point in a constant branch
followed by a statement, which the stage 2 odds rarely make.

Generator bugs found on the way: X0 and X1 weren't Writable; a `try`
printed as a group kept its locals in the evaluator's frame (variable
slots shifted: an evaluator crash, and DIFF_EXPECTEDs); an empty group
printed `pass` (not allowed alone in a block, nor in a trait method
with a result); the evaluator kept an error's type through a `raises`
function (a DIFF_EXPECTED: Mojo was right); raising calls between a
partial move and the field's reassignment, including in the
reassignment's value.

## Beyond the paths

Mojo features FM leaves out for now:
- **More ownership:** functions returning a union of origins
  (`-> ref[a, b] T`), where the place depends on a value; `mut self`
  accessors; refs stored in structs (`Pointer`, `Span`).
- **Overloading and `@implicit` conversions:** Mojo's resolution rules
  aren't fully specified, so the evaluator would have to restrict itself
  to unambiguous overload sets.
- **More of the type system:** retroactive conformance with
  `__extension` (e.g. `Int` to a trait), `where` on value parameters
  (`where n > 0`), associated types of associated types (`T.E0.E1`) and
  constraints on them (`where T.E0 == A`), value parameters on methods,
  methods with two parameters of their own, parameters not inferable at
  all (`p0: V[n + 1]` needs an explicit n), and keyword and default
  arguments.
- **`Variant` and `isa`:** the counterpart of FJ's downcasts.
