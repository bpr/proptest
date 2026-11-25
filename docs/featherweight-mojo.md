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

**Validation.** After both fixes, on the same nightly, all OK:
2,000 `mut_uninit` mutants (seed 1023, round 3's mutant seed), 2,000
near misses of all kinds (seed 1013, round 3's near-miss seed), 600
`loop_exit` near misses (seed 1041), 1,000 mutants of all kinds (seed
1042) and 600 stage 2 programs (seed 1043).

## Beyond the paths

Mojo features FM leaves out for now:
- **More ownership:** `ref` results and origins, and `deinit`
  (consuming) methods.
- **Overloading and `@implicit` conversions:** Mojo's resolution rules
  aren't fully specified, so the evaluator would have to restrict itself
  to unambiguous overload sets.
- **More of the type system:** retroactive conformance with
  `__extension` (e.g. `Int` to a trait), conditional conformance
  (`where` clauses), associated types, generic methods, `comptime` value
  parameters (`struct B[n: Int]`), and keyword and default arguments.
- **`Variant` and `isa`:** the counterpart of FJ's downcasts.
