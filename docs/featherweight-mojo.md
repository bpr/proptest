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
and generic functions over trait bounds. Like FJ, it is purely
functional. Every program terminates.

This is stage 1. Stage 2 adds ownership (`var`/`mut` arguments, moves
with `^`, `ref` results). Stage 3 adds programs made ill-typed on
purpose, which the compiler must reject without crashing. See "Beyond
stage 1" at the end.

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

## Beyond stage 1

Mojo features FM leaves out for now:
- **Ownership (stage 2):** `var` and `mut` arguments, moves with `^`
  (Γ loses the variable), partial moves of fields, `ref` results and
  origins, and non-`ImplicitlyCopyable` types with `.copy()`. Γ then
  needs an init state and live loans per variable, as in Midtgaard et
  al., *Effect-driven QuickChecking of compilers* (ICFP 2017).
- **Ill-typed mutants (stage 3):** use after `^`, an argument of the
  wrong type, a missing required method, overlapping `mut` borrows. The
  compiler must reject each one and must not crash.
- **Overloading and `@implicit` conversions:** Mojo's resolution rules
  aren't fully specified, so the evaluator would have to restrict itself
  to unambiguous overload sets.
- **More of the type system:** retroactive conformance with
  `__extension` (e.g. `Int` to a trait), conditional conformance
  (`where` clauses), associated types, generic methods, `comptime` value
  parameters (`struct B[n: Int]`), and keyword and default arguments.
- **`Variant` and `isa`:** the counterpart of FJ's downcasts.
