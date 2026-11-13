# Differences from Hypothesis

proptest follows the design of Hypothesis's current engine closely: the
same choice types and constraints, the same simplicity order, the same
generation distributions and shrink passes. This document lists where it
differs and what it leaves out, and for each one says **why**: a Mojo
language limit, a missing library, a judgment about cost and benefit, or
simply time. It ends with a list of what would be practical to port next,
and of what has been ported since the first version of this document.

The facts about Mojo here were checked against Mojo 1.3.0.dev2026110505
(the version `pixi.toml` currently resolves to). Several of them are
limitations of a young language that may well be lifted; where so, the
section says what the port would look like afterwards.

Contents:

1. [Differences in the API](#1-differences-in-the-api)
2. [Differences in the engine](#2-differences-in-the-engine)
3. [Features not ported, or ported with changes](#3-features-not-ported-or-ported-with-changes)
4. [What is practical to port](#4-what-is-practical-to-port)

---

## 1. Differences in the API

### 1.1 Combinators are free functions: `map(s, f)`, not `s.map(f)`

**What.** `map`, `filter` and `flatmap` are free functions taking the
strategy as their first argument.

**Why.** The natural place for them is a default method on the `Strategy`
trait:

```mojo
trait Strategy(Deinitable, Movable):
    comptime Value: Copyable & Writable & Deinitable
    def do_draw(self, mut data: ConjectureData) raises -> Self.Value: ...

    def map[R: Copyable & Writable & Deinitable,
            F: (def(Self.Value) -> R) & Copyable](self, f: F) -> Mapped[Self, R, F]:
        return Mapped[Self, R, F](self.copy(), f)
```

The trait itself compiles, but no struct can then conform to it. For
`struct Ints(Strategy)` with `comptime Value = Int` the compiler reports:

```
error: 'Ints' does not implement all requirements for 'Strategy'
note: no 'map' candidates have type
  'def[R: ..., F: def(Int) -> R & Copyable](self: Ints, f: F) thin -> Mapped[Ints, R, F]'
note: candidate declared here with type
  'def[R: ..., F: def(_Self.Value) -> R & Copyable](self: Ints, f: F) thin -> Mapped[Ints, R, F]'
```

When the compiler checks that the struct satisfies the trait, it
substitutes `Int` for `Self.Value` in the expected signature but not in the
synthesized default method (which still says `_Self.Value`), and the two
closure types no longer match. Spelling the parameter as `Some[...]`
instead of a named type parameter fails the same way. It is a compiler bug
in how associated types are substituted inside closure types in default
trait methods; ordinary default methods (`label()`, for example) work.

**What a fix would allow.** Once that is fixed, `map`, `filter` and
`flatmap` can move onto the trait unchanged, keeping the free functions as
aliases. Nothing else in the design depends on this.

A related constraint shapes the combinator structs: a closure is only
`Copyable` if it captures with `{var^}`, and a `Copyable` bound on a
closure type parameter is not checked until instantiation (a lambda passes
`F: ... & Copyable` and then fails deep inside the generic code). So the
combinators take `var f: F` and are `Copyable` only `where conforms_to(F,
Copyable)`, rather than requiring copyable functions.

### 1.2 State machine rules are numbered

**What.** A `StateMachine` declares `rule_count()`, `rule_name(i)`,
`precondition(i)` and `run_rule(i, data)` and dispatches on the rule
number, where Hypothesis collects methods decorated with `@rule`,
`@precondition`, `@invariant` and `@initialize`.

**Why.** Two missing language features:

- **No user-defined decorators.** Mojo's decorators (`@fieldwise_init`,
  `@always_inline`, ...) are built into the compiler; a library cannot
  define `@rule`.
- **No method reflection.** `std.reflection.reflect[T]` can list a struct's
  *fields* (`field_names()`, `field_types()`, `field_ref`), but not its
  methods, so there is no way to find "every method marked as a rule" even
  by naming convention.

Rule *arguments* are drawn inside the rule body with `data.draw(s, "name")`
rather than declared as `@rule(x=integers())` for the same reason; this is
equivalent to Hypothesis's `st.data()` inside a rule, and the labels are
what appear in the printed steps.

**What a fix would allow.** With method reflection (even just "all methods
whose name starts with `rule_`"), `run_state_machine_as_test` could
generate the dispatch itself. Decorators would allow the Hypothesis API
almost verbatim.

**The typed alternative.** `TypedStateMachine` (from Rust's
proptest-state-machine) sidesteps the problem: a step is a value of an
associated `Transition` type (typically a `Variant` of one struct per
operation), drawn by `transition(data)` from the current state and
applied by `apply(t)`. Rules have no numbers or names; the report prints
each transition through `Writable` (`state.apply(Push(x=0))`). It differs
from Hypothesis's rules in three ways: there are no bundles or
initialize rules (keep values in the machine, and set up in `__init__`);
there is no swarm testing, since transitions have no rule index to
disable; and when `precondition` rejects three transitions in a row the
program ends at that step instead of the test case being discarded,
because only `transition` knows how to draw a valid one.

**Model-based commands.** `Command` (`commands.mojo`) is not in
Hypothesis. It follows RapidCheck's `rc::state` and Erlang QuickCheck:
each operation is a struct with its own `generate`, `precondition`,
`next_state` (on the model) and `run` (on the system under test, given
the model's prior state). `commands[C1, ..., Cn](model)` is a strategy for
whole programs generated from the model alone, run inside an ordinary
property. Programs are encoded like `lists()`, with a rejected
precondition handled as a rejected element, so they shrink like lists.
RapidCheck re-checks preconditions during shrinking. Here the later
commands are regenerated from the same choices in the new model state
instead, so a shrunk program is always valid.

### 1.3 `note`, `event`, `target` and `assume` with data are methods on `ConjectureData`

**What.** Hypothesis's `note(...)`, `event(...)` and `target(...)` are free
functions that find the current test case through a context variable. In
proptest they are methods of the `ConjectureData` passed to `given_data`
tests, composite strategies and stateful rules. (`assume` needs no context:
it raises a marker error, so it *is* a free function.)

**Why.** Mojo has no global variables ("global variables are not
supported; move this into a function body or use 'comptime'"), and
therefore no thread-locals or context variables. The stdlib does have an
internal mechanism (`_get_global` in `std.ffi`), but it is private and
undocumented, and building on it would tie proptest to stdlib internals.

### 1.4 `given` takes one to six strategies

**What.** There are six overloads of `given`, for one to six strategies,
and five `tuples` overloads (two to six). Hypothesis takes any number of
positional or keyword strategies, matched to the test's parameter names.

**Why.** Keyword matching needs `inspect.signature`, which has no Mojo
equivalent: a closure type does not expose its parameter names. Positional
arity is a matter of effort: Mojo has variadic parameter packs (`*Ts`), and
a single variadic `given`/`tuples` may be expressible with them, but the
interaction of packs with closure types and associated `Value` types was
not explored. The overloads are generated mechanically, so going beyond
six is easy; six covers nearly all real properties, and a `composite` or
`given_data` test handles the rest.

### 1.5 `composite(f)`, not `@composite`

Same reason as 1.2: no user decorators. `composite` takes a function
`def(mut ConjectureData) raises -> T`, which is exactly the body of a
Hypothesis composite strategy.

### 1.6 Strategy values must be `Movable` and `Writable`

**What.** `Strategy.Value` must conform to `Movable & Writable &
Deinitable` (the `Drawable` composition). A few strategies also need
`Copyable` values: `just`, `sampled_from`, `permutations` and `shared`
hand out copies of values they hold, `Bundle` keeps values for later
steps, and set elements and dictionary keys must be copyable.

**Why.** `Writable` because failures are reported by printing the drawn
values; Hypothesis can `repr` any Python object, Mojo can only format types
that opt in. Mojo's own `repr()` is too verbose to use for reports
(`repr(5)` is `Int(5)`, `repr([1])` is `List[Int]([Int(1)])`), so
proptest uses `write_to` formatting and quotes top-level strings itself.

Values don't need to be `Copyable` (from Rust proptest, which only asks
for `Debug`): the engine never keeps a value, because it rebuilds every
value from its choice sequence when it replays a test case. So tests can
generate unique handles and other move-only types, and `lazy_just(f)`
stands in for `just` with them. Two limits:
- In Mojo 1.3, `List.write_to` copies its elements, so a `List` of a
  move-only type can be drawn but not printed. It can't be a test
  argument, though a strategy can still use one internally.
- Values that can't be destroyed (linear types) are out of reach, because
  the engine must destroy the inputs of abandoned test cases.

### 1.7 Recursive data has to avoid self-referential structs

**What.** `recursive()` works, but its example and test build nested-list
*strings* rather than a tree struct.

**Why.** Mojo cannot yet compile a struct that contains a collection of
itself. Both

```mojo
struct Tree(Copyable, Deinitable):
    var kids: List[Tree]
```

and the same with `List[ArcPointer[Tree]]` fail with
`field 'kids' has non-'Deinitable' type 'List[...Tree...]'`: the
conditional `Deinitable` conformance of `List` is evaluated before `Tree`'s
own conformance is known. Hypothesis's canonical recursive examples (JSON,
trees) need such types. `recursive()` itself is fine and will work with
recursive structs as soon as they compile.

### 1.8 Telling distinct bugs apart (interesting origins)

**What.** Hypothesis identifies "the same bug" by the exception's type and
the file and line it was raised from, and shrinks each distinct bug
separately. proptest uses the `At <file>:<line>:<col>: <Kind>` prefix that
the `std.testing` assertions and `proptest.fail()` put on error messages.
Errors without such a prefix (`raise Error("...")`) are all treated as one
bug.

**Why.** A Mojo `Error` is a message plus an optional stack trace, and the
stack trace is only collected when the program runs with
`MODULAR_DEBUG=stack-trace-on-error`. There is no exception type
hierarchy for untyped `raises`, and no raise location. Using the whole
message would be wrong: messages usually contain the failing values
(`"x was 101"`), so every shrink step would look like a new bug and
shrinking would stall.

**What could change.** Mojo's typed errors (`raises MyError`) carry a
static type, but a test function's signature is `raises` (untyped), so the
type is erased by the time the engine sees it. If `Error` recorded its
raise location (cheaply, as `call_location()` can), proptest could use it
directly and drop the message-prefix convention.

### 1.9 128-bit integers instead of arbitrary precision

**What.** Integer choices are `Int128`; `integers()` produces `Int`,
`integers_of[dtype]()` any fixed-width integer type.

**Why.** Mojo has no arbitrary-precision integer type in its standard
library. 128 bits holds every value of every Mojo integer type (including
`UInt64`), and choice *indices*, which are distances from `shrink_towards`,
fit in `UInt128`. Where Hypothesis relies on big integers, proptest works
around them:

- **Generation of unbounded integers.** Hypothesis draws in
  `[-2**128, 2**128]`; proptest uses `[-2**126, 2**126]` to stay inside
  `Int128`.
- **Collection indices.** Hypothesis's `choice_to_index` for strings and
  bytes is `alphabet**length`-sized and routinely exceeds any fixed width.
  proptest never materializes it: `choice_compare` compares collections
  structurally (shortlex by element order), which is the same order.
  `choice_from_index` for collections is computed in 128 bits and raises
  `ChoiceTooLarge` past that, which only matters for the "simplest"
  templates and exhaustive enumeration of small spaces, where indices are
  small.
- **`DataTree` child counts.** Capped at 2**120 ("too many to exhaust").

**Would a bigint help?** In two places, a little:

- An `integers()` over a bigint type, for testing code that uses one. That
  needs only a new strategy and wider integer choices, and is the main
  reason to want one.
- Exact collection indices, which would simplify `choice_from_index` and
  the `DataTree`'s counting. The structural comparison is faster than
  bigint arithmetic, so it would stay for ordering.

Everywhere else (floats, booleans, generation, shrinking) fixed width is
simpler and faster. A plausible design if Mojo gains a standard bigint:
keep `Int128` as the fast path for integer choices and add a separate
choice kind for big integers, used only by a big-integer strategy.

As for a "widely used bigint library": the closest is `decimo` (formerly
DeciMojo), which provides `BigInt`, `BigDecimal` and `Decimal128` and is
used by `linamo` in `~/src/mojo/repos/numerics`. It currently pins Mojo
`<1.3`, so it cannot be a dependency yet. A `decimo` strategy would be a
natural optional extension (see section 4), not a reason to change the
core.

---

## 2. Differences in the engine

### 2.1 Shrink-pass scheduling (ported, without `ChoiceTree`)

**What.** As in Hypothesis, the shrinker runs each pass a step at a time:
a step tries the pass at one *position* (a node, a span, a group of equal
choices...), resuming where the pass last stopped; after 10 straight
failures it jumps to random positions; after 20 it moves on to the next
pass; a pass is exhausted once every position has been tried on the
current shrink target; and after each round the passes that deleted
choices move to the front and the useless ones to the back
(`fixate_shrink_passes`). Per-pass statistics are printed at debug
verbosity, like Hypothesis's shrink-pass profiling.

**What differs, and why.** Hypothesis's passes are generator-like
functions of a `chooser`: a pass calls `chooser.choose(sequence,
condition)` several times per step (for instance a label, then a span with
that label, then a descendant span), and a `ChoiceTree` records which
*combinations* have been tried. Mojo has no generators or coroutines to
suspend a pass mid-step, so proptest's passes choose only their first
position from the scheduler and loop over the rest of the combination
inside the step. The scheduling behavior is the same at the level that
matters (cheap failing steps, random jumps when stalled, pass reordering);
what's lost is finer-grained resumption inside a step.

One visible consequence, shared with Hypothesis: which local minimum the
shrinker reaches depends on the order of attempts. The Die Hard state
machine has two minimal solutions (6 steps starting with `fill_big`, 8
starting with `fill_small`) that no single deletion or lowering connects;
with this scheduling, roughly one run in twelve reports the 8-step one.

### 2.2 One shrink pass is missing

- **`normalize_unicode_chars` is ported.** It replaces characters with
  simpler related ones: case forms (from Mojo's `String.upper()` and
  `lower()`), and the characters of their NFD and NFKD decompositions and
  casefold (so `'À'` becomes `'A'`, `'ﬁ'` becomes `'F'`, a mathematical
  bold `'𝐓'` becomes `'T'`). Mojo's standard library has case mapping but
  no normalization or casefold data, so `tools/gen_unicode.mojo` generates a
  table of the decompositions (6,954 codepoints, from the Unicode
  Character Database), except for the 11,172 Hangul syllables, whose
  decomposition is computed with the Unicode standard's algorithm to keep
  the table small. The shrinker only parses the table when it meets a
  non-ASCII character. All four of Hypothesis's shrink-quality tests for
  this pass (issue 4725 among them) are ported and pass.
- **`widen_to_span_with_recorded_value`** replaces a strategy's choices with
  a *value hole* holding the value it produced, and asks the strategy at
  that position to re-encode the value (`_invert`) more simply, for
  example moving a value from a later `one_of` branch to an earlier one.
  **Why not:** it needs every strategy to implement inversion
  (value → choices), and the hole to hold a value of any type in the
  untyped choice sequence. The second is doable with type erasure (as
  `BoxedStrategy` does), but the first is a new obligation on every
  strategy. `reduce_each_alternative`, which is ported, covers the most
  common case.

### 2.3 Misaligned integer choices are clamped

**What.** When a replayed choice does not fit the constraints the test now
draws under (it is *misaligned*), Hypothesis substitutes the simplest
choice. proptest does the same, except that an integer that is merely out
of range is clamped into the range.

**Why.** This is a deliberate improvement rather than a limitation.
Misalignment is usually caused by the shrinker deleting part of a
collection, after which an index into it (`integers(0, len(xs) - 1)`) may
be out of range. Resetting it to 0 moves the index to the start of the
collection; clamping keeps it pointing at the end. In stateful tests that
check the most recent element, the reset turns a successful deletion into
a passing test, and the shrinker gets stuck with extra steps; with clamping
the buggy-set test in `tests/test_stateful.mojo` shrinks to the true
minimum every time (15 of 15 runs, against roughly 1 in 4 failures to do so
before). Termination is unaffected: the shrinker only accepts candidates
that are simpler by the sort order.

### 2.4 The `DataTree` is uncompressed

**What.** proptest's `DataTree` records every test case's choices in a
trie, generates novel prefixes, simulates attempts to avoid re-running
known ones, detects exhaustion, and detects *flaky strategies* (data
generation that makes different choices, or a different number of them,
after the same earlier choices), reported as `FlakyStrategyDefinition`.
Unlike Hypothesis's it does not compress runs of single-child nodes into
one node.

**Why.** Compression is a memory optimization that matters for long-running
tests with large inputs; proptest's tree uses one node per choice, which
is simpler and has not been a problem at the sizes tested. Flakiness
detection checks the cases Hypothesis checks (choice kind and constraints,
forcedness, and a run stopping earlier or later than an earlier run with
the same choices), except that, like Hypothesis, a test whose outcome
changes (failing, then passing) is left to the replay check, which reports
it as a flaky *test*.

### 2.5 Other engine features

- **The early "small examples" phase is ported.** For its first examples
  (up to a tenth of `max_examples`, at most 50) the engine runs the
  simplest completion of a novel prefix, then a random completion limited
  to five times its size, chosen through the tree so it is never a repeat.
  Overruns caused by that limit don't count towards the `data_too_large`
  health check.
- **The Pareto front is ported** (`internal/pareto.mojo`): with a
  database, the engine keeps an approximate front of non-dominated
  targeted test cases, saves it under the test's key plus `.pareto`,
  replays it in the reuse phase to seed the next run, and at the end of
  the target phase shrinks each member, accepting only shrinks that
  dominate it. Two differences: Hypothesis also compares structural
  coverage *tags*, which proptest doesn't record, and proptest caps the
  Pareto optimization at 10 × `max_examples` test calls. The cap exists
  because competing targets (say, a list's length and its sum) make the
  front hundreds of members long and each shrink costs hundreds of calls;
  Hypothesis bounds this indirectly through its target-phase budget,
  which proptest structures differently.
- **Byte strings favor boundary bytes.** Hypothesis draws each byte of
  a byte string uniformly (its only bias is toward constants scraped
  from the test's module, which proptest has no way to collect). proptest
  makes each byte one of 0x00, 0x01, 0x7F, 0x80, 0xFE and 0xFF with
  probability 1/8, and 5% of byte strings one of them repeated, as
  byte-level fuzzers do: parsers and codecs break at those values (sign
  bits, terminators, all-ones fields), which uniform bytes hit once in
  256 draws each. Shrinking is unaffected; the fuzz loop
  (`FuzzTarget.fuzz`) also mutates single bytes to these values.
- **Integer `weights` are a full distribution.** Hypothesis's integer
  choices take `weights`, a mapping from some values to probabilities
  summing to less than 1, with the rest of the probability spread over
  the whole range. proptest's are a list of probabilities for
  `min_value`, `min_value + 1`, ..., `max_value`, summing to 1, which is
  all its users need: `one_of(..., weights=)`, `sampled_from(...,
  weights=)` and the command choice of `commands()` each pick an index in
  a small range. As in Hypothesis, weights only change how values are
  generated: the simplicity order and the shrinker ignore them, and so
  does the byte reader of `fuzz_one_input` (3.11).

### 2.6 Strings are codepoint lists inside the engine

**What.** String choices are `List[UInt32]` of codepoints, converted to a
`String` by the strategy.

**Why.** Mojo strings are UTF-8 and deliberately don't offer indexing by
character (`len(String)` is a compile error, to force a choice between
bytes, codepoints and graphemes). The shrinker needs to replace, delete and
reorder individual characters, so codepoints are the natural unit. This is
invisible to users.

### 2.7 Database format

**What.** Saved examples are text files with one choice per line, in
`.proptest/examples/<hash of key>/<hash of contents>`. Hypothesis uses a
binary encoding (`choices_to_bytes`) in the same directory layout, plus
secondary and Pareto keys, and supports other backends (Redis, GitHub
artifacts, multiplexed and read-only databases).

**Why.** Compatibility with Hypothesis's databases is pointless (choice
sequences only make sense for the same test), and text is easy to inspect.
The test's key is its source location (`file:line:col` of the `given`
call), since Mojo has no stable function names for closures; moving a test
in its file therefore orphans its saved examples, where Hypothesis keys on
the function's qualified name. Other backends were not needed.

---

## 3. Features not ported, or ported with changes

### 3.1 Deadlines (ported)

`Settings(deadline=...)` (milliseconds, default 200, `None` to disable)
works as in Hypothesis: an example whose test body takes longer fails with
`DeadlineExceeded`, with 25% grace except on the final replay, and a
failure that doesn't exceed the deadline when replayed is reported as
"unreliable test timings". Time spent drawing data is excluded. The
`too_slow` health check (more than `max(1 s, 5 × deadline)` spent
generating data before ten valid examples) is ported with it.

**Remaining differences.**

- **Stateful tests have a deadline per step.** Each step of a state
  machine (its rule and the invariant checks after it, excluding time
  spent drawing data) must finish within the deadline. Hypothesis instead
  times the whole state-machine run and *subtracts* the time spent in
  rules (`_stateful_run_times`), so in practice rule bodies are never
  subject to its deadline. Per-step deadlines catch a slow operation in
  the system under test, which is what a deadline is for; pass
  `deadline=None` to turn them off.
- **Deadlines are measured per example with a wall clock**, so a test that
  runs a whole nested `find` or `given` per example (as some of proptest's
  own tests do) needs `deadline=None`, as in Hypothesis.

### 3.2 Alternative backends

Hypothesis can replace its random generator with another *provider*, most
notably CrossHair (symbolic execution with an SMT solver). **Why not:**
the providers that exist are Python libraries that execute Python code
symbolically; there is nothing equivalent for Mojo. The provider
abstraction itself is easy (proptest's `Provider` could become a trait),
but without a backend to plug in it would be speculative. **Practical:
the interface yes; useful backends, not today.**

### 3.3 `@reproduce_failure` (ported as a setting)

With `print_blob=True` (or verbose output), a failure report includes a
line like `Settings(reproduce="proptest1:aToxMDAxCg==")`, and running the
test with that setting replays exactly that example: no database, no
search and no shrinking; it raises `DidNotReproduce` if the example no
longer fails.

**Why it differs.** Hypothesis prints a `@reproduce_failure(version, blob)`
decorator to paste above the test. Mojo has no user decorators (1.2), so
it is a setting instead. The blob is the database's text format, base64
encoded (`std.base64`), with a `proptest1:` prefix in place of
Hypothesis's version check: a blob only makes sense for the same test and
strategies, which no version number can guarantee, so proptest just
reports `DidNotReproduce` when they have changed.

### 3.4 The explain phase (argument half ported)

After shrinking, proptest varies each argument of the minimal example
(largest first): first by borrowing the values of other arguments of the
same shape, so that `assert a != b` isn't misreported, then randomly. If 100
variations fail the same way, the argument is marked "or any other
generated value"; one passing variation rules it out. If several arguments
are marked, it checks whether they can vary together and reports the
result, all as in Hypothesis (`Shrinker._explain`). "Arguments" are the
top-level draws: the arguments of `given`, and the draws of a `given_data`
test.

**What isn't ported, and why.**

- **Coverage-based explanations** ("these lines were only run by failing
  examples") need line tracing (`sys.settrace` in Python). Mojo has no
  tracing or coverage hooks at run time.
- **State machines** don't get explanations: their reports print steps,
  not arguments, so the phase is switched off for
  `run_state_machine_as_test`, where it would only cost time (every rule
  argument is a top-level draw).
- Hypothesis skips the experiments when a passing test case seen during
  shrinking already settles them (`passing_choice_sequences`); proptest
  always runs them, which costs a few hundred extra calls per failure but
  gives the same answers.

Turn it off with `Phases(explain=False)`.

### 3.5 Type inference: `from_type` (ported at compile time)

`from_type[T]()` resolves a strategy at compile time:

1. a type implementing the `Arbitrary` trait draws itself with its static
   `arbitrary(data)` (Hypothesis's `register_type_strategy`, but attached
   to the type);
2. the standard types have `Arbitrary`-style implementations added by
   struct extensions (`__extension List(...)`): integer and float
   scalars, `Bool`, `String`, `List`, `Optional`, `Set`, `Dict` and
   `Tuple` of one to six elements, each drawing its parameters
   recursively with `from_type`, so they nest to any depth;
3. any other struct is built field by field, recursively, each field in
   its own span (Hypothesis's `builds(Cls)` with every argument inferred).

`build[T](field["name"](strategy), ...)` (from RapidCheck's `gen::build`)
builds a struct field by field like case 3, drawing the named fields from
the given strategies: Hypothesis's `builds(Cls, name=strategy)`. The
names and the strategies' types are checked at compile time, against the
fields rather than an `__init__`'s parameters, for the reason below.

**What differs, and why.**

- **Inference from a test's parameters is `check(prop)`, not `given`**:
  Mojo can't reflect on a function's signature, but overload resolution
  infers the argument types of a closure type parameter
  (`check[A: Drawable, B: Drawable, //, P: def(A, B) raises](f: P)`), and
  each is drawn with `from_type`. This is quickcheck's `Testable` rather
  than Hypothesis's `@given(x=...)`/`builds` inference: there are
  separate overloads for one to six arguments and for properties that
  return `Bool`, and `given` itself still takes explicit strategies.
- **Structs are built from their fields, not their `__init__`**: Mojo can
  reflect on a struct's fields (`reflect[T].field_types()`,
  `field_offset`) but not on its initializers. The struct is allocated
  uninitialized and each field written at its offset, so invariants that
  `__init__` would establish don't hold; such types should implement
  `Arbitrary`.
- **Standard types get their strategies from struct extensions.** Mojo
  can't pattern-match a generic type (`T == List[E]` for an unknown `E`)
  or ask a type for its parameters from outside, but a struct extension
  can add a trait conformance to `List` whose static method sees
  `Self.T` (and `Dict`'s `Self.K`/`Self.V`, a `Tuple`'s `Self.Ts[i]`).
  This is the type-class instance Hypothesis gets from its type registry.
  The extensions implement a private trait rather than `Arbitrary`
  itself, because `Optional` and `Tuple` are only conditionally
  movable: the private trait's draw is generic over the type
  `draw_from_type` asks for (always `Self`, and known to be copyable).
  Earlier versions enumerated 298 supported combinations in a generated
  chain of `comptime if`s, limited to one level of nesting and to pairs
  and triples of common types. Tuples stop at six elements because
  `tuples()` does; `Set` and `Dict` need the default hasher. A field of
  an unsupported type is a compile-time error.
- If drawing a struct is abandoned part-way (the test case overruns or is
  filtered out), the fields written so far are leaked rather than
  destroyed, because a partly initialized struct can't be destroyed
  safely. It's small and only happens for discarded test cases.
- **Constraint types are an addition** (`strategies/constraints.mojo`):
  `Bounded`, `Positive`, `NonNegative`, `NonZero`, `NonEmpty`, `Sorted`,
  `Blind` and `Via` come from QuickCheck's modifiers. In Hypothesis the
  strategy is an argument to `@given`; with `check(prop)` the type is the
  only place left to say "a non-empty list", so the wrappers implement
  `Arbitrary` and carry the constraint in the type. `Via[f]` takes a draw
  function rather than a strategy: a strategy can't be a type parameter
  because the strategy constructors raise, and a struct field whose type
  is a strategy parameter's associated `Value` trips a Mojo 1.3 bug
  ("use of uninitialized value") once the value is non-trivial.

### 3.6 `from_regex` (ported for the common subset)

`from_regex(pattern, fullmatch=False)` supports literals and escapes,
`.`, character classes and ranges, `\d \w \s` and their negations (with
Python's Unicode meanings), groups (capturing, non-capturing, named),
alternation, all quantifiers including lazy and possessive forms, the
anchors `^ $ \A \Z` at the ends of the pattern, and the inline flags
`(?i)` and `(?s)`. As in Hypothesis, unanchored patterns are padded with
arbitrary text unless `fullmatch=True`, and a repeated character class is
drawn as one string choice so it shrinks like text.

**What differs, and why.**

- **Backreferences, lookaround, word boundaries, conditionals, anchors in
  the middle of a pattern, and other flags raise `InvalidArgument`.**
  Hypothesis supports them by generating candidates and then filtering
  with `re.search`/`re.fullmatch`; Mojo has no regex engine to filter
  with. Everything that *is* supported is generated exactly, so no filter
  is needed.
- **proptest has its own parser.** The parser in
  `~/src/mojo/examples/MojoCompileTimeRegex` was designed for
  compile-time matching, with fixed limits (20 alternatives, 20 sequence
  items) and ASCII character classes; generation needs Unicode classes,
  ranges, negation and case folding, so a small runtime parser
  (`strategies/regex.mojo`) was simpler.
- **Byte patterns** (`from_regex(b"...")`, generating `bytes`) aren't
  supported.

### 3.7 Dates and times, emails, IP addresses, UUIDs, fractions, decimals

**Why not:** Mojo's standard library has no date/time, network-address,
UUID, rational or decimal types (`std.time` only measures time). These
strategies generate values *of those types*, so without the types there is
nothing to generate. Strings in those formats (an email address as a
`String`) could be generated with `from_regex` or composites.
**Practical: once such types exist, or as strategies for third-party
types (`decimo` for decimals and big integers).**

### 3.8 NumPy: `proptest_numojo` (ported for NuMojo)

`extras/proptest_numojo` provides `arrays[dtype](shape, elements,
unique=)` with fixed or drawn shapes, `array_shapes(min_dims=, max_dims=,
min_side=, max_side=)` and `from_dtype[dtype]()`, for NuMojo's `NDArray`.

**What differs, and why.**

- **A separate package.** `mojo precompile proptest` compiles every module
  of the package, so a NuMojo module inside proptest would make NuMojo a
  hard dependency. `pixi run test-numojo` uses the Mojo 1.3-patched NuMojo
  vendored by MojoDEC, because the published NuMojo requires Mojo < 1.3.
- **The dtype is a compile-time parameter**, not a strategy
  (Hypothesis's `scalar_dtypes()` and friends): an `NDArray`'s dtype is part
  of its type, so a test's parameter type fixes it.
- **Every element is drawn.** Hypothesis draws only some elements of large
  arrays and fills the rest with a fill value, which is faster; proptest
  draws all of them, which is simpler and shrinks the same.
- `broadcastable_shapes`, `mutually_broadcastable_shapes`, `basic_indices`
  and `integer_array_indices` are ported, with three differences:
  `mutually_broadcastable_shapes` takes `num_shapes` but not a gufunc
  `signature` (signature parsing could be added; NuMojo has no gufuncs to
  use it with); `basic_indices` returns a `BasicIndex` value with an
  `apply(array)` method rather than a tuple, and its slices have
  non-negative bounds and positive steps; and `integer_array_indices`
  returns a list of arrays, since NuMojo's integer-array indexing only
  takes one array (for the first dimension).
- **Testing these found two NuMojo 0.12 bugs.** NumPy accepts an
  ellipsis that stands for no dimensions (`a[..., 0, 0, 0]` on a 3-D
  array); NuMojo counts the ellipsis as a dimension and raises "Too many
  indices". And when every dimension is indexed by an integer, NuMojo
  drops new axes: `a[newaxis, 0, 0, 0]` has shape `()` instead of NumPy's
  `(1,)`. `basic_indices` generates both (as Hypothesis's does); the tests
  in `extras/tests` skip them with `assume` and a comment.
- pandas and the array API have no Mojo counterparts.

### 3.9 Unicode categories in `characters()` (ported)

`characters(categories=, exclude_categories=, codec=)` work as in
Hypothesis, including one-letter major categories (`"L"`). The category
table is generated from the Unicode Character Database (Unicode 17.0,
pinned in `pixi.toml`) by `tools/gen_unicode.mojo` and checked in, because
Mojo's standard library has no Unicode category data; Hypothesis builds
the same table at run time from `unicodedata` and caches it on disk.

**What differs, and why.**

- **Surrogates (`Cs`) are never generated**, since UTF-8 can't encode
  them; Python strings can hold them.
- **`codec` accepts only `"ascii"`, `"latin-1"` and `"utf-8"`**: Mojo has
  no codec registry to ask which characters a codec can encode.
- **An empty `categories` list means "no restriction"**, where Hypothesis's
  `categories=()` means "no categories" (only `include_characters`). A Mojo
  list literal can't be passed where an `Optional[List[String]]` is
  expected, so the argument is a plain list and empty is the default.
- The Unicode version is fixed when the table is generated (it's whatever
  `unicodedata` the generating Python had), not the running Python's.

### 3.10 Smaller omissions

- **`deferred()`** (lazily defined, mutually recursive strategies) needs a
  strategy that refers to itself through shared mutable state; with
  `BoxedStrategy` and `ArcPointer` it is possible, but `recursive()` covers
  the common case.
- **`shared()` is ported**, with one difference: without a `key`,
  Hypothesis shares between uses of the same strategy *object*, and Mojo
  values have no identity to key on (copies are separate values). proptest
  keys on the source location of the `shared(...)` call instead, which
  gives the same behavior for the usual `var x = shared(s)` and reuses of
  `x`. Values are kept type-erased on the `ConjectureData`; reading a key
  back as a different type raises an error rather than misbehaving.
- **`one_of` takes `weights=`** (from Rust's `prop_oneof![w => s, ...]`;
  Hypothesis has no weighted `one_of`). The branch is still an integer
  choice in `[0, n)`, so shrinking and the shrinker's alternative-lowering
  pass are unchanged; the weights live in the choice's constraints and
  only bias generation. They are a list of probabilities over the whole
  range, a simplification of Hypothesis's internal `weights` mapping
  (some values to probabilities, the rest uniform), which Hypothesis uses
  for `sampled_from`-like internals rather than in its public API.
  `one_of(s1, ..., s6)` also stores its strategies unboxed, so they need
  not be `Copyable`.
- **`fixed_dictionaries`, `frozensets`, `iterables`, `randoms`,
  `slices`, `register_type_strategy`**: Python-specific types
  or behaviors, or (for `fixed_dictionaries`) easy to write with
  `composite`.
- **Statistics are ported as a setting**: `show_statistics=True` prints
  the generate phase's events (Hypothesis's
  `--hypothesis-show-statistics`, without the timing lines). QuickCheck's
  `tabulate` and `cover` add tables and coverage requirements, and
  `check_coverage=Confidence()` checks the requirements with its Wilson
  score test, generating past `max_examples` as needed (giving up after
  100,000 examples, where the observed share decides). Hypothesis has no
  coverage requirements. `cover` and `tabulate` also exist as strategy
  wrappers, because `given` tests have no `ConjectureData` to call them
  on (1.3).
- **`functions()` is ported** as `functions[A](returns)`, returning a
  memoized `Function[A, R]`. Hypothesis's version wraps a signature
  (`like=`) and checks purity; here the argument type is a parameter and
  results are memoized by key, so a function is pure by construction.
  Calls print as a table, `{x->y, ...}`, rather than as the calls noted
  one by one. The argument must be a `KeyElement`. Calling a function
  after its test case has ended raises.
- **Additions from other libraries** (not in Hypothesis): `filter_map`
  and `filter(reason=)`, `subsequence` and `Index`, and `lazy_just`, from
  Rust proptest; `Outcome` results, `expect_failure`, `run_property` and
  the `PolyA`/`PolyB`/`PolyC` test types, from QuickCheck; and from
  RapidCheck, `apply(s1, ..., sN, f)` (Hypothesis's `builds` with a
  function, with the function last as in `given`, because Mojo infers
  parameters in argument order), `sampled_from(..., weights=)` (using the
  same choice weights as `one_of`), `build[T](field["x"](s), ...)` (below,
  3.5), and the `before_minimal_test_case()` breakpoint hook.
- **`Settings(fork=True)` and `Settings(timeout=ms)`** (not in
  Hypothesis; from Rust proptest's `fork` and `timeout`): each test case
  runs in a `fork()`ed child, so crashes and hangs fail test cases instead
  of ending the run, and are shrunk. Python code rarely crashes the
  interpreter, so Hypothesis has no need for this; Mojo code with raw
  pointers often does. Unlike Rust proptest, which records each test
  case's input before running it and restarts a child that dies, the
  child here logs its choices and spans to memory shared with the parent
  as it makes them, so a crash partway through still leaves the parent
  the choices the shrinker needs. Nothing a child logs is trusted: a log
  that is inconsistent (because the test corrupted the child's memory) is
  reported as a crash. A crash's interesting origin is its signal, or its
  exit status (1.8). A memory error can fail differently from run to run,
  so when the final replay of a failure fails with a different origin,
  the report says so and gives the original error (Hypothesis reports the
  new error alone); such a failure may not have been shrunk.
- **Observability output, settings profiles, the pytest plugin, the ghostwriter**: tooling around
  Python's ecosystem. Environment-variable overrides stand in for profiles.
- **Health checks**: `filter_too_much`, `data_too_large`,
  `large_base_example` and `too_slow` are ported; `function_scoped_fixture`, `differing_executors`,
  `nested_given` and `return_value` are about pytest or Python semantics.

### 3.11 `fuzz_one_input` (ported as `fuzz_target`)

Hypothesis attaches `fuzz_one_input` to every `@given` test. proptest's
`given` runs immediately, so `fuzz_target(strategies..., test)` takes the
same arguments and returns a `FuzzTarget` with a `fuzz_one_input(bytes)`
method. Mojo can't return a closure-typed value without naming its type,
so the target type-erases the engine's runner (as `BoxedStrategy` does),
and is generic over the type of the test and its strategies, which it
owns, so that a test capturing variables by reference keeps them alive.
The bytes are read as in Hypothesis's `BytestringProvider`
(`internal/bytestring.mojo`): bit-exact integers with rejection,
one-byte booleans, 65-bit floats clamped into range, and a continue byte
before each optional element of a string or byte string; weights and
special values are ignored. The differences:

- **The return value replays.** For a passing test, Hypothesis returns
  the test case's database encoding, which `fuzz_one_input` reads
  differently. proptest returns the bytes that decode to the same
  choices (its own inverse of the reader), so a fuzzer can store them in
  its corpus.
- **Failures are saved under the test's key, not `<key>.secondary`.**
  Hypothesis replays its secondary corpus only when the primary one is
  small; proptest's `given` replays the key it saves to, so a failure
  found by fuzzing is reported by the next ordinary run. As in Hypothesis,
  only failures simpler than the simplest seen so far for their origin
  are saved. The two share a key only if they are given the same
  `database_key`: the defaults are their call sites, where Hypothesis
  uses a digest of the test function.
- **Crashes**: with `fork=True` (3.10) each input runs in a child
  process, so a crash raises from `fuzz_one_input` and is saved instead
  of ending the fuzzer.
- **A built-in fuzz loop.** `FuzzTarget.fuzz(seconds)` has no Hypothesis
  counterpart; the nearest is HypoFuzz, a separate project, which
  measures code coverage. Mojo has no coverage hooks a library can read,
  so proptest's loop measures what the strategies did instead: each
  (parent span label, span label) pair, with its count in AFL's buckets,
  each `event`, and any improved `target` score. A valid test case that
  adds one joins the corpus, saved under `<database_key>.fuzz`. Each
  new test case is either generated fresh (one in ten) or a mutation of
  a corpus entry: one to three values replaced by random or boundary
  values (0, +-1, the bounds, powers of two near machine-type limits,
  infinities, NaN, subnormals), and/or a span spliced from another entry
  with the same label, deleted, duplicated, or cut off and redrawn.
  Failures are shrunk and reported as `given` reports them. Without
  coverage, a test that branches on values its strategies don't
  distinguish gets no guidance unless it calls `event` or `target`.
- No observability output.

---

## 4. What is practical to port

Grouped by what stands in the way.

**Blocked by Mojo today** (revisit when the language changes):

| Feature | Waiting for |
| --- | --- |
| `s.map(f)` methods | the default-method/associated-type closure bug (1.1) |
| `@rule`, `@composite`, `@reproduce_failure` syntax | user-defined decorators (1.2) |
| Automatic rule discovery | method reflection (1.2) |
| Free-function `note`/`event`/`target` | globals or context variables (1.3) |
| Recursive data types in tests and examples | self-referential structs (1.7) |
| Location-based bug identity for all errors | raise locations on `Error` (1.8) |
| Big integers | a bigint in the stdlib, or `decimo` on Mojo 1.3 (1.9) |

**Ported since this document was first written:**

- From the "practical now, small" list: deadlines and the `too_slow`
  health check (3.1), the `reproduce=` setting (3.3), flaky-strategy
  detection (2.4), the small-examples phase (2.5), `shared()` (3.10),
  `given`/`tuples` for up to six strategies (1.4), and the case-mapping
  half of `normalize_unicode_chars` (2.2).
- From the "practical now, moderate" list: `from_type[T]()` (3.5),
  `from_regex` (3.6), the NuMojo package (3.8), Unicode categories (3.9),
  the argument half of the explain phase (3.4), step-wise shrink-pass
  scheduling (2.1) and the Pareto front (2.5).
- From the remaining small items: the NuMojo index and broadcasting
  strategies (3.8), nested containers and tuples in `from_type` (3.5), the
  decomposition half of `normalize_unicode_chars` (2.2), and deadlines for
  stateful steps (3.1).
- From [ideas.md](ideas.md): type-directed `check(prop)` (3.5), which
  turned out not to need signature reflection, constraint types (3.5),
  typed state machines (1.2), unboxed, weighted `one_of` (3.10),
  statistics with coverage checking (3.10), move-only values (1.6),
  `functions()` (3.10), and the smaller additions listed there; and
  from RapidCheck, model-based testing with commands (1.2).

Nothing practical-and-small is left; what remains is either blocked by
Mojo (above) or of doubtful value (below).

**Possible but not obviously worth it:**

- `widen_to_span_with_recorded_value` (2.2): inversion would be a new
  method every strategy must implement.
- A pluggable provider interface (3.2), until there is a backend to use it.
- Hypothesis-compatible database formats and backends (2.7).
