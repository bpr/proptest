# Influences and differences

proptest started as a port of Hypothesis, and its engine still is one. Its
API also borrows from other property-testing libraries, especially where
their designs suit a statically typed language better than Hypothesis's
dynamic one. This page says what came from where.

## Hypothesis

From Hypothesis, proptest has:

- **the Conjecture engine**: choice sequences, spans, the shrinker and
  its passes, the data tree, mutation, targeting, the Pareto front, and the
  explain phase;
- **the strategies**: numbers, text, collections, `one_of`, `map`,
  `filter`, `flatmap`, `composite`, `recursive`, `shared`, `functions`,
  `from_regex` with Unicode categories, and `from_type`;
- **the example database**, health checks, deadlines, settings, phases,
  verbosity, `@reproduce_failure` (as `Settings(reproduce=...)`), and
  run statistics;
- **rule-based state machines**, with bundles, preconditions, invariants,
  initialize rules, and swarm testing;
- **NuMojo strategies**, the counterpart of `hypothesis.extra.numpy`.

The [differences document](https://github.com/bpr/proptest/blob/master/docs/differences-from-hypothesis.md)
lists every difference from Hypothesis and why. The main ones are
described in [Why the API looks the way it does](mojo-api.md). Not ported:
alternative backends, observability output, the date, time, email, and IP
address strategies, and Hypothesis's tooling (the pytest plugin, the
ghostwriter).

## Rust's quickcheck

- **`check(prop)`**: strategies inferred from the property's parameter
  types, like quickcheck's `quickcheck(prop)` and its `Testable` trait.
- **`Outcome`**: a property can pass, fail with a message, or discard its
  input (quickcheck's `TestResult`).

## Haskell's QuickCheck

- **Constraint types**: `Positive[T]`, `NonNegative[T]`, `NonZero[T]`,
  `NonEmpty[T]`, `Sorted[T]`, and `Blind[T]`, from QuickCheck's modifiers.
- **Coverage**: `cover`, `tabulate`, and `check_coverage` with its
  statistical test (`checkCoverage`).
- **`expect_failure`** (`expectFailure`), and **`run_property`**
  (`quickCheckResult`).
- **`PolyA`, `PolyB`, `PolyC`**, the stand-in types for generic code
  (`Test.QuickCheck.Poly`).
- **Generated functions** that print as tables (`Fun`), alongside
  Hypothesis's `functions`.

## Rust's proptest

- **Typed state machines**, whose steps are values of a `Transition` type
  (proptest-state-machine).
- **`filter_map`**, **`filter(reason=)`**, **`subsequence`**, **`Index`**,
  **`lazy_just`**, and weighted **`one_of`**.

## RapidCheck, and Erlang QuickCheck

- **Model-based testing** with `Command` structs, the model kept separate
  from the system under test (`rc::state`, which follows Erlang
  QuickCheck's `eqc_statem`).
- **`build[T](field["x"](s))`** (`gen::build`), **`apply`**
  (`gen::apply`), weighted **`sampled_from`** (`gen::weightedElement`),
  and **`before_minimal_test_case`** (`rc::beforeMinimalTestCase`).

## What wasn't borrowed

Some ideas from these libraries don't fit Conjecture:

- **Shrinking values directly** (QuickCheck's `shrink`, Rust proptest's
  `ValueTree`): Conjecture shrinks the choice sequence instead, which needs
  no per-type code and keeps every invariant.
- **A size parameter** (QuickCheck's `sized`, RapidCheck's `resize`):
  Conjecture controls sizes through average sizes and a choice budget, and
  a global size would interfere with replay and the database.
- **Macros and derive attributes**: Mojo has no user macros. `check`,
  `from_type`, `composite`, and `TestSuite` discovery cover the same
  ground.

The repository's [ideas document](https://github.com/bpr/proptest/blob/master/docs/ideas.md)
records each idea considered, with the reasons for adopting or rejecting
it.
