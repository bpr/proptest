# Why the API looks the way it does

proptest's API follows Hypothesis's names and ideas, but it's shaped by
Mojo, a statically typed, compiled language without decorators, global
variables, or run-time reflection on functions. This page explains the
main differences in shape.

## `given` is a function, not a decorator

Hypothesis writes `@given(st.integers())` above a test. Mojo has no user
decorators, so `given(integers(), prop)` is a call inside the test, with
the property as a nested function. The compiler checks that the property's
parameter types match the strategies' value types.

There are separate overloads of `given` for one to six strategies, because
Mojo can't yet express "a function whose parameters are the value types of
these strategies" for any number of strategies.

## Combinators are free functions

Hypothesis writes `integers().map(f)`. In proptest it's `map(integers(),
f)`. A method on the `Strategy` trait that's generic over a closure of
`Self.Value` hits a compiler limitation, so `map`, `filter`, `flatmap` and
the rest are free functions with the strategy first.

## Strategies have types

Every strategy is a struct with a type: `integers()` returns an `Integers`,
`lists(integers())` a `Lists[Integers]`, and `map(s, f)` a `Mapped[S, R,
F]`, where `F` is the type of the function. These types let the compiler
check and specialize every test, so drawing a value calls the strategies'
code directly, with no dynamic dispatch. The cost is that a function
returning a strategy has to spell its type; `boxed(s)` erases it, at the
cost of an indirect call.

`one_of` follows the same pattern: `one_of(s1, s2, s3)` stores its
strategies in a tuple, with no boxing, and a list of `BoxedStrategy` is
the dynamic alternative.

## Inferring strategies from types happens at compile time

Hypothesis's `from_type` looks at a type at run time. proptest's
`from_type[T]()` chooses the strategy at compile time: from an `Arbitrary`
implementation, from the standard types' built-in strategies, or by
reflecting on a struct's fields. `check(prop)` doesn't reflect on the
property's signature (Mojo can't); overload resolution infers its
parameter types, and each is drawn with `from_type`.

## Settings are a struct

Hypothesis's settings are a decorator with named profiles. proptest's are a
`Settings` struct of keyword arguments. Mojo has no global variables, so
there's no global profile; `PROPTEST_*` environment variables take its
place.

## State machines number their rules

Hypothesis finds a state machine's rules by looking for methods decorated
with `@rule`. A proptest `StateMachine` numbers its rules and dispatches
on the number. `TypedStateMachine` and commands avoid numbers by making
operations into values and structs.

## The "interesting origin" is a location prefix

Hypothesis tells bugs apart by the exception's type and the line it was
raised on. Mojo errors don't have types or tracebacks, so proptest uses the
`At file:line:col:` prefix that `std.testing` assertions and `fail()` put on
their messages. Errors raised without one count as a single bug.

## Integers are 128-bit

Hypothesis's integers are unbounded, like Python's. proptest's choices are
128-bit integers, which covers every Mojo integer type.

The [differences document](https://github.com/bpr/proptest/blob/master/docs/differences-from-hypothesis.md)
lists every difference from Hypothesis, with the reasons.
