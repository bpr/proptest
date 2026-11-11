# proptest

proptest is a property testing framework for Mojo (i.e., the QuickCheck
family) inspired by the [Hypothesis](https://hypothesis.works/) framework
for Python, with ideas from Rust's
[proptest](https://github.com/proptest-rs/proptest) and
[quickcheck](https://github.com/BurntSushi/quickcheck), Haskell's
[QuickCheck](https://github.com/nick8325/quickcheck), and C++'s
[RapidCheck](https://github.com/emil-e/rapidcheck).

You state a property your code should have and say which inputs it should
hold for. proptest generates many inputs, looking for one that breaks the
property, and when it finds one it *shrinks* it to a minimal failing
example before reporting it.

```mojo
from std.testing import assert_equal
from proptest import given, text

def test_decode_inverts_encode() raises:
    def prop(s: String) raises:
        assert_equal(decode(encode(s)), s)
    given(text(), prop)
```

```
Falsifying example (examples/quickstart.mojo:41:14):
    given('0')
At examples/quickstart.mojo:38:21: AssertionError: `left == right` comparison failed:
   left:
  right: 0
```

Like Hypothesis, proptest is built on the *Conjecture* engine: strategies
don't generate values directly but parse them from a sequence of recorded
choices, and the shrinker simplifies that choice sequence. Shrinking
therefore works for any strategy, including ones you write yourself, with
no shrinking code of your own.

The other libraries contributed most of the typed API:
- **Rust's quickcheck:** `check(prop)`, with strategies inferred from the
  property's parameter types.
- **Haskell's QuickCheck:** constraint types such as `Positive[T]` and
  `NonEmpty[T]`, coverage checking, `Outcome` results and the `PolyA`
  test types.
- **Rust's proptest:** typed state machines, `filter_map` and weighted
  `one_of`.
- **RapidCheck:** model-based testing with `Command` structs, `build` and
  `apply`.

What came from where is recorded in
[docs/differences-from-hypothesis.md](docs/differences-from-hypothesis.md)
and [docs/ideas.md](docs/ideas.md).

## Documentation

The [proptest book](https://bpr.github.io/proptest/) has a tutorial,
how-to guides, explanations, and a reference, following the layout of
Hypothesis's documentation. Its sources are in [book/](book/); to build it
locally, install [mdbook](https://rust-lang.github.io/mdBook/) and run
`pixi run book` (output in `book/build/`), or `pixi run book-serve` to read
it in a browser. `pixi run book-test` compiles and runs every code example in it.

## Setup

proptest needs Mojo 1.3 or later (the nightly channel, via pixi):

```sh
pixi install
pixi run test        # the test suite
pixi run examples    # the examples in examples/
```

To use it from another project, put this directory on the include path
(`mojo run -I path/to/proptest-repo ...`), or build a package with
`pixi run package` (writes `build/proptest.mojoc`). There is also a conda
recipe (`conda.recipe/`); proptest will go on the modular-community
channel once Mojo 1.3 is released (see `docs/publishing.md`).

## Writing tests

`given` takes one to six strategies and a test function with a matching
signature. It runs the test on generated values (100 by default) and raises
an `Error` describing the shrunk counterexample if the test fails:

```mojo
from proptest import given, integers, lists, Settings

def test_sum_is_commutative() raises:
    def prop(a: Int, b: Int) raises:
        assert_equal(a + b, b + a)
    given(integers(), integers(), prop)

def test_reversing_twice() raises:
    def prop(xs: List[Int]) raises:
        var ys = xs.copy()
        ys.reverse()
        ys.reverse()
        assert_equal(xs, ys)
    given(lists(integers()), prop, Settings(max_examples=1000))
```

The test functions are ordinary nested functions; they can capture outer
values with a capture list (`def prop(x: Int) raises {var limit}: ...`).
Tests fit `std.testing.TestSuite` as usual.

Inside a test, `assume(condition)` rejects the current input (like
Hypothesis's `assume`), and `fail(msg)` fails the test.

For tests that need to draw data as they go, use `given_data`, whose test
receives the `ConjectureData` itself (Hypothesis's `st.data()`):

```mojo
def prop(mut data: ConjectureData) raises:
    var xs = data.draw(lists(integers(), min_size=1), "xs")
    var i = data.draw(integers(0, len(xs) - 1), "i")
    data.note(String("checking index ", i))
    data.target(Float64(len(xs)))      # targeted search: prefer long lists
    ...
given_data(prop)
```

After shrinking, proptest checks which arguments of the minimal example
can vary freely without changing the failure (Hypothesis's *explain*
phase) and says so:

```
Falsifying example (tests/test_example.mojo:8:14):
    given(
        11,
        '',  # or any other generated value
        0,  # or any other generated value
    )
    # The test always failed when commented parts were varied together.
```

`find(strategy, condition)` returns the simplest value satisfying a
condition, and `example(strategy)` returns a random value, for exploring
strategies.

### Strategies

| proptest | Hypothesis | values |
| --- | --- | --- |
| `integers(min, max)` | `integers()` | `Int` (bounds default to `Int.MIN`/`Int.MAX`) |
| `integers_of[DType.uint8](min, max)` | `integers()` | `Scalar[dtype]`, any integer dtype |
| `floats(min, max, allow_nan=, allow_infinity=, allow_subnormal=, exclude_min=, exclude_max=)` | `floats()` | `Float64` |
| `floats32(...)` | `floats(width=32)` | `Float32` |
| `booleans()` | `booleans()` | `Bool` |
| `just(x)`, `lazy_just(f)` | `just()` | always `x`; a fresh `f()` per test case |
| `sampled_from([a, b, c])` | `sampled_from()` | one of the elements; `weights=[...]` biases the choice |
| `one_of(s1, ..., s6, weights=)`, `one_of(list_of_boxed, weights=)` | `one_of()`, `s1 \| s2` | a value from any of them (same type), chosen in proportion to the optional integer `weights`; shrinks towards the first |
| `lists(s, min_size=, max_size=)` | `lists()` | `List[T]` |
| `unique_lists(s, ...)`, `unique_lists_by(s, key, ...)` | `lists(unique=True)`, `lists(unique_by=)` | `List[T]` |
| `sets(s, ...)` | `sets()` | `Set[T]` |
| `dictionaries(keys, values, ...)` | `dictionaries()` | `Dict[K, V]` |
| `tuples(s1, s2, ...)` (2 to 6) | `tuples()` | `Tuple[...]` |
| `shared(s, key=)` | `shared()` | one value per test case for each key |
| `optionals(s)` | `none() \| s` | `Optional[T]` |
| `text(alphabet, min_size=, max_size=)` | `text()` | `String` (any codepoint but surrogates by default) |
| `characters(min_codepoint=, max_codepoint=, categories=, exclude_categories=, include_characters=, exclude_characters=, codec=)` | `characters()` | one-character `String` (categories are Unicode general categories, e.g. `["Lu", "Nd"]` or `["L"]`) |
| `from_regex(pattern, fullmatch=)` | `from_regex()` | `String` matching (or, by default, containing a match of) a regex |
| `from_type[T]()` | `from_type()`, `builds()` | `T`: scalars, `String`, `List`/`Optional`/`Set`/`Dict` and tuples nested to any depth, any `Arbitrary` type (including the constraint types), and structs built field by field |
| `binary(min_size=, max_size=)` | `binary()` | `List[UInt8]` |
| `permutations(list)` | `permutations()` | `List[T]` |
| `subsequence(list, min_size=, max_size=)` | — (Rust `sample::subsequence`) | order-preserving sublists |
| `functions[A](returns)` | `functions()` | memoized `Function[A, R]`, printed as `{x->y, ...}` |
| `map(s, f)` | `s.map(f)` | `f(x)` |
| `apply(s1, ..., sN, f)` | `builds(f, s1, ...)` | `f(a1, ..., aN)`, two to six arguments (RapidCheck's `gen::apply`) |
| `filter(s, pred, reason=)` | `s.filter(pred)` | `x` with `pred(x)`; `reason` names the condition in health checks |
| `filter_map(s, f)` | — (Rust `prop_filter_map`) | `f(x)` where it isn't `None` |
| `flatmap(s, f)` | `s.flatmap(f)` | a value from `f(x)` |
| `composite(f)` | `@composite` | `f(data)` where `f` draws with `data.draw(...)` |
| `recursive(base, extend, max_leaves=)` | `recursive()` | recursive data |
| `boxed(s)` → `BoxedStrategy[T]` | — | type-erased strategy |

Combinators are free functions (`map(s, f)`, not `s.map(f)`): Mojo traits
cannot yet have default methods generic over closures of the strategy's
value type. `f` and `pred` can be top-level functions, closures, or lambdas
(`map(integers(), lambda (x: Int) {} -> Int: x * 2)`).

### Writing a strategy

A strategy is a struct conforming to `Strategy`, with an associated `Value`
type and a `do_draw` method that draws from other strategies or makes
primitive choices on the `ConjectureData`:

```mojo
@fieldwise_init
struct Point(Copyable, Writable):
    var x: Int
    var y: Int

struct Points(Strategy, Copyable):
    comptime Value = Point
    def __init__(out self):
        pass
    def do_draw(self, mut data: ConjectureData) raises -> Point:
        return Point(data.draw(integers(0, 100)), data.draw(integers(0, 100)))
```

Values must be `Movable` and `Writable` (so failures can be printed), but
need not be `Copyable`: the engine rebuilds values from choices rather
than copying them, so move-only types such as unique handles work, and
`lazy_just(f)` makes a fresh one per test case. `just`, `sampled_from`,
`permutations`, `shared`, set elements and dictionary keys need
`Copyable` values.
`composite(f)` does the same for a plain function.

### Strategies from types

`from_type[T]()` picks a strategy at compile time. Scalars, `Bool`,
`String`, `List`, `Optional`, `Set`, `Dict` and tuples (up to six
elements) are supported, nested to any depth. A type can provide its own
strategy by implementing `Arbitrary` (Hypothesis's
`register_type_strategy`); other structs are built field by field using
Mojo's reflection, recursively:

```mojo
@fieldwise_init
struct Range(Arbitrary, Copyable, Writable):
    var lo: Int
    var hi: Int

    @staticmethod
    def arbitrary(mut data: ConjectureData) raises -> Self:
        var lo = data.draw(integers(-100, 100))
        return Self(lo, data.draw(integers(lo, 100)))

@fieldwise_init
struct Point(Copyable, Writable):
    var x: UInt16
    var y: UInt16

@fieldwise_init
struct Sprite(Copyable, Writable):
    var position: Point         # built field by field
    var extent: Range           # uses Range.arbitrary
    var tags: List[String]
    var layer: Optional[Int8]

given(from_type[Sprite](), prop)
```

Building from fields bypasses `__init__`, so give types with invariants an
`Arbitrary` implementation.

`build[T](field["name"](strategy), ...)` builds a struct the same way, but
draws the named fields from the given strategies (RapidCheck's
`gen::build`). Field names and the strategies' value types are checked at
compile time:

```mojo
build[Sprite](field["layer"](just(Optional[Int8](0))), field["tags"](lists(text(), max_size=3)))
```

### Type-directed tests

`check(prop)` draws each of the property's arguments with `from_type`, so
the parameter types are the whole specification (quickcheck's
`quickcheck(prop)`). The property can raise, like a `given` test, or return
`Bool`:

```mojo
from proptest import check

def test_sprites() raises:
    def prop(s: Sprite, scale: UInt8) raises:
        assert_true(s.extent.lo <= s.extent.hi)
    check(prop)

def test_addition_commutes() raises:
    def prop(a: Int, b: Int) raises -> Bool:
        return a + b == b + a
    check(prop, Settings(max_examples=1000))
```

It takes one to six arguments and reports failures like `given`.

A property can also return an `Outcome` (`Outcome.passed()`,
`Outcome.discard()`, `Outcome.fail("why")` or `Outcome.of(cond, "why")`),
which can reject inputs as well as fail on them (quickcheck's
`TestResult`).

For generic code, `PolyA`, `PolyB` and `PolyC` are opaque stand-in types
that support only equality, ordering, hashing and printing (QuickCheck's
`Poly`): `check` a property over `List[PolyA]` rather than `List[Int]`,
and it can't pass because of something particular to `Int`. `Index` is a
position drawn before the collection it indexes is known:
`i.get(len(xs))`.

### Constraint types

When the plain types don't say enough, wrap them (QuickCheck's modifiers).
Each wrapper implements `Arbitrary`, so it works with `check`, `from_type`
and struct fields alike, and shrinking never breaks the constraint. The
value is `.value`, and reports print it without the wrapper:

```mojo
def prop(xs: NonEmpty[List[Int]], i: NonNegative[Int]) -> Bool:
    return xs.value[i.value % len(xs.value)] in xs.value
check(prop)
```

| Type | Values |
|---|---|
| `Bounded[lo, hi]`, `Bounded[lo, hi, UInt8]` | `lo <= value <= hi` (default type `Int`) |
| `Positive[T]`, `NonNegative[T]`, `NonZero[T]` | integer scalars, `Float64`, `Float32` (floats finite) |
| `NonEmpty[T]` | a `List`, `String`, `Set` or `Dict` with at least one element |
| `Sorted[List[T]]` | an ascending list of `Comparable` elements |
| `Blind[T]` | any `T`, printed as `<hidden>` |
| `Via[f]` | the value `f(data)` draws, for any `def f(mut data: ConjectureData) raises -> T` |

`Via` names any strategy in a type:

```mojo
def digits(mut data: ConjectureData) raises -> List[Int]:
    return data.draw(lists(integers(0, 9), max_size=4))

def prop(xs: Via[digits], n: Positive[UInt8]) -> Bool: ...
```

Use `given` with explicit strategies when strategies depend on each other
or on run-time values.

### Results and negative tests

`run_property(strategy, test)` runs a property like `given` but returns a
`PropertyResult` instead of raising. It holds whether it passed, the typed
shrunk `counterexample`, the report `message`, a reproduce `blob`, and the
`RunReport` with counts and statistics. `expect_failure(f)` runs a test
function that should fail (a negative control: does this property, with
these generators, find the bug?) and returns the failure report, raising if
the test passes.

### Settings

```mojo
given(s, prop, Settings(
    max_examples=500,          # valid examples to try
    seed=UInt64(1234),         # reproducible runs (or derandomize=True)
    database=None,             # don't save failures (default: .proptest/examples)
    phases=Phases(shrink=False),  # also explain=False to skip explaining
    verbosity=Verbosity.verbose,
    report_multiple_bugs=False,
    suppress_health_check=[HealthCheck.filter_too_much],
    deadline=500.0,            # ms per example (default 200; None disables)
    print_blob=True,           # print a blob for reproduce=
))
```

As in Hypothesis, an example whose test body takes longer than `deadline`
(time spent generating its data excluded) fails with `DeadlineExceeded`,
and a strategy whose data generation is slow fails the `too_slow` health
check. In stateful tests the deadline applies to each step. With `print_blob=True` (or verbose output) a failure report includes
a line like

```
To reproduce this example, run the test with Settings(reproduce="proptest1:aToxMDAxCg==")
```

and running the test with that setting replays exactly that example, with
no search (Hypothesis's `@reproduce_failure`).

To debug the shrunk failure itself, set a breakpoint on
`before_minimal_test_case`, which is called just before the final replay
(RapidCheck's `rc::beforeMinimalTestCase`). In `mojo debug` or
`mojo-lldb`: `breakpoint set -r before_minimal_test_case`. Its argument is
the test's location, for a conditional breakpoint.

Settings left at their defaults can be set from the environment, like a
Hypothesis profile: `PROPTEST_MAX_EXAMPLES`, `PROPTEST_SEED`,
`PROPTEST_VERBOSITY` (`quiet`/`normal`/`verbose`/`debug`) and
`PROPTEST_DATABASE` (a directory, or `none`).

Failing examples are saved in the example database (`.proptest/examples`,
one directory per test, keyed by the test's source location) and replayed
first on the next run, so a failure keeps failing until it is fixed.

### Statistics and coverage

`Settings(show_statistics=True)` (or verbose output) prints what the
generate phase saw. It counts three things:
- events recorded with `data.event(...)`, as a share of test cases
  (Hypothesis's `--hypothesis-show-statistics`);
- values recorded with `data.tabulate(table, value)` (QuickCheck);
- coverage requirements declared with `data.cover(percent, condition, label)`
  (QuickCheck).

The strategy wrappers `cover(s, percent, label, pred)` and
`tabulate(s, table, key)` do the same for `given` and `check` tests, which
have no `data`:

```mojo
var xs = cover(lists(integers()), 20, "long", lambda (xs: List[Int]) -> Bool: len(xs) >= 5)
given(xs, prop, Settings(check_coverage=Confidence()))
```

```
proptest statistics for tests/test_x.mojo:12:5:
  - 100 passing, 0 invalid and 0 overrun examples (generate phase)
  - Coverage:
    * 41.00% long (required 20.0%)
```

An unmet requirement prints a warning. With
`check_coverage=Confidence(certainty=1e9, tolerance=0.9)` it is checked
statistically instead, as QuickCheck's `checkCoverage` does:
- Generation continues past `max_examples`, checking at 1×, 2×, 4×, ...
  until every requirement is known to hold (to within `tolerance`) or
  one is known to fail.
- Each conclusion is wrong with probability about `1 / certainty`.
- A failure raises `Insufficient coverage`.

This catches generators that quietly stop producing the interesting
cases. The statistics are also in the `RunReport` that `run_test`
returns (`report.statistics`).

### Stateful testing

Stateful tests generate whole programs: sequences of operations ("rules")
against a system, with invariants checked after each step. Hypothesis
finds rules by reflection; a Mojo state machine numbers them:

```mojo
from proptest.stateful import StateMachine, Bundle, run_state_machine_as_test

struct DieHard(StateMachine):
    var small: Int
    var big: Int

    def __init__(out self):
        self.small = 0
        self.big = 0

    def rule_count(self) -> Int:
        return 6

    def rule_name(self, rule: Int) -> String: ...
    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises: ...

    def check_invariants(self) raises:
        if self.big == 4:
            fail("the big jug holds exactly 4 gallons")

run_state_machine_as_test[DieHard](Settings(max_examples=10000))
```

finds (typically within a thousand programs) and shrinks the solution to the water jug puzzle from *Die Hard 3*
(see `examples/die_hard.mojo`):

```
state = DieHard()
state.fill_big()
state.pour_big_into_small()
state.empty_small()
state.pour_big_into_small()
state.fill_big()
state.pour_big_into_small()
state.teardown()
```

`precondition(rule)` enables rules conditionally, rules draw their
arguments with `data.draw(strategy, "name")` (printed in the steps),
`Bundle[T]` passes values between steps, and `initialize_count`/
`run_initialize` give rules that run once, first. As in Hypothesis, each
test case disables a random subset of the rules ("swarm testing"), which
makes runs that hammer a few operations much more likely.

#### Typed state machines

A `TypedStateMachine` replaces rule numbers with a `Transition` type
(Rust's proptest-state-machine). Each step draws a transition from the
current state, then applies it; failures print the transitions through
`Writable`. A `Variant` with one struct per operation works well:

```mojo
from std.utils import Variant
from proptest import TypedStateMachine, run_typed_state_machine_as_test

@fieldwise_init
struct Push(Copyable, Writable):
    var x: Int

@fieldwise_init
struct Pop(Copyable, Writable):
    pass

struct StackMachine(TypedStateMachine):
    comptime Transition = Variant[Push, Pop]
    var model: List[Int]
    var stack: MyStack

    def __init__(out self): ...

    def transition(self, mut data: ConjectureData) raises -> Self.Transition:
        if len(self.model) == 0 or data.draw(booleans()):
            return Push(data.draw(integers()))
        return Pop()                      # only when there is something to pop

    def apply(mut self, t: Self.Transition) raises:
        if t.isa[Push]():
            self.model.append(t[Push].x)
            self.stack.push(t[Push].x)
        else:
            assert_equal(self.stack.pop(), self.model.pop())

run_typed_state_machine_as_test[StackMachine]()
```

```
state = StackMachine()
state.apply(Push(x=0))
state.apply(Pop())
state.teardown()
```

Draw only valid transitions: when the shrinker deletes a step, the later
ones are drawn again in the new state, so they stay valid. An optional
`precondition(t)` rejects a transition instead; after three rejections in
a row the program ends there. `check_invariants` and `teardown` work as
for `StateMachine`. There is no swarm testing, because the runner can't
tell kinds of transition apart.

#### Model-based testing with commands

`Command` (from RapidCheck's `rc::state` and Erlang QuickCheck) keeps the
model apart from the system under test. Each operation is a struct naming
the `Model` and `Sut` types. It generates itself from the model, and has
an optional `precondition(model)`, `next_state(mut model)`, and
`run(model, mut sut)`, which acts on the system and checks the result
against the model's state before the step:

```mojo
@fieldwise_init
struct Put(Command):
    comptime Model = Dict[Int, Int]
    comptime Sut = KvStore
    var key: Int
    var value: Int

    @staticmethod
    def generate(model: Self.Model, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 9)), data.draw(integers()))

    def next_state(self, mut model: Self.Model) raises:
        model[self.key] = self.value

    def run(self, model: Self.Model, mut sut: Self.Sut) raises:
        sut.put(self.key, self.value)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Put(", self.key, ", ", self.value, ")")

# Get and Remove likewise; then, for a KvStore with a default constructor:
check_commands[Put, Get, Remove](Dict[Int, Int]())
```

If the store forgets an overwritten value once it has held three keys,
the failure is reported as the shrunk program:

```
given([Put(0, 0), Put(1, 0), Put(2, 0), Put(0, 1), Get(0)])
```

`commands[Put, Get, Remove](model)` is a strategy for whole programs
(`Commands[Put, Get, Remove]`), generated from the model alone, so the
system isn't needed to generate or validate them. A program runs inside an
ordinary property with `program.run(model, sut)`. The property can
generate the initial state, use a fixture, or run the same program on two
implementations and compare them. `run_commands(model, sut, data)` draws
and runs one inside `given_data`. `commands(..., weights=[...])` biases the
choice of command type, and `max_commands` (default 50) bounds the length.

Compared with `TypedStateMachine`, each operation's code lives in its own
struct instead of an `isa` chain in `apply`, and the whole program is
known before it runs. A command that picks a value out of the model, such
as an existing key, shrinks less well, because deleting an earlier step
changes which value the same choice picks. Draw directly with a
`precondition` when rejections would be rare.

`examples/lru_cache.mojo` tests an LRU cache this way, with a capacity
drawn per test case and a model that is a plain list in recency order.
`examples/lru_cache_pointers.mojo` is the same cache with heap-allocated
nodes linked by raw pointers, checked by the same model plus a link
invariant after every step, and clean under `--sanitize address`.

## How it works

The engine is a port of Hypothesis's Conjecture
(`hypothesis.internal.conjecture`):

| proptest | Hypothesis | |
| --- | --- | --- |
| `internal/choice.mojo` | `choice.py` | typed choices, constraints, the simplicity order |
| `internal/data.mojo` | `data.py` | `ConjectureData`: recording choices and spans |
| `internal/provider.mojo` | `providers.py`, `statistics.py` | random generation with "nasty" values |
| `internal/datatree.mojo` | `datatree.py` | novelty and exhaustion of the search space |
| `internal/engine.mojo` | `engine.py`, `optimiser.py` | phases: reuse, generate (with mutation), target |
| `internal/shrinker.mojo` | `shrinker.py` | the shrink passes |
| `internal/shrinking.mojo` | `shrinking/*.py`, `junkdrawer.py` | integer, float, ordering and collection shrinkers |
| `internal/floats.mojo` | `floats.py` (both) | lexicographic float encoding |
| `internal/intervals.mojo` | `intervalsets.py` | codepoint sets |
| `internal/charmap.mojo` (+ generated `charmap_data.mojo`) | `charmap.py` | Unicode general categories |
| `internal/pareto.mojo` | `pareto.py` | the Pareto front of targeted examples |
| `strategies/regex.mojo` | `strategies/_internal/regex.py` | `from_regex` |
| `strategies/types.mojo` | `strategies/_internal/types.py` | `from_type` |
| `strategies/constraints.mojo` | — (QuickCheck's `Modifiers.hs`) | constraint types (`Positive`, `NonEmpty`, `Via`, ...) |
| `strategies/` | `strategies/_internal/` | strategies |
| `core.mojo`, `settings.mojo`, `database.mojo`, `stateful.mojo` | `core.py`, `_settings.py`, `database.py`, `stateful.py` | the public API |
| `commands.mojo` | (RapidCheck's `rc::state`) | model-based testing with `Command` structs |

A test case is a sequence of choices (integers, floats, booleans, byte
strings and strings), each drawn under constraints. Every choice type has
a simplicity order, and one sequence is simpler than another if it is
shorter, or the same length and simpler at the first difference. The
shrinker only ever moves to simpler sequences, so it always terminates;
because strategies replay from the sequence, any simpler sequence that
still fails is a simpler failing example.

### Differences from Hypothesis

[docs/differences-from-hypothesis.md](docs/differences-from-hypothesis.md)
explains the reasons for each of these and what would be practical to
port next.

- Integers are 128-bit rather than arbitrary precision (enough for every
  Mojo integer type).
- Hypothesis's interesting-origin (exception type and location) becomes the
  `At file:line:col:` prefix that `std.testing` assertions and `fail()` put
  on error messages; errors without one count as one bug.
- `@reproduce_failure` is the `reproduce=` setting.
- `from_type` works at compile time, from field reflection; `check(prop)`
  infers strategies from the property's parameter types through overload
  resolution, not signature reflection; `from_regex` supports the
  common subset of regex syntax (no backreferences, lookaround or word
  boundaries).
- No alternative backends, observability, or the date/time, email and IP
  strategies; NumPy's counterpart is the separate `proptest_numojo` package
  (`extras/`).
- The shrinker does not port `widen_to_span_with_recorded_value`. The Pareto optimization of
  targeted examples is limited to 10 × `max_examples` calls.
- The `DataTree` is uncompressed.
- When a replayed choice no longer fits (the test now draws under different
  constraints), an out-of-range integer is clamped into range rather than
  replaced by the simplest value. After the shrinker deletes part of a
  collection, an index into it then keeps pointing at the end, which lets
  stateful tests shrink further.
- Strings are lists of codepoints inside the engine.
- The database is a directory of text files, one choice per line.

## Layout

```
proptest/           the package (see "How it works")
tests/              the test suite: pixi run test
examples/           pixi run examples
extras/             proptest_numojo (NuMojo array strategies): pixi run test-numojo
tools/              generator for the Unicode tables (charmap_data.mojo, decomposition_data.mojo)
docs/               differences-from-hypothesis.md, publishing.md
conda.recipe/       conda package recipe (rattler-build) and its smoke test
```

### NuMojo arrays

`extras/proptest_numojo` is the counterpart of `hypothesis.extra.numpy`:
`arrays[dtype](shape, elements)`, `array_shapes(min_dims=, max_dims=,
min_side=, max_side=)`, `from_dtype[dtype]()`, `broadcastable_shapes`,
`mutually_broadcastable_shapes`, `basic_indices` (whose values index an
array with `index.apply(a)`) and `integer_array_indices`. It's a separate package so
proptest doesn't depend on NuMojo; put both on the include path
(`-I extras -I <dir containing numojo>`). `pixi run test-numojo` uses the
Mojo 1.3-patched NuMojo vendored by MojoDEC next to this repository, or
`$NUMOJO_PARENT`.

## License

The MIT License (MIT)
