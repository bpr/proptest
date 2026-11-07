# proptest

Property-based testing for Mojo: a port of
[Hypothesis](https://hypothesis.works/) to Mojo 1.3.

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

## Setup

proptest needs Mojo 1.3 or later (the nightly channel, via pixi):

```sh
pixi install
pixi run test        # the test suite
pixi run examples    # the examples in examples/
```

To use it from another project, put this directory on the include path
(`mojo run -I path/to/proptest-repo ...`), or build a package with
`pixi run package` (writes `build/proptest.mojoc`).

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
| `just(x)` | `just()` | always `x` |
| `sampled_from([a, b, c])` | `sampled_from()` | one of the elements |
| `one_of(s1, s2, ...)` | `one_of()`, `s1 \| s2` | a value from any of them (same type) |
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
| `from_type[T]()` | `from_type()`, `builds()` | `T`: scalars, `String`, `List`/`Optional`/`Set`/`Dict[String, _]` of them (nested one level), common pairs and triples, any `Arbitrary` type, and structs built field by field |
| `binary(min_size=, max_size=)` | `binary()` | `List[UInt8]` |
| `permutations(list)` | `permutations()` | `List[T]` |
| `map(s, f)` | `s.map(f)` | `f(x)` |
| `filter(s, pred)` | `s.filter(pred)` | `x` with `pred(x)` |
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

Values must be `Copyable` and `Writable` (so failures can be printed).
`composite(f)` does the same for a plain function.

### Strategies from types

`from_type[T]()` picks a strategy at compile time. A type can provide its own
by implementing `Arbitrary` (Hypothesis's `register_type_strategy`); other
structs are built field by field using Mojo's reflection, recursively:

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

Settings left at their defaults can be set from the environment, like a
Hypothesis profile: `PROPTEST_MAX_EXAMPLES`, `PROPTEST_SEED`,
`PROPTEST_VERBOSITY` (`quiet`/`normal`/`verbose`/`debug`) and
`PROPTEST_DATABASE` (a directory, or `none`).

Failing examples are saved in the example database (`.proptest/examples`,
one directory per test, keyed by the test's source location) and replayed
first on the next run, so a failure keeps failing until it is fixed.

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
| `strategies/types.mojo` (generated) | `strategies/_internal/types.py` | `from_type` |
| `strategies/` | `strategies/_internal/` | strategies |
| `core.mojo`, `settings.mojo`, `database.mojo`, `stateful.mojo` | `core.py`, `_settings.py`, `database.py`, `stateful.py` | the public API |

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
- `from_type` works at compile time, from field reflection, and can't
  infer strategies from a test's parameter types; `from_regex` supports the
  common subset of regex syntax (no backreferences, lookaround or word
  boundaries).
- No alternative backends, observability, or the date/time, email and IP
  strategies; NumPy's counterpart is the separate `proptest_numojo` package
  (`extras/`).
- The shrinker does not port `widen_to_span_with_recorded_value`. The Pareto optimisation of
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
tools/              generators for charmap_data.mojo and strategies/types.mojo
docs/               differences-from-hypothesis.md
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
