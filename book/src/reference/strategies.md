# Strategies

Every strategy function returns a struct conforming to `Strategy`, whose
type is given after `->`. Functions marked `raises` check their arguments
and raise `InvalidArgument` errors. "Shrinks towards" describes the
simplest value.

## Numbers

### `integers`

```mojo-sig
integers(min_value: Optional[Int] = None, max_value: Optional[Int] = None) raises -> Integers
```

`Int` values in `[min_value, max_value]`. Omitted bounds are the limits of
`Int`. Shrinks towards 0, or the bound nearest 0.

### `integers_of`

```mojo-sig
integers_of[dtype: DType](min_value: Optional[Scalar[dtype]] = None,
                          max_value: Optional[Scalar[dtype]] = None) raises -> ScalarIntegers[dtype]
```

Integers of any integer `DType` (`UInt8`, `Int32`, `UInt64`, ...),
defaulting to the type's full range.

### `floats`

```mojo-sig
floats(min_value: Optional[Float64] = None, max_value: Optional[Float64] = None, *,
       allow_nan: Optional[Bool] = None, allow_infinity: Optional[Bool] = None,
       allow_subnormal: Bool = True, exclude_min: Bool = False,
       exclude_max: Bool = False) raises -> Floats
```

`Float64` values in the range. `allow_nan` defaults to true when there are
no bounds; `allow_infinity` to true when a bound is missing.
`exclude_min`/`exclude_max` make a bound exclusive. Shrinks towards 0, then
towards simple integers and fractions.

### `floats32`

```mojo-sig
floats32(min_value: Optional[Float64] = None, max_value: Optional[Float64] = None, *,
         allow_nan: Optional[Bool] = None, allow_infinity: Optional[Bool] = None) raises -> Floats32
```

`Float32` values (Hypothesis's `floats(width=32)`).

### `booleans`

```mojo-sig
booleans() -> Booleans
```

`True` or `False`, shrinking towards `False`.

## Text

### `text`

```mojo-sig
text(alphabet: Optional[String] = None, *, min_size: Int = 0,
     max_size: Optional[Int] = None) raises -> Text
text(alphabet: Characters, *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> Text
```

Strings whose length in codepoints is in `[min_size, max_size]`, made of
the characters of `alphabet`: a string of allowed characters, or a
`characters(...)` strategy. By default, any codepoint except surrogates
(which UTF-8 can't encode). Shrinks towards shorter strings, and towards
`'0'`.

### `characters`

```mojo-sig
characters(*, min_codepoint: UInt32 = 0, max_codepoint: UInt32 = 0x10FFFF,
           categories: List[String] = [], exclude_categories: List[String] = [],
           include_characters: String = "", exclude_characters: String = "",
           codec: Optional[String] = None) raises -> Characters
```

Single characters, as one-character `String`s. `categories` are Unicode
general categories (`"Lu"`, `"Nd"`, or a major class like `"L"`), from
Unicode 17.0. `codec` is `"ascii"`, `"latin-1"`, or `"utf-8"`.

### `from_regex`

```mojo-sig
from_regex(pattern: String, *, fullmatch: Bool = False) raises -> Regex
```

Strings that contain a match of `pattern`, or, with `fullmatch=True`, that
match it entirely. It supports the common subset of Python's syntax:

- literals and escapes (`\n`, `\xHH`, `\uHHHH`, ...);
- `.`, classes (`[abc]`, `[a-z]`, `[^...]`), and `\d \D \w \W \s \S`,
  which are Unicode-aware as in Python;
- groups `( )`, `(?: )`, `(?P<name> )`, and alternation `|`;
- the quantifiers `* + ? {n} {n,} {n,m} {,m}`, with lazy and possessive
  forms;
- the anchors `^ $ \A \Z`, and the flags `(?i)` and `(?s)` at the start.

Backreferences, lookaround, word boundaries, conditionals, and other flags
raise `InvalidArgument`.

### `binary`

```mojo-sig
binary(*, min_size: Int = 0, max_size: Optional[Int] = None) raises -> Binary
```

Byte strings (`List[UInt8]`).

## Collections

### `lists`

```mojo-sig
lists(elements: S, *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> Lists[S]
```

`List[S.Value]` with length in `[min_size, max_size]`. Shrinks by deleting
elements, then by shrinking the rest.

### `unique_lists`, `unique_lists_by`

```mojo-sig
unique_lists(elements: S, *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> UniqueValues[S]
unique_lists_by(elements: S, key: F, *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> UniqueLists[S, K, F]
```

Lists of distinct values (`S.Value` must be `KeyElement & Copyable`), or of
values with distinct `key(x)` (Hypothesis's `lists(unique=True)` and
`lists(unique_by=key)`).

### `sets`

```mojo-sig
sets(elements: S, *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> Sets[S]
```

`Set[S.Value]`; the values must be `KeyElement & Copyable`.

### `dictionaries`

```mojo-sig
dictionaries(keys: KS, values: VS, *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> Dictionaries[KS, VS]
```

`Dict[KS.Value, VS.Value]`; keys must be `KeyElement & Copyable`.

### `tuples`

```mojo-sig
tuples(s1, s2) -> Tuples2[S1, S2]
...                                      # up to six: Tuples6
```

`Tuple` of a value from each strategy.

### `optionals`

```mojo-sig
optionals(strategy: S) -> Optionals[S]
```

`None` or a value from `strategy`, shrinking towards `None`.

## Choosing

### `just`, `lazy_just`

```mojo-sig
just(value: T) -> Just[T]                 # T: Copyable
lazy_just(f: def() raises -> T) -> LazyJust[T, F]
```

Always `value`; or `f()`, called afresh for each test case, for values that
can't or shouldn't be copied. Neither makes any choices.

### `sampled_from`

```mojo-sig
sampled_from(elements: List[T]) raises -> SampledFrom[T]
sampled_from(elements: List[T], *, weights: List[Int]) raises -> SampledFrom[T]
```

One of `elements`, shrinking towards the first. `weights` (positive, one
per element) make each element's probability proportional to its weight.

### `one_of`

```mojo-sig
one_of(s1, s2) -> Alternatives[S1, S2]
one_of(s1, s2, *, weights: List[Int]) raises -> Alternatives[S1, S2]
...                                      # up to six strategies
one_of(strategies: List[BoxedStrategy[T]]) raises -> OneOf[T]
one_of(strategies: List[BoxedStrategy[T]], *, weights: List[Int]) raises -> OneOf[T]
```

A value from one of the strategies, which must all produce the same type;
shrinks towards the first. The fixed-arity forms store the strategies
unboxed. The weights only bias generation; they don't change shrinking.

### `permutations`

```mojo-sig
permutations(values: List[T]) -> Permutations[T]
```

Reorderings of `values`, shrinking towards the original order.

### `subsequence`

```mojo-sig
subsequence(values: List[T], *, min_size: Int = 0, max_size: Optional[Int] = None) raises -> Subsequences[T]
```

Sublists of `values` that keep their order (Rust proptest's
`sample::subsequence`), shrinking towards dropping elements.

## Transforming

### `map`

```mojo-sig
map(strategy: S, f: def(S.Value) raises -> R) -> Mapped[S, R, F]
```

`f(x)` for `x` from `strategy` (Hypothesis's `strategy.map(f)`).

### `apply`

```mojo-sig
apply(s1, s2, f: def(S1.Value, S2.Value) raises -> R) -> Applied2[S1, S2, R, F]
...                                      # up to six strategies: Applied6
```

`f(a1, ..., aN)` with each argument from its strategy (RapidCheck's
`gen::apply`, Hypothesis's `builds` with a function). The function comes
last.

### `filter`

```mojo-sig
filter(strategy: S, predicate: def(S.Value) raises -> Bool, *, reason: String = "") -> Filtered[S, F]
```

Values for which `predicate` holds. Each test case tries three times
before it's rejected. `reason` names the condition in the
`filter_too_much` health check.

### `filter_map`

```mojo-sig
filter_map(strategy: S, f: def(S.Value) raises -> Optional[R], *, reason: String = "") -> FilterMapped[S, R, F]
```

`f(x)` where it isn't `None` (Rust proptest's `prop_filter_map`).

### `flatmap`

```mojo-sig
flatmap(strategy: S, f: def(S.Value) raises -> S2) -> FlatMapped[S, S2, F]
```

Draw `x` from `strategy`, then a value from the strategy `f(x)`.

### `composite`

```mojo-sig
composite(f: def(mut ConjectureData) raises -> T) -> Composite[T, F]
```

A strategy from a function that draws with `data.draw(...)` (Hypothesis's
`@composite`).

### `recursive`

```mojo-sig
recursive(base: S, extend: def(BoxedStrategy[T]) raises -> BoxedStrategy[T], *,
          max_leaves: Int = 100) raises -> Recursive[T]
```

Recursive data: values from `base`, or from `extend(s)`, where `s` is the
recursive strategy itself, up to about `max_leaves` base values per
example.

### `shared`

```mojo-sig
shared(base: S, key: Optional[String] = None) -> Shared[S]
```

One value per test case: every draw from a `shared` strategy with the same
key returns the same value. Without a key, draws from the same `shared(...)`
call (and copies of it) share; separate calls don't. Hypothesis shares by
object identity instead.

### `boxed`

```mojo-sig
boxed(strategy: S) -> BoxedStrategy[S.Value]      # S: Copyable
```

The same values, with the strategy's type erased. Useful for lists of
strategies, recursion, and functions that return strategies.

## Statistics

### `cover`

```mojo-sig
cover(strategy: S, percent: Float64, label: String, condition: def(S.Value) raises -> Bool) -> Covered[S, F]
```

Values from `strategy`, requiring that `condition` holds for at least
`percent`% of test cases (QuickCheck's `cover`).

### `tabulate`

```mojo-sig
tabulate(strategy: S, table: String, key: def(S.Value) raises -> String) -> Tabulated[S, F]
```

Values from `strategy`, recording `key(value)` in the statistics table
`table` (QuickCheck's `tabulate`).

## Types

### `from_type`

```mojo-sig
from_type[T: Drawable]() -> FromType[T]
```

Values of `T`, with the strategy chosen at compile time. See
[Types](types.md).

### `build`, `field`

```mojo-sig
build[T](field["name"](strategy), ...) -> Built[T, *Fs]
```

A struct built field by field, with the named fields drawn from the given
strategies. See [Types](types.md#build-and-field).

### `functions`

```mojo-sig
functions[A](returns: S) -> Functions[A, R]
```

Memoized functions from `A` to values of `returns`. See
[Generate functions](../how-to/functions.md).

### `commands`

```mojo-sig
commands[*Cs: Command](model, *, max_commands: Int = 50) -> CommandSequences[*Cs]
commands[*Cs: Command](model, *, weights: List[Int], max_commands: Int = 50) raises -> CommandSequences[*Cs]
```

Programs of commands. See [Stateful and model-based testing](stateful.md).

## NuMojo arrays

In the separate `proptest_numojo` package: `arrays`, `array_shapes`,
`from_dtype`, `broadcastable_shapes`, `mutually_broadcastable_shapes`,
`basic_indices`, and `integer_array_indices`. See
[Generate NuMojo arrays](../how-to/numojo.md).
