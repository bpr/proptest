# Tips and limitations

## Tips

### Start with simple properties

The most useful first property is often "doesn't crash": call the code on
generated input and check nothing else. It finds a surprising number of
bugs, and tells you what input the code actually accepts. Then add round
trips (`decode(encode(x)) == x`), invariants, and comparisons with a
simpler implementation.

### Generate valid inputs instead of filtering

Construct the inputs you need: draw a list, then an index into it; draw a
lower bound, then an upper bound above it. Filtering with `filter` or
`assume` discards work, and if it discards most of it, the test fails a
health check.

### Keep test cases small

Large inputs are slow to generate, to run, and to shrink. Pass `max_size`
to collection strategies when the code under test doesn't need large
inputs to show its behaviour; most bugs show up with small ones.

### Compare against a model

A slow, obviously correct implementation is a powerful oracle. A
`Dict` can model a hash table, a sorted `List` a priority queue. Stateful
and model-based tests are built around this idea.

### Check that the test can fail

A property that can't fail tests nothing. Plant a bug and run the test
with [`expect_failure`](../how-to/negative-tests.md), or look at the
statistics to see whether the inputs you care about are generated.

### Make values readable

Counterexamples are printed with `write_to`. A short, clear form makes
reports easier to read: `Interval(0, 5)`, not every field with its name.

### Keep tests deterministic

Draw all randomness through proptest, and don't let state leak between
test cases. See [Flaky failures](../tutorial/flaky.md).

## Limitations

### Property-based testing finds bugs; it doesn't prove their absence

A passing run means proptest didn't find a failure in the inputs it tried.
Bugs that need very particular inputs (a specific 64-bit value, say) may
never be generated. Targeting, explicit examples, and boundary-heavy
generation help, but a passing property test isn't a proof.

### Some properties are hard to state

Code whose correct output is hard to describe without reimplementing it is
hard to test this way. Partial properties still help: the output has the
right length, is sorted, contains only elements of the input.

### Tests run many times

A property test runs the code hundreds of times, which is slow if each run
is slow. Lower `max_examples` for expensive tests, and run more examples in
CI or nightly.

### Mojo-specific limitations

- `given` and `check` take at most six arguments; use `tuples`, a struct,
  or `given_data` for more.
- Generated values must be `Writable`.
- Struct fields of types that can't be reflected or drawn need an
  `Arbitrary` implementation or an explicit strategy.
- `from_regex` supports the common subset of regular expressions: no
  backreferences, lookaround, or word boundaries.
