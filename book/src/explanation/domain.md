# Domain and distribution

A strategy has two properties that are easy to confuse:

- its **domain**: the set of values it can produce;
- its **distribution**: how likely each of those values is.

`integers(0, 100)` has the domain 0 to 100. Its distribution isn't
uniform: proptest generates 0, 100, and other boundary values more often
than chance would, along with "nasty" values that tend to find bugs.

## Choose the domain to match the property

The domain is the part you control, and the part that matters. A test
should generate every input for which the property is supposed to hold.
If `my_sort` should work for any list of integers, test it with
`lists(integers())`, not `lists(integers(0, 100), max_size=10)`. A narrower
domain only tests a narrower claim.

Narrow the domain when the property genuinely doesn't apply outside it:
`floats(allow_nan=False)` for code that's documented not to accept `NaN`.
The constraint types (`Positive[T]`, `NonEmpty[T]`) are a way of writing
the domain into the test's signature.

## Why you don't control the distribution

proptest doesn't offer settings for the probabilities of particular
values, for the same reasons as Hypothesis:

- The best distribution for finding bugs isn't a natural one. Bugs cluster
  at boundaries, at special values, and in unusual combinations, so the
  engine deliberately over-represents those.
- The distribution changes during a run: proptest starts with small,
  simple inputs, mutates inputs it has seen, and steers towards new
  behaviour. A fixed distribution would fight this.
- Shrinking doesn't depend on the distribution, so there's no need to bias
  towards small values to get small counterexamples.

There are two exceptions, both from other libraries: `one_of` and
`sampled_from` accept `weights`, for when one alternative really should
appear more often; and `cover` lets you *check* the distribution where it
matters, rather than control it. See
[Check the distribution of inputs](../how-to/coverage.md).

## What the distribution is

It's an implementation detail, and it changes between versions. Roughly:

- each choice is sometimes forced to a special value (a bound, zero, a
  "nasty" float such as `NaN` or the smallest subnormal) and otherwise
  drawn at random;
- collections continue with a probability chosen to give a moderate
  average size;
- after the first few test cases, many are mutations of earlier ones, and
  later ones are guided towards unexplored choice sequences.

To see what a particular strategy produces, use `example`, or record
statistics with `tabulate` and `Settings(show_statistics=True)`.
