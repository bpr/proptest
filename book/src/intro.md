# proptest

proptest is a property testing framework for [Mojo](https://www.modular.com/mojo)
(i.e., the QuickCheck family) inspired by the
[Hypothesis](https://hypothesis.works/) framework for Python, with ideas
from Rust's [proptest](https://github.com/proptest-rs/proptest) and
[quickcheck](https://github.com/BurntSushi/quickcheck), Haskell's
[QuickCheck](https://github.com/nick8325/quickcheck), and C++'s
[RapidCheck](https://github.com/emil-e/rapidcheck).

With proptest, you write tests that should pass for every input in a range
you describe, and proptest chooses which of those inputs to try, including
edge cases you might not have thought of. When it finds an input that fails,
it *shrinks* it to a minimal failing example before reporting it:

```mojo
from std.testing import assert_true
from proptest import given, lists, integers
~
~def my_sort(xs: List[Int]) -> List[Int]:
~    var ys = xs.copy()
~    sort(ys)
~    return ys^

def test_sort_is_ordered() raises:
    def prop(xs: List[Int]) raises:
        var ys = my_sort(xs)
        for i in range(1, len(ys)):
            assert_true(ys[i - 1] <= ys[i])
    given(lists(integers()), prop)
~
~def main() raises:
~    test_sort_is_ordered()
```

proptest is built on Hypothesis's *Conjecture* engine. Strategies don't
generate values directly: they parse them from a recorded sequence of
choices, and the shrinker simplifies that sequence. Shrinking therefore
works for every strategy, including the ones you write yourself, without
any shrinking code of your own. The other libraries contributed most of
the typed API: inferring inputs from a property's parameter types,
constraint types such as `Positive[T]`, coverage checking, and
model-based testing.

## How this book is organized

The book follows the layout of the
[Hypothesis documentation](https://hypothesis.readthedocs.io/):

- **[Quickstart](quickstart.md)**: the essentials on one page.
- **Tutorial**: an introduction to proptest, from a first test through
  strategies, settings, the example database, and stateful testing. Start
  here if you're new to property-based testing.
- **How-to guides**: recipes for particular tasks, such as checking the
  distribution of your inputs or debugging a failure.
- **Explanations**: how proptest works, and why it is the way it is.
- **Reference**: every test function, setting, and strategy.

Where proptest behaves differently from Hypothesis, the book says so. The
[differences document](https://github.com/bpr/proptest/blob/master/docs/differences-from-hypothesis.md)
in the repository has the full list, with the reason for each.

## Requirements

proptest needs **Mojo 1.3** or later. Until Mojo 1.3.0 is released, that
means the nightly channel. See [Introduction to proptest](tutorial/introduction.md#installing-proptest)
for installation.
