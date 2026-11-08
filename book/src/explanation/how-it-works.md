# How proptest works

proptest's engine is a port of Hypothesis's *Conjecture* engine. This
page explains its main ideas: choice sequences, shrinking, the phases of a
run, and how distinct bugs are told apart.

## Choice sequences

A strategy doesn't produce values from a random number generator directly.
It makes *choices* through the `ConjectureData`: draw an integer in this
range, a float, a boolean with this probability, a string from these
codepoints, a byte string. Each choice is recorded. A test case is the
sequence of choices it made, and the values are whatever the strategies
built from those choices.

This has a crucial consequence: given the same choice sequence, the
strategies rebuild the same values. So a test case can be replayed, saved,
and, most importantly, *modified*. Change a choice and replay, and the
strategies build a different but related value.

Choices are grouped into *spans*, one for each `data.draw(strategy)`, so
the engine knows which choices belong to which value: this run of choices
is one list element, that one is a dictionary key. Spans are why a custom
strategy should draw through `data.draw` rather than calling another
strategy's `do_draw`.

## Shrinking

Every kind of choice has a *simplicity order*: smaller integers (nearer
the "shrink towards" point) are simpler, `False` is simpler than `True`,
shorter strings are simpler, and so on. One choice sequence is simpler than
another if it's shorter, or the same length and simpler at the first
choice where they differ.

The shrinker takes a failing choice sequence and tries simpler ones,
keeping any that still fail. Its *passes* each try a kind of change:

- replace a span with its simplest form;
- delete runs of choices (which removes list elements, or steps of a
  program);
- replace a span with one of its descendants (a tree with a subtree);
- reorder spans with the same label, such as list elements;
- simplify each choice: lower an integer, simplify a float towards an
  integer, shorten a string;
- lower duplicated choices, or pairs of integers, together;
- and the others in Hypothesis's shrinker, which proptest ports.

Because the shrinker only moves to simpler sequences, it always ends. And
because strategies rebuild values from choices, every simpler failing
sequence is a simpler failing *value*, with all the strategies' invariants
intact. This is the main advantage over shrinking values directly, as
QuickCheck and Rust's proptest do: no strategy needs a shrinker of its own,
shrinking works through `map`, `flatmap`, and `filter`, and a shrunk value
is always one the strategy could have produced.

## The phases of a run

A run of `given` goes through these phases, each of which can be turned off
with `Phases`:

1. **explicit**: run explicit examples.
2. **reuse**: replay failures saved in the example database.
3. **generate**: generate new test cases. The first is the simplest
   possible input; early test cases are kept small, and later ones
   explore further. Some test cases mutate earlier ones rather than
   starting fresh.
4. **target**: hill-climb on the scores reported with `data.target`.
5. **shrink**: shrink each distinct failure.
6. **explain**: for the shrunk failure, find which arguments can vary
   without changing the outcome, and mark them in the report.

Generation is guided by a tree of the choice sequences tried so far, so
proptest doesn't run an identical test case twice, and knows when the
search space is exhausted.

## Distinct failures

A run can find several bugs. proptest tells them apart by their *origin*:
the location of the error. The `std.testing` assertions and `fail()` put
an `At file:line:col:` prefix on their errors, and failures at different
locations are treated as different bugs, each shrunk separately and
reported together (with `report_multiple_bugs=True`, the default):

```text
proptest found 2 distinct failures.

--- Failure 1 of 2 ---
Falsifying example (...):
...
```

Without this, shrinking one bug can slip into another: the shrinker
happily keeps a simpler input that fails for a different reason, and you
end up with a minimal example of the wrong bug. Errors without a location
prefix all count as one origin.

## The example database

The database maps each test to the choice sequences of its failures. It
stores choices, not values, so saved examples replay through the test's
current strategies. It's a directory of small text files, one per example,
one choice per line.

## Further reading

- [How many times will proptest run my test?](test-case-count.md)
- David R. MacIver and Alastair F. Donaldson, "Test-Case Reduction via
  Test-Case Generation: Insights from the Hypothesis Reducer", ECOOP 2020.
- The engine's source is in `proptest/internal/`; the
  [README](https://github.com/bpr/proptest#how-it-works) maps each file
  to its Hypothesis original.
