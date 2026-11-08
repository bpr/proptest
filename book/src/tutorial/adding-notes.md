# Adding notes and statistics

A failure report shows the inputs. Sometimes you also want to see values
the test computed from them, or to know what kinds of input the test saw
over a whole run. This page covers notes, events, and run statistics.

## Notes

`data.note(message)` adds a line to the failure report. Notes are only
printed for the final, shrunk example, so they don't clutter the output
while proptest searches. Notes need the `ConjectureData`, so use them from
`given_data` tests, `composite` strategies, or state machine rules:

```mojo
from proptest import given_data, integers, ConjectureData, Settings

def main():
    def prop(mut data: ConjectureData) raises:
        var x = data.draw(integers(0, 1000), "x")
        data.note(String("x squared is ", x * x))
        if x > 100:
            raise Error("too big")

    try:
        given_data(prop, Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (notes.mojo:10:19):
    Draw 1 (x): 101
    x squared is 10201
too big
```

In a `given` test, you can put the same information in the error message
instead: `std.testing` assertions take a message argument.

## Statistics

`Settings(show_statistics=True)` prints a summary of what the test saw
during the generate phase (Hypothesis's `--hypothesis-show-statistics`).
Verbose output includes it too. Three things feed it.

- **Events**: `data.event(label)` records that something happened in
  this test case. The statistics show the share of test cases that
  recorded each event.
- **Tables**: `data.tabulate(table, value)` (from QuickCheck) records a
  value in a named table. The statistics show how often each value
  occurred.
- **Coverage requirements**: `data.cover(percent, condition, label)`
  (from QuickCheck) says that at least `percent`% of test cases should
  satisfy `condition`.

```mojo
from proptest import given_data, lists, integers, ConjectureData, Settings

def main() raises:
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(0, 9)))
        data.event("empty" if len(xs) == 0 else "non-empty")
        data.tabulate("length", String(min(len(xs), 3)))
        data.cover(30, len(xs) >= 2, "two or more")

    given_data(prop, Settings(database=None, show_statistics=True))
```

```text
proptest statistics for stats.mojo:10:15:
  - 99 passing, 0 invalid and 19 overrun examples (generate phase)
  - Events:
    * 83.90%, non-empty
  - length (99 values):
    * 85.86%, 3
    * 9.09%, 2
    * 5.05%, 1
  - Coverage:
    * 94.95% two or more (required 30.0%)
```

Event percentages are of all test cases, including invalid and overrun
ones; table percentages are of the values recorded.

The statistics can be surprising. Here no empty list appears, because
proptest tries the simplest input first (an empty list, before the generate
phase) and never runs an identical input twice. And 19 test cases were
"overrun": early in a run, proptest keeps test cases small, and abandons
ones that grow too large. That's why it's worth looking at the statistics
when you write a new strategy.

### Statistics for `given` and `check` tests

`given` and `check` tests have no `data`. The strategy wrappers
`tabulate(s, table, key)` and `cover(s, percent, label, condition)` record
the same statistics for each value a strategy produces:

```mojo
from proptest import given, cover, tabulate, lists, integers, Settings

def bucket(xs: List[Int]) -> String:
    return "short" if len(xs) < 5 else "long"

def main() raises:
    def prop(xs: List[Int]) raises:
        pass

    var xs = tabulate(
        cover(lists(integers()), 20, "long", lambda (xs: List[Int]) -> Bool: len(xs) >= 5),
        "size",
        bucket,
    )
    given(xs, prop, Settings(database=None, show_statistics=True))
```

### Coverage requirements

An unmet `cover` requirement prints a warning. To make it a test failure,
checked with a statistical test so that it fails only when the coverage is
really too low, use `Settings(check_coverage=Confidence())`. See
[Check the distribution of inputs](../how-to/coverage.md).

### Statistics in code

The statistics are also available as data: `run_test` and `run_property`
return a `RunReport`, whose `statistics` field holds the counts, events,
tables, and coverage.
