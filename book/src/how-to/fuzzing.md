# Drive a test from a fuzzer

`given` runs a test on `max_examples` inputs and stops. A fuzzer runs
for hours, mutating a corpus of byte strings and keeping the ones that do
something new. `fuzz_target` connects the two: it takes the same
arguments as `given`, and returns a `FuzzTarget` whose
`fuzz_one_input(bytes)` runs the test once, with its inputs read from the
bytes. This is Hypothesis's `fuzz_one_input`. Without a fuzzer,
`target.fuzz(seconds)` runs a fuzz loop of its own (see [Fuzz without a
fuzzer](#fuzz-without-a-fuzzer)).

```mojo
from proptest import fuzz_target, lists, integers, Settings
from std.testing import assert_equal


def encode(xs: List[Int]) -> String:
    var out = String()
    for i in range(len(xs)):
        if i > 0:
            out += ","
        out += String(xs[i])
    return out


def decode(s: String) raises -> List[Int]:
    var out = List[Int]()
    for part in s.split(","):  # BUG: "".split(",") is [""]
        out.append(atol(part))
    return out^


def main() raises:
    def round_trips(xs: List[Int]) raises:
        assert_equal(decode(encode(xs)), xs)

    var target = fuzz_target(
        lists(integers(-1000, 1000)), round_trips, Settings(database=None)
    )
    var inputs: List[List[UInt8]] = [
        [255, 3, 232, 255, 0, 7, 0, 99],
        [255, 3],
        [0],
    ]
    for input in inputs:
        try:
            var canonical = target.fuzz_one_input(input)
            if canonical:
                print("passed; canonical input:", canonical.value())
            else:
                print("not a valid input")
        except e:
            print("failed:", e)
```

```text
passed; canonical input: [255, 3, 232, 255, 0, 7, 0]
not a valid input
failed: String is not convertible to integer with base 10: ''
```

`fuzz_one_input` has three outcomes:

- **The test passed.** It returns the *canonical* bytes for the test
  case: the shortest input that replays it, with unused bytes dropped. A
  fuzzer can keep these in its corpus in place of the input.
- **The input isn't a valid test case.** It returns `None`: the bytes ran
  out before the strategies finished drawing (`[255, 3]` above starts a
  list element and stops halfway through it), or `assume` or a `filter`
  rejected the values.
- **The test failed.** It raises the test's error, after saving the
  failing example to the example database.

## How bytes become values

Each choice a strategy makes takes the next bytes of the input, so a
fuzzer's mutations of the bytes become changes to the values:

- an integer takes just enough bits to cover its range, big-endian
  (`integers(-1000, 1000)` takes 11 bits, so 2 bytes: `[3, 232]` is
  1000 above the minimum, 0);
- a boolean takes one byte, true when it is high enough for the
  boolean's probability;
- a float takes 65 bits, a sign and a magnitude, clamped into range;
- a list, or a string or byte string, takes a byte before each element
  that may or may not be there, saying whether there is one (high: yes;
  low: stop; `0` above is the empty list).

The encoding depends on the strategies and on the version of proptest,
like the example database.

## Replay fuzzing failures in your tests

A failure found by fuzzing is saved to the example database under the
target's `database_key`. Give the target and the ordinary test the same
key, and the test replays the failure, shrinks it, and reports it, the
next time it runs:

```mojo
from proptest import (
    fuzz_target, given, lists, integers, expect_failure, Settings, Phases
)
from std.testing import assert_true


def main() raises:
    def small_sum(xs: List[Int]) raises:
        var total = 0
        for x in xs:
            total += x
        assert_true(total < 1500, String("sum is ", total))

    var settings = Settings(
        database=".proptest-db", database_key="small_sum"
    )
    var target = fuzz_target(lists(integers(0, 1000)), small_sum, settings)
    # [continue, 1000, continue, 1000, stop]
    try:
        _ = target.fuzz_one_input([255, 3, 232, 255, 3, 232, 0])
    except e:
        print("fuzzing found:", e)

    # Later, the ordinary test replays the saved failure and shrinks it,
    # even with generation turned off.
    def run() raises:
        given(
            lists(integers(0, 1000)),
            small_sum,
            Settings(
                database=".proptest-db",
                database_key="small_sum",
                phases=Phases(generate=False),
            ),
        )

    print(expect_failure(run))
```

```text
fuzzing found: At small_sum.mojo:12:20: AssertionError: sum is 2000
Falsifying example (small_sum.mojo:27:14):
    given([500, 1000])
At small_sum.mojo:12:20: AssertionError: sum is 1500
```

Without a `database_key`, each defaults to its own call site, so the
keys differ. A long fuzzing run saves a failure only when it is simpler
than the last one saved with the same error, so the database grows
slowly even when the same bug is hit millions of times.

## Fuzz without a fuzzer

`target.fuzz(seconds)` is a fuzzer of its own: it runs the test for
`seconds` (or `max_inputs=` test cases, if that comes first), then
shrinks and reports any failures as `given` does. It works on choices,
not bytes. Like a coverage-guided fuzzer, it keeps a *corpus* of the test
cases that did something new, and makes most new test cases by mutating
corpus entries: changing a few values, to random values or to boundary
values (0, -1, the bounds of the range, powers of two near the limits of
machine integers, infinities, NaN), and copying a strategy's choices from
one test case into another, or deleting, duplicating or cutting them off.

proptest can't see which lines of the test ran, so "something new" means
something the strategies or the test reported: a strategy drawing from
another that hadn't before, or a different number of times (a longer
list, a deeper tree); an `event`; or a better `target` score. That's
enough to find inputs that random generation won't. Here the test marks
each digit of the code it gets right with an event, and `fuzz` finds the
code a digit at a time, where random generation would need about a
million tries (16<sup>5</sup>):

```mojo
from proptest import fuzz_target, fuzz_target_data, lists, integers, fail
from proptest import ConjectureData, Settings


def main() raises:
    def unlock(mut data: ConjectureData) raises:
        var code = data.draw(lists(integers(0, 15), min_size=5, max_size=5))
        for i in range(5):
            if code[i] != i + 1:
                return
            data.event(String("digit ", i + 1, " right"))
        fail("unlocked")

    var target = fuzz_target_data(
        unlock, Settings(database=None, seed=UInt64(1))
    )
    try:
        _ = target.fuzz(10)
    except e:
        print(e)

    def no_bug(xs: List[Int]) raises:
        pass

    var other = fuzz_target(
        lists(integers(0, 9)), no_bug, Settings(database=None, seed=UInt64(1))
    )
    var report = other.fuzz(max_inputs=10_000)
    print(report.inputs, "inputs; corpus of", report.corpus)
```

```text
Falsifying example (unlock.mojo:14:34):
    Draw 1: [1, 2, 3, 4, 5]
At unlock.mojo:12:13: AssertionError: unlocked
10000 inputs; corpus of 9
```

When it finds no failure, `fuzz` returns a `FuzzReport` of what it did,
which prints as `N inputs (V valid) in Ts; corpus of C covering F
features`. With a database, the corpus is saved under
`<database_key>.fuzz`, and the next run starts from it, and failures are
saved under the test's key, as `given` saves them.

## Crashes

A fuzzer usually finds crashes, not errors. With `Settings(fork=True)`
each input runs in a child process (see [Test code that
crashes](crashes.md)), and a crash raises a `Crash` error from
`fuzz_one_input` and is saved like any other failure, while the fuzzing
process goes on. Without it, a crash ends the process, and the fuzzer
must save the input itself. `fuzz` shrinks a crash as `given` does.

## Settings

`database`, `database_key`, `fork` and `timeout` apply to a fuzz target.
`fuzz` also uses `seed`, `verbosity` (`Verbosity.verbose` prints its
progress every five seconds), `phases.shrink`, `phases.explain` and
`report_multiple_bugs`. There is no deadline.
`fuzz_target_data(test)` makes a target from a test that draws its own
data, as `given_data` does.
