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
corpus entries: changing runs of values, to random values, to boundary
values (0, -1, the bounds of the range, powers of two near the limits of
machine integers, infinities, NaN) or to their simplest values,
overwriting runs of bytes or characters within a string, and copying a
strategy's choices from one test case into another, or deleting,
duplicating or cutting them off. It keeps only the simplest test case for
each thing covered, and mutates the entries that cover rarely seen things
most often, so a test whose common paths produce many variants doesn't
bury the few that got further. A test case that `assume` or a filter
rejects is kept too if it covered something no valid test case has, as a
step toward one that does (it is mutated less often, and dropped once a
valid test case covers the same things).

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
10000 inputs; corpus of 11
```

When it finds no failure, `fuzz` returns a `FuzzReport` of what it did,
which prints as `N inputs (V valid) in Ts; corpus of C covering F
features`. With a database, the corpus is saved under
`<database_key>.fuzz`, and the next run starts from it, and failures are
saved under the test's key, as `given` saves them.

`fuzz(..., guided=False)` turns the guidance off: every test case is
generated afresh, as `given` generates them, and the report still counts
the features covered. Comparing the two shows how much the guidance
helps a given test.

## Get past magic values

Some checks are all but impossible to pass by chance: `x == 20261114`
holds for one integer in 2<sup>64</sup>. Fuzzers get past them by
watching the program's comparisons and trying the values it compares
with. proptest can't see your code's comparisons, but a `Traced` value
can: draw it with `traced(...)` and it records every comparison it takes
part in. `fuzz` then tries setting the choice that produced the value
to what it was compared with (and, for integers, one either side of it;
for strings, also the current string with it added at the front or the
back). It also counts getting closer than before at a comparison as
covering something new, which helps when the compared value is
computed from several draws:

```mojo
from proptest import fuzz_target, traced, integers, text, fail
from proptest import Settings, Traced


def main() raises:
    def check(code: Traced[Int], cmd: Traced[String]) raises:
        if code == 20261114 and cmd.startswith("UNLOCK"):
            fail("unlocked")

    var target = fuzz_target(
        traced(integers()),
        traced(text()),
        check,
        Settings(database=None, seed=UInt64(1)),
    )
    try:
        _ = target.fuzz(10)
    except e:
        print(e)
```

```text
Falsifying example (magic.mojo:10:29):
    given(20261114, 'UNLOCK')
At magic.mojo:8:17: AssertionError: unlocked
```

It takes about a hundred inputs; without `traced`, `fuzz` doesn't find
it at all. `Traced[T]` works for integers of any width and `String`,
and conforms to `Comparable` and `Hashable`, so you can pass it to
generic code, whose comparisons are recorded too. To trace a value
computed in the test, wrap it yourself: `Traced(x + y,
data.comparisons)` in a test that draws its own data.

Arithmetic on a `Traced` value gives a `Traced` value too. When the
result was computed from one drawn value by steps that can be undone
(adding, subtracting, multiplying, shifting left, XOR, negating, and
`~` for integers; adding text at either end for strings), a comparison
also works out what the drawn value would need to be, and `fuzz` tries
that:

```mojo
from proptest import fuzz_target, traced, integers, fail
from proptest import Settings, Traced


def main() raises:
    def check(x: Traced[Int]) raises:
        var checksum = (x * 31 + 7) ^ 0xBEEF
        if checksum == 0xBD8B68:
            fail("checksum matches")

    var target = fuzz_target(
        traced(integers()),
        check,
        Settings(database=None, seed=UInt64(1)),
    )
    try:
        _ = target.fuzz(10)
    except e:
        print(e)
```

```text
Falsifying example (checksum.mojo:11:29):
    given(400000)
At checksum.mojo:9:17: AssertionError: checksum matches
```

The arithmetic wraps as the type's does, and the reverse steps wrap the
same way, but a multiplication is only undone when the division is
exact. Dividing, taking a remainder, `&`, `|` and `>>` lose track of
the drawn value; the result is still traced, so getting closer at its
comparisons still counts. When both operands are `Traced`, the result is
traced back to the left one (or the right one, if the left was already
lost) with the other taken as a constant.

The values compared with also join the "nasty" constants that `given`
and `fuzz` occasionally generate, so `given` tries them too.

## Use a dictionary

When the input is a text or binary format, the tokens it uses
(keywords, magic bytes, separators) are as hard to hit by chance as a
magic number. List them in `Settings(dictionary=...)`, as you would give
AFL++ or libFuzzer a dictionary: `fuzz` then inserts tokens into strings
and byte strings, writes them over part of a value or in place of it
(up to three at a time, so tokens can appear together), and sets
integers to the tokens that are numbers (`42`, `-1`, `0x7f`). `given`
and `fuzz` also generate a token whole now and then.

```mojo
from proptest import fuzz_target, text, fail, Settings


def main() raises:
    def handle(request: String) raises:
        if request.startswith("POST /admin"):
            fail("reached the admin page")

    var target = fuzz_target(
        text(),
        handle,
        Settings(
            database=None,
            seed=UInt64(1),
            dictionary=["GET", "POST", " ", "/admin", "/index", "HTTP/1.1"],
        ),
    )
    try:
        _ = target.fuzz(30)
    except e:
        print(e)
```

```text
Falsifying example (admin.mojo:9:29):
    given('POST /admin')
At admin.mojo:7:17: AssertionError: reached the admin page
```

Without the dictionary, `fuzz` doesn't find it. For tokens that
aren't text, or a dictionary you already have, `load_dictionary(path)`
reads the AFL++/libFuzzer format (one `name="value"` per line, with
`\xNN` escapes, as in AFL++'s `dictionaries/` directory), and
`parse_dictionary(text)` reads it from a string. A token that isn't
valid UTF-8 is used only for byte strings. A dictionary and `traced`
work together: the dictionary supplies the tokens, and `traced` values
supply the values the code compares with.

## Fuzz model-based tests

A program from `commands()` (see [Stateful testing](../tutorial/stateful.md)) is
a value like any other, so `fuzz_target` takes one. What `fuzz` can
see of it, though, is only what the commands drew, and the bugs that
model-based tests find are usually in states that take many steps to
reach. Give `commands` a `fingerprint`, a function from the model to
an abstract state, and each abstract state a program reaches (and each
command type run in one) counts as covering something new, so `fuzz`
keeps the programs that get somewhere new and extends them.

Here a stack loses an item when it's popped back below depth 12, and
`Pop` and `Clear` keep random programs shallow. With the depth as the
fingerprint, `fuzz` finds the bug in about 800 inputs, where it takes
about 8,000 without:

```mojo
from proptest import Command, Commands, ConjectureData, Settings
from proptest import commands, fuzz_target, integers


struct Stack(Movable):
    """A stack that loses an item when popped back below depth 12."""

    var items: List[Int]

    def __init__(out self):
        self.items = []

    def pop(mut self) raises:
        _ = self.items.pop()
        if len(self.items) == 11:
            raise Error("lost an item")


@fieldwise_init
struct Push(Command):
    comptime Model = Int  # the depth
    comptime Sut = Stack
    var x: Int

    @staticmethod
    def generate(model: Int, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 9)))

    def next_state(self, mut model: Int) raises:
        model += 1

    def run(self, model: Int, mut sut: Stack) raises:
        sut.items.append(self.x)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Push(", self.x, ")")


@fieldwise_init
struct Pop(Command):
    comptime Model = Int
    comptime Sut = Stack

    @staticmethod
    def generate(model: Int, mut data: ConjectureData) raises -> Self:
        return Self()

    def precondition(self, model: Int) raises -> Bool:
        return model > 0

    def next_state(self, mut model: Int) raises:
        model -= 1

    def run(self, model: Int, mut sut: Stack) raises:
        sut.pop()

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Pop()")


@fieldwise_init
struct Clear(Command):
    comptime Model = Int
    comptime Sut = Stack

    @staticmethod
    def generate(model: Int, mut data: ConjectureData) raises -> Self:
        return Self()

    def next_state(self, mut model: Int) raises:
        model = 0

    def run(self, model: Int, mut sut: Stack) raises:
        sut.items.clear()

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Clear()")


def depth(model: Int) raises -> UInt64:
    return UInt64(model)


def main() raises:
    def prop(program: Commands[Push, Pop, Clear]) raises:
        var stack = Stack()
        program.run(0, stack)

    var target = fuzz_target(
        commands[Push, Pop, Clear](0, fingerprint=depth),
        prop,
        Settings(database=None, seed=UInt64(1)),
    )
    try:
        _ = target.fuzz(10)
    except e:
        print(e)
```

```text
Falsifying example (stack.mojo:89:29):
    given([Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Push(0), Pop()])
lost an item
```

Make the fingerprint coarse: a size, a few flags, which keys a store
holds rather than their values. If almost every state is new, nothing
stands out, and the corpus fills with programs that differ only in
detail. The fingerprint must be a function without captures. To report
coverage from any test, call `data.feature(x)` with a `UInt64` that
identifies what the test case reached; a new one counts like a new
`event`.

## Fuzz many tests at once

A long fuzzing session is best spent on the tests that are still
finding new behavior. `fuzz_all(target, ...)` fuzzes several targets in
turn, in slices of a tenth of a second, and gives each slice to the
target expected to cover something new soonest: the one with the fewest
test cases since it last did, for its speed (HypoFuzz's approach). Tests
that have stopped finding anything get a slice now and then, in case.
A target that fails stops there; the rest go on until the time is up,
and then every failure is raised together:

```mojo
from proptest import fuzz_all, fuzz_target, integers, lists, text, fail
from proptest import Settings


def main() raises:
    def reverse_twice(xs: List[Int]) raises:
        var ys = xs.copy()
        ys.reverse()
        ys.reverse()
        if ys != xs:
            fail("reversing twice changed the list")

    def trim(s: String) raises:
        if String(s.strip()).byte_length() > s.byte_length():
            fail("strip made it longer")

    def halve(x: Int) raises:
        if x > 0 and x // 2 >= x:
            fail("halving didn't shrink it")

    def mean(xs: List[Int]) raises:
        if len(xs) == 0:
            return
        var total = 0
        for x in xs:
            total += x
        if total // len(xs) > 1000:
            fail("mean too big")

    var settings = Settings(database=None)
    var a = fuzz_target(lists(integers()), reverse_twice, settings)
    var b = fuzz_target(text(), trim, settings)
    var c = fuzz_target(integers(), halve, settings)
    var d = fuzz_target(lists(integers(0, 10_000)), mean, settings)
    try:
        var reports = fuzz_all(a, b, c, d, seconds=5)
        for r in reports:
            print(r)
    except e:
        print(e)
```

```text
proptest: fuzz_all: campaign.mojo:34:24 failed (reported at the end)
Falsifying example (campaign.mojo:34:24):
    given([1001])
At campaign.mojo:28:17: AssertionError: mean too big
```

Without a failure, `fuzz_all` returns each target's `FuzzReport`.
`max_inputs=` caps the test cases across all the targets, and
`verbose=True` prints each target's totals. Each target keeps its
corpus (in the database too, as with `fuzz`), so a later `fuzz_all` or
`fuzz` goes on from there. Unlike `fuzz`, a target doesn't go on
looking for other bugs once it has failed.

## Crashes

A fuzzer usually finds crashes, not errors. With `Settings(fork=True)`
each input runs in a child process (see [Test code that
crashes](crashes.md)), and a crash raises a `Crash` error from
`fuzz_one_input` and is saved like any other failure, while the fuzzing
process goes on. Without it, a crash ends the process, and the fuzzer
must save the input itself. `fuzz` shrinks a crash as `given` does.

## Settings

`database`, `database_key`, `fork`, `timeout` and `dictionary` apply to a fuzz target.
`fuzz` also uses `seed`, `verbosity` (`Verbosity.verbose` prints its
progress every five seconds), `phases.shrink`, `phases.explain` and
`report_multiple_bugs`. There is no deadline.
`fuzz_target_data(test)` makes a target from a test that draws its own
data, as `given_data` does.
