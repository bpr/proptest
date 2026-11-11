# Test code that crashes

A test that segfaults, aborts, or trips AddressSanitizer kills the
process, and proptest with it: you see the crash, but not the input that
caused it, and nothing is shrunk. Code that uses raw pointers fails this
way more often than it raises.

## `fork=True`

With `Settings(fork=True)`, each test case runs in a child process. A
crash then fails the test case like any other error, and proptest shrinks
it:

```mojo
from proptest import expect_failure, given, lists, integers, fail, Settings

def last(xs: List[Int]) -> Int:
    # BUG: no check for an empty list, which has no buffer
    return xs.unsafe_ptr()[unsafe_offset=len(xs) - 1]

def main() raises:
    def last_is_an_element(xs: List[Int]) raises:
        if last(xs) not in xs:
            fail("last isn't an element")

    def run() raises:
        given(
            lists(integers()),
            last_is_an_element,
            Settings(database=None, fork=True),
        )

    print(expect_failure(run))
```

```text
Falsifying example (crash.mojo:15:14):
    given([])
Crash: the test case was killed by SIGSEGV (signal 11), in a child process (Settings(fork=True))
```

Each signal is a distinct failure, as is each exit status, so a test that
can both segfault and abort reports both. A test case that exits before
it finishes, for example when AddressSanitizer finds a use after free and
exits with status 1, fails too. Build the test with `--sanitize address`
to catch memory errors that don't crash:

```text
mojo build -I . --sanitize address -o my_test my_test.mojo && ./my_test
```

While searching and shrinking, children's error output (sanitizer reports,
for instance) is discarded; the final replay of each shrunk failure shows
it, so you see one report, for the minimal example.

## `timeout`

`Settings(timeout=ms)` kills a test case that runs longer than `ms`
milliseconds and fails it with `Timeout`; it implies `fork=True`. Unlike
`deadline`, which times a test case that finishes, it catches one that
never does, such as an infinite loop in a linked list with a cycle.

## What changes in a child process

- The child gets a copy of the parent's memory, so a test's side effects
  (a counter it increments, a global cache it fills) stay in the child.
- Each test case costs a `fork()`: about 0.2 ms for a built binary, and a
  few milliseconds under `mojo run`. Build the test (`mojo build`) when
  running many test cases.
- Core dumps are off in the children, and crashes use the default signal
  handlers rather than Mojo's, which print a stack trace. To see the
  trace, replay the shrunk failure in-process: run the test without
  `fork` and with `Settings(reproduce=...)` (see
  [Debug a failing test](debugging.md)).
- Code that uses threads may deadlock in the child, where only the
  thread that called `fork()` exists.
- POSIX only (Linux and macOS).

`PROPTEST_FORK=1` in the environment turns `fork` on for tests that
don't set it.
