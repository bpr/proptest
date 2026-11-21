# Run slow tests in parallel

A test whose test cases are slow, because each one builds a program,
starts a process, or waits on a network, spends almost all its time in
the test, not in proptest. `Settings(workers=k)` runs the generate phase
in `k` processes at once, so 100 test cases of a second each take about
`100 / k` seconds:

```mojo
from proptest import expect_failure, given, integers, fail, Settings
from std.ffi import external_call


def compile_and_run(n: Int) -> Int:
    # stands in for something slow: building a program, a network call
    _ = external_call["usleep", Int32](UInt32(20_000))
    return n if n < 1000 else n + 1  # BUG


def main() raises:
    def round_trips(n: Int) raises:
        if compile_and_run(n) != n:
            fail("wrong result")

    def run() raises:
        given(
            integers(0, 10_000),
            round_trips,
            Settings(database=None, workers=4, deadline=None),
        )

    print(expect_failure(run))
```

```text
Falsifying example (parallel.mojo:17:14):
    given(1000)
At parallel.mojo:14:17: AssertionError: wrong result
```

`workers=0` starts one worker per physical core, and `PROPTEST_WORKERS`
sets `workers` for tests that leave it at 1.

## How it works

The workers are `fork()`ed copies of the test process, as with
[`fork=True`](crashes.md). Each runs the generate and target phases with
its own seed and its share of `max_examples`. When one finds a failure,
the others stop after their current test case (or, with
`report_multiple_bugs`, after looking a little longer for other bugs, as a
single process does after its first failure). The failures come back to
the main process, which replays and shrinks them there, as usual.
Shrinking isn't parallel: each step depends on the one before.

Counts and [statistics](coverage.md) add up across the workers. A health
check that fails in a worker fails the test.

## When it helps

Starting a worker takes about 0.15 ms, and each one runs the simplest
test case again, so `workers` pays off when the test cases take a
millisecond or more each. Most properties take microseconds per test
case: 100 of them run in about 0.1 ms in one process, and in 0.7 ms with
four workers.

Because the workers are separate processes, the test doesn't need to be
thread-safe, but side effects of the generate phase, such as a variable
the test updates, stay in the workers. Workers that use the same files or
ports can get in each other's way: give each test case its own temporary
directory.

A worker that crashes ends only that worker; proptest reports the crash
and suggests `fork=True`, which works with `workers` and shrinks the
crashing test case.

`workers` is ignored with `check_coverage` (which decides when to stop
from all the test cases seen so far), with `reproduce=`, and by the fuzz
loop. A failure found with workers can differ from the one a single
process would have found with the same seed, since which worker gets
there first depends on timing; the `reproduce=` blob of the shrunk
failure still replays it exactly.
