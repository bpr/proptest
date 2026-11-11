# Debug a failing test

proptest's report gives the shrunk input and the error. When that isn't
enough to see the bug, these tools help.

## Replay just the failing example

With `Settings(print_blob=True)`, the report includes a blob:

```text
To reproduce this example, run the test with Settings(reproduce="proptest1:aToxMDEK")
```

Rerun the test with that setting, and proptest runs exactly that example,
once, without searching or shrinking. Add print statements or a debugger,
and you'll see only the failing case.

The example database does nearly the same automatically: the next run of
the test tries the saved failure first. But it then goes on to search and
shrink, so you'll see other test cases too.

## Stop on the minimal example in a debugger

A debugger breakpoint in the test stops on every test case, including the
hundreds that pass and the many tried while shrinking. Instead, set a
breakpoint on `before_minimal_test_case`, which proptest calls just before
the final replay of a shrunk failure (RapidCheck's
`rc::beforeMinimalTestCase`). When it stops there, set the breakpoints you
need in the test, and continue.

```text
$ mojo build -I path/to/proptest -g my_test.mojo -o my_test
$ mojo-lldb my_test
(lldb) breakpoint set -r before_minimal_test_case
(lldb) run
...
* thread #1, stop reason = breakpoint 1.1
    frame #0: my_test`proptest::core::before_minimal_test_case(::String)
(lldb) breakpoint set -f my_test.mojo -l 42
(lldb) continue
```

The function's argument is the test's location, for a conditional
breakpoint when a program has several failing tests.

## When the test crashes

A test that segfaults or aborts takes the run down with it, before
proptest can shrink anything. Run it with `Settings(fork=True)`; see
[Test code that crashes](crashes.md).

## See what the test computed

- **Notes**: in a `given_data` test, `data.note(...)` adds lines to the
  report, printed only for the final example.
- **Labels**: `data.draw(strategy, "name")` names each drawn value in the
  report.
- **Messages**: `std.testing` assertions take a message, and `fail(msg)`
  fails with one.

## See what proptest is doing

`Settings(verbosity=Verbosity.verbose)` (or `PROPTEST_VERBOSITY=verbose`)
prints the counts and seed of each run, the run's statistics, and the
reproduce blob. `Verbosity.debug` also prints every test case (its
status and choices), each successful shrink, and how well each shrink pass
did. That's a lot of output, meant for working on strategies or on
proptest itself.

## Turn off shrinking

If shrinking is slow, or you want to see the input as first found,
`Settings(phases=Phases(shrink=False, explain=False))` reports the first
failure unshrunk.

## Read the explain comments

After shrinking, proptest tries varying each argument of the minimal
example. Arguments that don't affect the failure are marked:

```text
Falsifying example (test.mojo:8:14):
    given(
        11,
        '',  # or any other generated value
        0,  # or any other generated value
    )
    # The test always failed when commented parts were varied together.
```

Here only the first argument matters, which narrows the search for the
cause.
