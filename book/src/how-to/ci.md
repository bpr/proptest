# Run proptest in CI

Property tests run as ordinary Mojo test programs, so a CI job runs them
the way it runs any other test. A few settings are worth choosing
deliberately for CI.

## Disable the example database

The database lets a failure persist between runs on one machine. In CI,
nothing is kept between jobs, so the database only adds files. Disable it
for every test that uses the default:

```sh
export PROPTEST_DATABASE=none
```

## Decide between fresh and repeatable runs

By default, every run uses a new random seed. That's what you want most of
the time: each CI run explores new inputs, and over time the suite tests
far more than any single run does. A failure that appears in CI shows its
example in the log, and with `print_blob=True` or verbose output, a blob to
reproduce it.

If you need every run to be identical (for a release check, say),
`Settings(derandomize=True)` derives each test's seed from the test, or
`PROPTEST_SEED=1234` fixes the seed for every test that doesn't set one.

## Run more examples

CI machines can afford more examples than a developer's edit-test loop.
`PROPTEST_MAX_EXAMPLES` raises `max_examples` for every test that leaves it
at the default:

```sh
PROPTEST_MAX_EXAMPLES=1000 mojo run -I . tests/test_parser.mojo
```

A nightly job with a much larger number is a cheap way to find rare bugs.

## Watch the deadline

The default deadline is 200 ms per example. Shared CI machines can be much
slower than a workstation, which makes slow tests fail with
`DeadlineExceeded` or flaky deadline errors. Give slow tests an explicit
`deadline` (or `None`).

## Print what's needed to reproduce

With `PROPTEST_VERBOSITY=verbose`, each failure report includes the seed
and a reproduce blob, at the cost of more output for passing tests.
`Settings(print_blob=True)` on important tests includes just the blob.

## Using proptest from a pixi project

Until proptest is on the modular-community channel, a project can use it
from a checkout:

```toml
[tasks]
test = "mojo run -I ../proptest tests/test_all.mojo"
```

or from a built `proptest.mojoc` (`pixi run package` in the proptest
repository), put on the include path.
