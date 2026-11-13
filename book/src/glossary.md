# Glossary

**Choice.** A single primitive decision made while generating a test case:
an integer, float, boolean, byte string, or string, drawn under
constraints such as a range.

**Choice sequence.** The choices a test case made, in order. Strategies
build values from it, so replaying the sequence rebuilds the values. The
example database, reproduce blobs, and the shrinker all work on choice
sequences.

**Command.** In model-based testing, a struct representing one operation:
it generates itself from the model, updates the model, and runs on the
system under test.

**Constraint type.** A wrapper type such as `Positive[T]` or `NonEmpty[T]`
that puts a constraint on generated values in the type.

**Coverage requirement.** A declaration, with `cover`, that some share of
test cases should satisfy a condition.

**Distinct failure.** A failure with its own *origin*, the location its
error was raised. Distinct failures are shrunk and reported separately.

**Example database.** The directory where proptest saves the choice
sequences of failing test cases, to replay them in later runs.

**Explain phase.** After shrinking, the phase that finds which arguments of
the minimal example can vary without changing the failure.

**Explicit example.** An input given by hand to `check_examples`, always
tested, never shrunk.

**Health check.** A check that the test can be tested well: that its
strategies don't reject too much, or generate data too large or too slow.

**Invalid test case.** A test case rejected by `assume`, a filter, or
`Outcome.discard()`. Invalid test cases don't count towards
`max_examples`.

**Minimal example.** The failing input proptest reports: the result of
shrinking.

**Model.** A simple value describing the state a system under test should
be in, used to check the system's behavior.

**Overrun.** A test case abandoned because it made too many choices.

**Property.** A statement that should hold for every input in a domain,
written as a test function.

**Shrinking.** Searching for a simpler failing test case by simplifying the
choice sequence of a failing one.

**Span.** A run of choices that together make one value, recorded by
`data.draw`. The shrinker uses spans to delete, reorder, and simplify
values.

**State machine.** A stateful test, defined as rules or transitions that
are run in random sequences against a system.

**Strategy.** A description of the values a test should be given: a struct
conforming to `Strategy`, which draws a value from a `ConjectureData`.

**SUT.** System under test.

**Swarm testing.** Disabling a random subset of a state machine's rules in
each test case, to make lopsided programs more likely.

**Targeting.** Steering the search towards inputs with high scores, reported
with `data.target`.

**Test case.** One run of the test function on one generated input.
