# Stateful testing

So far, each test has checked a function on one input. Many bugs only show
up after a particular *sequence* of operations: add, add, remove, then
look up. Stateful testing generates whole programs, sequences of
operations against the system under test, and shrinks a failing program to
the shortest, simplest sequence that still fails.

proptest has three ways to write a stateful test:

- **`StateMachine`**: numbered *rules*, as in Hypothesis's
  `RuleBasedStateMachine`. Covered on this page.
- **`TypedStateMachine`**: each step is a value of a `Transition` type,
  as in Rust's proptest-state-machine. Also covered on this page.
- **Commands**: model-based testing with one struct per operation, as in
  RapidCheck and Erlang QuickCheck. Covered in
  [Model-based testing](model-based.md).

## A rule-based state machine

Here is a set that loses elements under some conditions:

```mojo
from std.testing import assert_true
from proptest import ConjectureData, integers, Settings
from proptest.stateful import StateMachine, run_state_machine_as_test

struct BuggySet(Movable):
    var items: List[Int]

    def __init__(out self):
        self.items = []

    def add(mut self, x: Int):
        if x > 10 and len(self.items) >= 2:
            return  # bug: silently drops the element
        for y in self.items:
            if y == x:
                return
        self.items.append(x)

    def contains(self, x: Int) -> Bool:
        for y in self.items:
            if y == x:
                return True
        return False

struct SetMachine(StateMachine):
    var real: BuggySet
    var model: List[Int]

    def __init__(out self):
        self.real = BuggySet()
        self.model = []

    def rule_count(self) -> Int:
        return 2

    def rule_name(self, rule: Int) -> String:
        return "add" if rule == 0 else "check"

    def precondition(self, rule: Int) -> Bool:
        return rule == 0 or len(self.model) > 0

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            var x = data.draw(integers(0, 100), "x")
            self.real.add(x)
            if x not in self.model:
                self.model.append(x)
        else:
            var i = data.draw(integers(0, len(self.model) - 1), "i")
            assert_true(self.real.contains(self.model[i]), "element went missing")

def main():
    try:
        run_state_machine_as_test[SetMachine](Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (set.mojo:54:46):
    state = SetMachine()
    state.add(x=0)
    state.add(x=1)
    state.add(x=11)
    state.check(i=2)
    state.teardown()
At set.mojo:50:24: AssertionError: element went missing
```

The machine holds the system under test (`real`) and a *model* of what its
state should be (`model`, a plain list). Each step:

1. picks a rule whose `precondition` holds;
2. calls `run_rule`, which draws the rule's arguments with
   `data.draw(strategy, "name")`, applies the operation to both the system
   and the model, and checks that they agree;
3. calls `check_invariants`.

The failure is printed as the program that caused it, with each rule's
arguments named by their labels. proptest found some long program first,
then shrank it to the essential steps: two small elements, then a large
one, then a lookup.

Hypothesis finds rules by looking for methods decorated with `@rule`. Mojo
has no decorators or method reflection, so a Mojo state machine numbers
its rules: `rule_count` says how many there are, `rule_name` names them for
reports, and `run_rule` dispatches on the number.

## Invariants

`check_invariants` runs after the machine is created and after every step.
Use it for properties that should always hold, whatever the last operation
was. The [Die Hard](https://github.com/bpr/proptest/blob/master/examples/die_hard.mojo)
example uses an invariant to solve the water jug puzzle from the film: it
claims that the 5-gallon jug never holds exactly 4 gallons, and proptest
finds and shrinks a sequence of pours that refutes it:

```text
state = DieHard()
state.fill_big()
state.pour_big_into_small()
state.empty_small()
state.pour_big_into_small()
state.fill_big()
state.pour_big_into_small()
state.teardown()
```

## Passing values between steps: bundles

Sometimes one step creates a value that later steps use: a handle returned
by `open`, a key inserted earlier. A `Bundle[T]` collects such values
(Hypothesis's `Bundle`):

```mojo
~from proptest import ConjectureData, Settings, Bundle, fail
~from proptest.stateful import StateMachine, run_state_machine_as_test
~
~struct Files(Movable):
~    var open_handles: List[Int]
~    var next: Int
~
~    def __init__(out self):
~        self.open_handles = []
~        self.next = 0
~
~    def open(mut self) -> Int:
~        self.next += 1
~        self.open_handles.append(self.next)
~        return self.next
~
~    def close(mut self, h: Int) raises:
~        for i in range(len(self.open_handles)):
~            if self.open_handles[i] == h:
~                _ = self.open_handles.pop(i)
~                return
~        fail(String("closed handle ", h, " twice"))
~
struct HandleMachine(StateMachine):
    var system: Files
    var handles: Bundle[Int]
~
~    def __init__(out self):
~        self.system = Files()
~        self.handles = Bundle[Int]("handles")
~
~    def rule_count(self) -> Int:
~        return 2
~
~    def rule_name(self, rule: Int) -> String:
~        return "open" if rule == 0 else "close"
~
~    def precondition(self, rule: Int) -> Bool:
~        return rule == 0 or len(self.handles) > 0

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            self.handles.add(self.system.open())
        else:
            var h = self.handles.consume(data)   # draw(data) would keep it
            self.system.close(h)
~
~def main() raises:
~    run_state_machine_as_test[HandleMachine](Settings(database=None))
```

`draw` picks one of the values, shrinking towards the most recently added;
`consume` also removes it. The rule's precondition must make sure the
bundle isn't empty. In reports, a drawn value is printed with the bundle's
name, such as `state.use(values[0]=500)`.

## Initialize rules and teardown

`initialize_count` and `run_initialize` define rules that run exactly once
each, before any ordinary rule, in a random order (Hypothesis's
`@initialize`). `teardown` runs at the end of every program, even a
failing one, for releasing resources.

## Swarm testing

In each test case, proptest disables a random subset of the rules, as
Hypothesis does. A program that only adds and never removes, say, is much
more likely than it would be if every step chose uniformly among all the
rules, and such lopsided programs find bugs that balanced ones miss.

## Settings for stateful tests

`run_state_machine_as_test[M](settings)` takes the usual `Settings`.
`stateful_step_count` (default 50) is the maximum number of steps per
program, and `max_examples` is the number of programs. The `deadline`
applies to each step separately.

## Typed state machines

A `TypedStateMachine` replaces rule numbers with values (Rust's
proptest-state-machine). Each step draws a *transition*, a value of the
associated `Transition` type, from the current state, then applies it. A
`Variant` with one struct per operation works well:

```mojo
from std.testing import assert_true
from std.utils import Variant
from proptest import ConjectureData, integers, booleans, Settings
from proptest import TypedStateMachine, run_typed_state_machine_as_test

struct BuggySet(Movable):
    var items: List[Int]

    def __init__(out self):
        self.items = []

    def add(mut self, x: Int):
        if x > 10 and len(self.items) >= 2:
            return  # bug: silently drops the element
        if x not in self.items:
            self.items.append(x)

    def contains(self, x: Int) -> Bool:
        return x in self.items

@fieldwise_init
struct Add(Copyable, Writable):
    var x: Int

@fieldwise_init
struct Check(Copyable, Writable):
    var i: Int

struct TypedSetMachine(TypedStateMachine):
    comptime Transition = Variant[Add, Check]
    var real: BuggySet
    var model: List[Int]

    def __init__(out self):
        self.real = BuggySet()
        self.model = []

    def transition(self, mut data: ConjectureData) raises -> Self.Transition:
        # only valid transitions: Check needs an element to look up
        if len(self.model) == 0 or not data.draw(booleans()):
            return Add(data.draw(integers(0, 100)))
        return Check(data.draw(integers(0, len(self.model) - 1)))

    def apply(mut self, t: Self.Transition) raises:
        if t.isa[Add]():
            var x = t[Add].x
            self.real.add(x)
            if x not in self.model:
                self.model.append(x)
        else:
            assert_true(
                self.real.contains(self.model[t[Check].i]), "element went missing"
            )

def main():
    try:
        run_typed_state_machine_as_test[TypedSetMachine](Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (typed.mojo:57:57):
    state = TypedSetMachine()
    state.apply(Add(x=0))
    state.apply(Add(x=1))
    state.apply(Add(x=11))
    state.apply(Check(i=2))
    state.teardown()
At typed.mojo:51:24: AssertionError: element went missing
```

Transitions are printed through `Writable`. `transition` should draw only
transitions that are valid in the current state. When the shrinker deletes
a step, the later steps are drawn again in the new state, so they stay
valid. An optional `precondition(t)` rejects a transition instead; after
three rejections in a row, the program ends at that step.
`check_invariants` and `teardown` work as for `StateMachine`. There's no
swarm testing, because the runner can't tell kinds of transition apart.

## Which to choose

- **`StateMachine`** has bundles, initialize rules, and swarm testing, and
  reads like Hypothesis's rule-based machines.
- **`TypedStateMachine`** makes operations values with types, and is
  compact when the operations are simple.
- **Commands** ([next page](model-based.md)) give each operation its own
  struct, with the model kept separate from the system under test. They
  suit larger systems, and testing several implementations against one
  model.
