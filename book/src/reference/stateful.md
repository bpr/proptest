# Stateful and model-based testing

## `StateMachine`

```mojo-sig
trait StateMachine(Deinitable, Movable):
    def __init__(out self)
    def rule_count(self) -> Int
    def rule_name(self, rule: Int) -> String                       # default "rule<n>"
    def precondition(self, rule: Int) -> Bool                      # default True
    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises
    def check_invariants(self) raises                              # default: nothing
    def initialize_count(self) -> Int                              # default 0
    def initialize_name(self, rule: Int) -> String                 # default "initialize<n>"
    def run_initialize(mut self, rule: Int, mut data: ConjectureData) raises
    def teardown(mut self) raises                                  # default: nothing
```

A rule-based state machine (Hypothesis's `RuleBasedStateMachine`). Rules
are numbered from 0. Each program:

1. creates the machine with `__init__` and checks the invariants;
2. runs each initialize rule once, in a random order;
3. runs up to `stateful_step_count` steps, each choosing a rule whose
   precondition holds (from a random subset of the rules: *swarm
   testing*), running it, and checking the invariants;
4. calls `teardown`, even if a step failed.

Rule arguments are the labeled draws a rule makes; a failure prints each
step as `state.<rule_name>(<label>=<value>, ...)`.

### `run_state_machine_as_test`

```mojo-sig
run_state_machine_as_test[M: StateMachine](settings=Settings())
```

Runs programs against fresh machines and raises with the shrunk failing
program. It suppresses the `data_too_large` and `large_base_example`
health checks and the explain phase.

### `run_state_machine`

```mojo-sig
run_state_machine[M: StateMachine](mut data: ConjectureData, max_steps: Int, deadline_ns: Int = -1)
```

Runs one program inside a test, for use with `given_data` or `run_test`.

### `Bundle[T]`

```mojo-sig
Bundle[T](name: String)
bundle.add(value)
bundle.draw(data) -> T          # shrinks towards the most recently added
bundle.consume(data) -> T       # also removes the value
len(bundle)
```

Values produced by earlier steps for later steps (Hypothesis's `Bundle`).
`draw` and `consume` need a non-empty bundle; check it in the rule's
precondition. `T` must be `Copyable`.

## `TypedStateMachine`

```mojo-sig
trait TypedStateMachine(Deinitable, Movable):
    comptime Transition: Drawable
    def __init__(out self)
    def transition(self, mut data: ConjectureData) raises -> Self.Transition
    def precondition(self, t: Self.Transition) -> Bool             # default True
    def apply(mut self, t: Self.Transition) raises
    def check_invariants(self) raises                              # default: nothing
    def teardown(mut self) raises                                  # default: nothing
```

A state machine whose steps are values (Rust's proptest-state-machine).
Each step draws a transition from the current state and applies it. A
transition that fails its precondition is redrawn; after three rejections
in a row, the program ends at that step. Failures print as
`state.apply(<transition>)`. No swarm testing.

### `run_typed_state_machine_as_test`, `run_typed_state_machine`

```mojo-sig
run_typed_state_machine_as_test[M: TypedStateMachine](settings=Settings())
run_typed_state_machine[M: TypedStateMachine](mut data: ConjectureData, max_steps: Int, deadline_ns: Int = -1)
```

As for `StateMachine`.

## `Command`

```mojo-sig
trait Command(Copyable, Deinitable, Writable):
    comptime Model: Copyable & Deinitable
    comptime Sut: Deinitable

    @staticmethod
    def generate(model: Self.Model, mut data: ConjectureData) raises -> Self
    def precondition(self, model: Self.Model) raises -> Bool       # default True
    def next_state(self, mut model: Self.Model) raises             # default: nothing
    def run(self, model: Self.Model, mut sut: Self.Sut) raises     # default: nothing
```

One operation in a model-based test (RapidCheck's `rc::state::Command`).
`run` receives the model's state *before* the command. All the commands of
a program must have the same `Model` and `Sut`; this is checked at compile
time.

## `Commands[*Cs]`

A program: a sequence of commands of the types `Cs`, generated from a model
state.

| Member | Description |
|---|---|
| `run(model, mut sut)` | Run the program on `sut`, which must be in the state `model` describes. |
| `apply_all(mut model)` | Apply the program to a model only (RapidCheck's `applyAll`). |
| `is_valid(model) -> Bool` | Whether every precondition holds along the way (`isValidSequence`). |
| `len(program)` | The number of commands. |
| `steps: List[Variant[*Cs]]` | The commands. |

Prints as `[Put(0, 0), Get(0)]`.

### `commands`

```mojo-sig
commands[*Cs: Command](model, *, max_commands: Int = 50) -> CommandSequences[*Cs]
commands[*Cs: Command](model, *, weights: List[Int], max_commands: Int = 50) raises -> CommandSequences[*Cs]
```

A strategy for programs of up to `max_commands` commands, valid from
`model`. Shrinks towards shorter programs, and towards the first command
type. `weights` biases the choice of command type.

### `check_commands`

```mojo-sig
check_commands[*Cs: Command](model, settings=Settings(), *, max_commands: Int = 50)
```

Runs programs on a fresh, default-constructed `Sut` (which must be
`Defaultable`) for each test case.

### `run_commands`

```mojo-sig
run_commands[*Cs: Command](model, mut sut, mut data, *, max_commands: Int = 50)
```

Draws a program and runs it on `sut`, inside a `given_data` test
(RapidCheck's `rc::state::check`).
