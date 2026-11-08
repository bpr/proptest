# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Model-based testing with commands, after RapidCheck's `rc::state` (and
Erlang QuickCheck's `eqc_statem`).

Each operation on the system under test is a struct implementing
`Command`. It names the model and system types, generates itself from the
model, may reject a model state (`precondition`), updates the model
(`next_state`) and acts on the system, checking the result against the
model's state before the step (`run`):

```mojo
@fieldwise_init
struct Put(Command):
    comptime Model = Dict[String, Int]
    comptime Sut = KvStore
    var key: String
    var value: Int

    @staticmethod
    def generate(model: Self.Model, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(text()), data.draw(integers()))

    def next_state(self, mut model: Self.Model) raises:
        model[self.key] = self.value

    def run(self, model: Self.Model, mut sut: Self.Sut) raises:
        sut.put(self.key, self.value)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Put(", repr(self.key), ", ", self.value, ")")
```

`commands[Put, Get, Remove](model)` is a strategy for whole programs,
`Commands[Put, Get, Remove]`, generated against the model alone, so the
system is never needed to generate or to decide validity. A program runs
inside an ordinary property, which can therefore generate the initial
state, use a fixture, or run one program against two implementations:

```mojo
def prop(program: Commands[Put, Get, Remove]) raises:
    var store = KvStore()
    program.run(Dict[String, Int](), store)

given(commands[Put, Get, Remove](Dict[String, Int]()), prop)
```

`check_commands[Put, Get, Remove](model)` does exactly that for a system
type with a default constructor. A failure prints the shrunk program:

```
given([Put("", 0), Remove(""), Get("")])
```

Shrinking: the program is a list of commands, each drawn after a "keep
going" choice like the elements of `lists()`. When the shrinker deletes or
simplifies a command, the later ones are generated again from the same
choices in the new model state, so they stay valid. RapidCheck re-checks
preconditions while shrinking for the same reason.
"""

from std.reflection import call_location, SourceLocation
from std.memory import ArcPointer
from std.utils import Variant

from proptest.internal.data import ConjectureData, combine_labels
from proptest.strategies.strategy import Many, Strategy
from proptest.strategies.core import _normalize_weights
from proptest.settings import Settings
from proptest.core import given

comptime COMMANDS_LABEL: UInt64 = 0x636F6D6D616E6473


trait Command(Copyable, Deinitable, Writable):
    """One operation in a model-based test; see the module docs.

    All the commands of a program must have the same `Model` and `Sut`.
    """

    comptime Model: Copyable & Deinitable
    """The model of the system's state."""
    comptime Sut: Deinitable
    """The system under test."""

    @staticmethod
    def generate(model: Self.Model, mut data: ConjectureData) raises -> Self:
        """A command for the current model state. Draw only what is valid
        in that state where possible (e.g. a key that `model` holds), and
        leave the rest to `precondition`."""
        ...

    def precondition(self, model: Self.Model) raises -> Bool:
        """Whether this command may run in this model state. Rejected
        commands are dropped from the program and another is drawn."""
        return True

    def next_state(self, mut model: Self.Model) raises:
        """Apply this command to the model."""
        return

    def run(self, model: Self.Model, mut sut: Self.Sut) raises:
        """Apply this command to the system under test, and check the
        result. `model` is the state before the command."""
        return


struct Commands[*Cs: Command](Copyable, Sized, Writable):
    """A program: a sequence of commands of types `Cs`, valid for the model
    state it was generated from. Drawn from `commands()`."""

    comptime Model = Self.Cs[0].Model
    comptime Sut = Self.Cs[0].Sut
    comptime Step = Variant[*Self.Cs]

    var steps: List[Self.Step]

    def __init__(out self):
        comptime for i in range(len(Self.Cs)):
            comptime assert (
                Self.Cs[i].Model == Self.Model
            ), "Commands: every command must have the same Model"
            comptime assert (
                Self.Cs[i].Sut == Self.Sut
            ), "Commands: every command must have the same Sut"
        self.steps = []

    def __len__(self) -> Int:
        return len(self.steps)

    def run(self, var model: Self.Model, mut sut: Self.Sut) raises:
        """Run the program on `sut`, which must be in the state `model`
        describes. Each command's `run` sees the model's state before it."""
        for k in range(len(self.steps)):
            ref step = self.steps[k]
            comptime for i in range(len(Self.Cs)):
                if step.isa[Self.Cs[i]]():
                    ref c = step[Self.Cs[i]]
                    c.run(
                        rebind[Self.Cs[i].Model](model),
                        rebind[Self.Cs[i].Sut](sut),
                    )
                    c.next_state(rebind[Self.Cs[i].Model](model))

    def apply_all(self, mut model: Self.Model) raises:
        """Apply the program to `model` only (RapidCheck's `applyAll`)."""
        for k in range(len(self.steps)):
            ref step = self.steps[k]
            comptime for i in range(len(Self.Cs)):
                if step.isa[Self.Cs[i]]():
                    step[Self.Cs[i]].next_state(rebind[Self.Cs[i].Model](model))

    def is_valid(self, var model: Self.Model) raises -> Bool:
        """Whether every command's precondition holds when the program runs
        from `model` (RapidCheck's `isValidSequence`)."""
        for k in range(len(self.steps)):
            ref step = self.steps[k]
            comptime for i in range(len(Self.Cs)):
                if step.isa[Self.Cs[i]]():
                    ref c = step[Self.Cs[i]]
                    if not c.precondition(rebind[Self.Cs[i].Model](model)):
                        return False
                    c.next_state(rebind[Self.Cs[i].Model](model))
        return True

    def write_to(self, mut writer: Some[Writer]):
        writer.write("[")
        for k in range(len(self.steps)):
            if k > 0:
                writer.write(", ")
            writer.write(self.steps[k])
        writer.write("]")


struct CommandSequences[*Cs: Command](Copyable, Strategy):
    """Programs of commands `Cs` valid from a model state; see
    `commands()`."""

    comptime Value = Commands[*Self.Cs]

    var model: Self.Cs[0].Model
    var max_commands: Int
    var weights: Optional[ArcPointer[List[Float64]]]

    def __init__(
        out self,
        model: Self.Cs[0].Model,
        max_commands: Int,
        var weights: Optional[ArcPointer[List[Float64]]] = None,
    ):
        self.model = model.copy()
        self.max_commands = max_commands
        self.weights = weights^

    def label(self) -> UInt64:
        return combine_labels(COMMANDS_LABEL, UInt64(len(Self.Cs)))

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        comptime n = len(Self.Cs)
        var program = Commands[*Self.Cs]()
        var model = self.model.copy()
        # long programs find more bugs; the shrinker removes what isn't needed
        var steps = Many(
            0, self.max_commands, avg_size=Float64(self.max_commands) / 2
        )
        while steps.more(data):
            var k = Int(
                data.draw_integer(
                    Int128(0), Int128(n - 1), weights=self.weights
                )
            )
            comptime for i in range(n):
                if i == k:
                    ref m = rebind[Self.Cs[i].Model](model)
                    var c = Self.Cs[i].generate(m, data)
                    if c.precondition(m):
                        c.next_state(m)
                        program.steps.append(Commands[*Self.Cs].Step(c^))
                    else:
                        steps.reject(data)
        return program^


def commands[
    *Cs: Command
](model: Cs[0].Model, *, max_commands: Int = 50) -> CommandSequences[*Cs]:
    """Programs of up to `max_commands` commands of types `Cs`, generated
    from the model state `model`; shrinks towards shorter programs and
    towards the first command type."""
    return CommandSequences[*Cs](model, max_commands)


def commands[
    *Cs: Command
](
    model: Cs[0].Model, *, weights: List[Int], max_commands: Int = 50
) raises -> CommandSequences[*Cs]:
    """Like `commands(model)`, choosing each command type in proportion to
    its (positive) weight."""
    var ws = _normalize_weights(weights, len(Cs), "commands", "command types")
    return CommandSequences[*Cs](model, max_commands, ws^)


def run_commands[
    *Cs: Command
](
    model: Cs[0].Model,
    mut sut: Cs[0].Sut,
    mut data: ConjectureData,
    *,
    max_commands: Int = 50,
) raises:
    """Draw a program from `model` and run it on `sut`, inside a property
    (RapidCheck's `rc::state::check`)."""
    var program = data.draw(commands[*Cs](model, max_commands=max_commands))
    program.run(model.copy(), sut)


@always_inline
def check_commands[
    *Cs: Command
](
    model: Cs[0].Model,
    settings: Settings = Settings(),
    *,
    max_commands: Int = 50,
    location: Optional[SourceLocation] = None,
) raises:
    """Run programs of commands `Cs` on a fresh, default-constructed system
    for each test case, starting from `model`; raises with the shrunk
    program if one fails."""
    comptime S = Cs[0].Sut
    comptime assert conforms_to(
        S, Defaultable
    ), "check_commands needs a Sut with a default constructor; use given()"
    var loc = location.value() if location else call_location()
    var start = model.copy()

    def prop(program: Commands[*Cs]) raises {start}:
        var sut = S()
        program.run(start.copy(), sut)

    given(
        commands[*Cs](model, max_commands=max_commands),
        prop,
        settings,
        location=loc,
    )
