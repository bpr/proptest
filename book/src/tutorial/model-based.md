# Model-based testing

Model-based testing (from RapidCheck's `rc::state` and Erlang QuickCheck)
separates three things that a state machine mixes together:

- the **model**: a simple value describing the state the system should be
  in, such as a `Dict` standing in for a database;
- the **system under test** (the *SUT*);
- the **commands**: one struct per operation, each knowing how to generate
  itself from the model, how it changes the model, and how to run it on the
  system and check the result.

Because commands are generated from the model alone, proptest can generate
a whole program without touching the system, then run it. The program is a
value: you can print it, run it on two implementations, or run it inside an
ordinary property that sets up the system however it likes.

## Commands

A command implements the `Command` trait. It names the `Model` and `Sut`
types, and provides:

- `generate(model, data)`: a static method that draws a command valid in
  the model's current state;
- `precondition(model)` (optional): whether the command may run in this
  state;
- `next_state(mut model)` (optional): apply the command to the model;
- `run(model, mut sut)` (optional): apply the command to the system and
  check the result. `model` is the state *before* the command;
- `write_to`, to print the command in reports.

Here is a key-value store with a bug: once it has held three keys, it
ignores overwrites.

```mojo
from std.testing import assert_true, assert_equal, assert_false
from proptest import (
    Command, Commands, commands, given, integers, sampled_from,
    ConjectureData, Settings,
)

struct KvStore(Defaultable, Movable):
    var keys: List[Int]
    var values: List[Int]
    var peak: Int

    def __init__(out self):
        self.keys = []
        self.values = []
        self.peak = 0

    def put(mut self, k: Int, v: Int):
        for i in range(len(self.keys)):
            if self.keys[i] == k:
                if self.peak < 3:  # BUG: overwrites ignored after 3 keys
                    self.values[i] = v
                return
        self.keys.append(k)
        self.values.append(v)
        self.peak = max(self.peak, len(self.keys))

    def get(self, k: Int) -> Optional[Int]:
        for i in range(len(self.keys)):
            if self.keys[i] == k:
                return self.values[i]
        return None

    def remove(mut self, k: Int):
        for i in range(len(self.keys)):
            if self.keys[i] == k:
                _ = self.keys.pop(i)
                _ = self.values.pop(i)
                return

comptime KvModel = Dict[Int, Int]

@fieldwise_init
struct Put(Command):
    comptime Model = KvModel
    comptime Sut = KvStore
    var key: Int
    var value: Int

    @staticmethod
    def generate(model: KvModel, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 9)), data.draw(integers(0, 9)))

    def next_state(self, mut model: KvModel) raises:
        model[self.key] = self.value

    def run(self, model: KvModel, mut sut: KvStore) raises:
        sut.put(self.key, self.value)

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Put(", self.key, ", ", self.value, ")")

@fieldwise_init
struct Get(Command):
    comptime Model = KvModel
    comptime Sut = KvStore
    var key: Int

    @staticmethod
    def generate(model: KvModel, mut data: ConjectureData) raises -> Self:
        var keys = List[Int]()
        for k in model.keys():
            keys.append(k)
        if len(keys) == 0:
            return Self(0)  # rejected by the precondition
        return Self(data.draw(sampled_from(keys^)))

    def precondition(self, model: KvModel) raises -> Bool:
        return self.key in model

    def run(self, model: KvModel, mut sut: KvStore) raises:
        var got = sut.get(self.key)
        assert_true(Bool(got), "key missing")
        assert_equal(got.value(), model[self.key])

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Get(", self.key, ")")

@fieldwise_init
struct Remove(Command):
    comptime Model = KvModel
    comptime Sut = KvStore
    var key: Int

    @staticmethod
    def generate(model: KvModel, mut data: ConjectureData) raises -> Self:
        return Self(data.draw(integers(0, 9)))

    def next_state(self, mut model: KvModel) raises:
        _ = model.pop(self.key, 0)

    def run(self, model: KvModel, mut sut: KvStore) raises:
        sut.remove(self.key)
        assert_false(Bool(sut.get(self.key)))

    def write_to(self, mut writer: Some[Writer]):
        writer.write("Remove(", self.key, ")")

def main():
    def prop(program: Commands[Put, Get, Remove]) raises:
        var store = KvStore()
        program.run(KvModel(), store)

    try:
        given(commands[Put, Get, Remove](KvModel()), prop, Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (kv.mojo:114:14):
    given([Put(0, 1), Put(1, 0), Put(2, 0), Put(0, 0), Get(0)])
At kv.mojo:83:21: AssertionError: `left == right` comparison failed:
   left: 1
  right: 0
```

The shrunk program is a minimal one: three distinct keys, an overwrite,
and a read of the overwritten key. (Which key is overwritten, and with
which value, can vary between runs; the shape doesn't.)

## Programs

`commands[Put, Get, Remove](model)` is a strategy for programs: values of
type `Commands[Put, Get, Remove]`, valid when run from the state `model`.
It takes optional `weights=[...]`, to choose some command types more often
than others, and `max_commands` (default 50).

A program runs with `program.run(model, sut)`, which runs each command on
the system and updates a copy of the model as it goes. Because this happens
inside an ordinary property, the property can:

- **generate the initial state** with other strategies, and build the
  system and model to match;
- **use a fixture**, such as a temporary directory or a connection;
- **test two implementations against each other**: run the same program
  on both, and compare them.

```mojo
~from std.testing import assert_true, assert_equal, assert_false
~from proptest import (
~    Command, Commands, commands, given, integers, sampled_from,
~    ConjectureData, Settings,
~)
~
~struct KvStore(Defaultable, Movable):
~    var keys: List[Int]
~    var values: List[Int]
~    var peak: Int
~
~    def __init__(out self):
~        self.keys = []
~        self.values = []
~        self.peak = 0
~
~    def put(mut self, k: Int, v: Int):
~        for i in range(len(self.keys)):
~            if self.keys[i] == k:
~                if self.peak < 3:  # BUG: overwrites ignored after 3 keys
~                    self.values[i] = v
~                return
~        self.keys.append(k)
~        self.values.append(v)
~        self.peak = max(self.peak, len(self.keys))
~
~    def get(self, k: Int) -> Optional[Int]:
~        for i in range(len(self.keys)):
~            if self.keys[i] == k:
~                return self.values[i]
~        return None
~
~    def remove(mut self, k: Int):
~        for i in range(len(self.keys)):
~            if self.keys[i] == k:
~                _ = self.keys.pop(i)
~                _ = self.values.pop(i)
~                return
~
~comptime KvModel = Dict[Int, Int]
~
~@fieldwise_init
~struct Put(Command):
~    comptime Model = KvModel
~    comptime Sut = KvStore
~    var key: Int
~    var value: Int
~
~    @staticmethod
~    def generate(model: KvModel, mut data: ConjectureData) raises -> Self:
~        return Self(data.draw(integers(0, 9)), data.draw(integers(0, 9)))
~
~    def next_state(self, mut model: KvModel) raises:
~        model[self.key] = self.value
~
~    def run(self, model: KvModel, mut sut: KvStore) raises:
~        sut.put(self.key, self.value)
~
~    def write_to(self, mut writer: Some[Writer]):
~        writer.write("Put(", self.key, ", ", self.value, ")")
~
~@fieldwise_init
~struct Get(Command):
~    comptime Model = KvModel
~    comptime Sut = KvStore
~    var key: Int
~
~    @staticmethod
~    def generate(model: KvModel, mut data: ConjectureData) raises -> Self:
~        var keys = List[Int]()
~        for k in model.keys():
~            keys.append(k)
~        if len(keys) == 0:
~            return Self(0)  # rejected by the precondition
~        return Self(data.draw(sampled_from(keys^)))
~
~    def precondition(self, model: KvModel) raises -> Bool:
~        return self.key in model
~
~    def run(self, model: KvModel, mut sut: KvStore) raises:
~        var got = sut.get(self.key)
~        assert_true(Bool(got), "key missing")
~        assert_equal(got.value(), model[self.key])
~
~    def write_to(self, mut writer: Some[Writer]):
~        writer.write("Get(", self.key, ")")
~
~@fieldwise_init
~struct Remove(Command):
~    comptime Model = KvModel
~    comptime Sut = KvStore
~    var key: Int
~
~    @staticmethod
~    def generate(model: KvModel, mut data: ConjectureData) raises -> Self:
~        return Self(data.draw(integers(0, 9)))
~
~    def next_state(self, mut model: KvModel) raises:
~        _ = model.pop(self.key, 0)
~
~    def run(self, model: KvModel, mut sut: KvStore) raises:
~        sut.remove(self.key)
~        assert_false(Bool(sut.get(self.key)))
~
~    def write_to(self, mut writer: Some[Writer]):
~        writer.write("Remove(", self.key, ")")
~comptime FastKvStore = KvStore
~
def prop(program: Commands[Put, Get, Remove]) raises:
    var a = KvStore()
    var b = FastKvStore()
    program.run(KvModel(), a)
    program.run(KvModel(), b)
    for k in range(10):
        assert_true(a.get(k) == b.get(k))
~
~def main() raises:
~    try:  # this page's KvStore has the bug, so Get's check fails
~        given(commands[Put, Get, Remove](KvModel()), prop, Settings(database=None))
~    except e:
~        print(e)
```

`program.apply_all(model)` applies a program to a model only, and
`program.is_valid(model)` checks every precondition along the way
(RapidCheck's `applyAll` and `isValidSequence`).

## Shortcuts

- `check_commands[Put, Get, Remove](model, settings)` runs programs on a
  fresh, default-constructed system for each test case: the whole test
  above, for a `Sut` that is `Defaultable`.
- `run_commands[Put, Get, Remove](model, sut, data)` draws a program and
  runs it, inside a `given_data` test.

## How programs shrink

A program is generated like a list: each command is drawn after a "keep
going" choice, so the shrinker can delete commands. When it deletes or
simplifies one, the later commands are generated again from the same
choices, in the new model state, so a shrunk program is always valid.
RapidCheck re-checks preconditions while shrinking for the same reason.

There's one limitation. A command that picks a value *out of the model*,
like `Get` choosing among the keys the model holds, is coupled to the
earlier steps: deleting an earlier `Put` changes which key the same choice
picks. Shrinking can then stop a step or two short of minimal. When
rejections would be rare, drawing the value directly (`integers(0, 9)`)
and rejecting invalid ones with `precondition` shrinks better.

## Compared with state machines

Model-based testing and `TypedStateMachine` can express the same tests.
Commands keep each operation's generation, model update, and checks
together in one struct, rather than in an `isa` chain, and the whole
program exists before it runs. State machines draw each step from the
current state of the system itself, which is simpler when there's no
separate model.

## A complete example

[`examples/lru_cache.mojo`](https://github.com/bpr/proptest/blob/master/examples/lru_cache.mojo)
tests an LRU cache (LeetCode 146) against a model that keeps its entries
in a plain list, most recently used first. Each test case draws the
cache's capacity, then a program of `put` and `get` commands, and after
the program compares the cache's recency order with the model's.

[`examples/lru_cache_pointers.mojo`](https://github.com/bpr/proptest/blob/master/examples/lru_cache_pointers.mojo)
is the same cache built from heap-allocated nodes and raw pointers. Its
commands also check the list's links after every step, and building it
with `--sanitize address` checks for leaks and use after free.

[`examples/dancing_links.mojo`](https://github.com/bpr/proptest/blob/master/examples/dancing_links.mojo)
is Knuth's Dancing Links, an exact cover solver whose nodes are linked by
raw pointers in four directions. Its `Cover` and `Uncover` commands check
every column against a model after each step, and when every cover has
been undone they check that every link is back where it started.

[`examples/xor_list.mojo`](https://github.com/bpr/proptest/blob/master/examples/xor_list.mojo)
is an XOR linked list: each node stores the XOR of its neighbors'
addresses, so the same code walks it either way, and reversing it is
swapping its head and tail. Its commands walk the list in both directions
after every step and compare it with a `List`.

[`examples/splay_tree.mojo`](https://github.com/bpr/proptest/blob/master/examples/splay_tree.mojo)
is a splay tree whose nodes link to their parents as well as their
children. Its commands check every link, the key order, and the subtree
sizes after each step, and compare the tree with a sorted list. A splay
that moves a node to the root one rotation at a time still gives the right
answers, only slowly, so the tree also checks the access lemma of
Sleator and Tarjan's analysis after every splay, and a second property
checks that accessing every key in order takes at most 4.5 n rotations.

[`examples/red_black_tree.mojo`](https://github.com/bpr/proptest/blob/master/examples/red_black_tree.mojo)
is a red-black tree that, like the Linux kernel's, stores each node's
color in the low bit of its parent pointer. After each command it checks
the red-black rules, that every parent link points back and holds no
stray bits, and that the height is at most 2 log2(n + 1).

[`examples/intrusive_list.mojo`](https://github.com/bpr/proptest/blob/master/examples/intrusive_list.mojo)
is an intrusive list in the Linux kernel's style: the links are fields of
the tasks themselves, so a task can be on two lists at once, and
`container_of` recovers a task from its link by subtracting the field's
offset, `reflect[Task].field_offset[name="ready_link"]()`. A scheduler's
commands (spawn, wake, block, run, kill, ...) are checked against two
plain lists of ids, walking both rings both ways after every step.
