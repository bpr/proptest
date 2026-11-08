# Model-based testing with commands (RapidCheck's rc::state).

from std.testing import TestSuite, assert_equal, assert_true, assert_false

from proptest import *


def fast() -> Settings:
    return Settings(database=None, max_examples=200)


# ---- a key-value store, correct or with a bug


struct KvStore(Defaultable, Movable):
    """A store that, with `buggy`, forgets a key's new value when the key
    is overwritten after the store has held three keys."""

    var keys: List[Int]
    var values: List[Int]
    var buggy: Bool
    var peak: Int

    def __init__(out self):
        self = Self(buggy=False)

    def __init__(out self, *, buggy: Bool):
        self.keys = []
        self.values = []
        self.buggy = buggy
        self.peak = 0

    def put(mut self, k: Int, v: Int):
        for i in range(len(self.keys)):
            if self.keys[i] == k:
                if not (self.buggy and self.peak >= 3):
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
        # a key the model holds
        var keys = List[Int]()
        for k in model.keys():
            keys.append(k)
        if len(keys) == 0:
            return Self(0)
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


# ---- tests


def test_correct_store_passes() raises:
    check_commands[Put, Get, Remove](KvModel(), fast())


def test_programs_are_valid_for_the_model() raises:
    def prop(program: Commands[Put, Get, Remove]) raises:
        assert_true(program.is_valid(KvModel()))
        assert_true(len(program) <= 50)
        # every Get is for a key the model holds at that point
        var model = KvModel()
        program.apply_all(model)

    given(commands[Put, Get, Remove](KvModel()), prop, fast())


def test_finds_and_shrinks_the_bug() raises:
    def prop(program: Commands[Put, Get, Remove]) raises:
        var store = KvStore(buggy=True)
        program.run(KvModel(), store)

    def run() raises:
        given(
            commands[Put, Get, Remove](KvModel()),
            prop,
            Settings(database=None, max_examples=1000),
        )

    var msg = expect_failure(run)
    # three distinct keys, an overwrite, a read of that key. Usually
    # exactly that; sometimes a Remove survives, because Get picks its key
    # by position in the model, so deleting an earlier step changes the key.
    assert_true(", 1), Get(" in msg, msg)
    assert_true(msg.count("Put(") >= 4, msg)
    assert_equal(msg.count("Get("), 1, msg)
    assert_true(msg.count("Remove(") <= 1, msg)


def test_differential_two_implementations() raises:
    # the same program against two stores, compared after every run
    def prop(program: Commands[Put, Get, Remove]) raises:
        var a = KvStore()
        var b = KvStore()
        program.run(KvModel(), a)
        program.run(KvModel(), b)
        for k in range(10):
            assert_equal(a.get(k), b.get(k))

    given(commands[Put, Get, Remove](KvModel()), prop, fast())


def test_run_commands_inside_a_property() raises:
    # the initial state is generated, and the store built to match it
    def test(mut data: ConjectureData) raises:
        var start = KvModel()
        var store = KvStore()
        for k in range(data.draw(integers(0, 3))):
            start[k] = k
            store.put(k, k)
        run_commands[Put, Get, Remove](start, store, data)

    given_data(test, fast())


def test_weights_and_max_commands() raises:
    var puts = 0
    var total = 0

    def mostly_puts(
        program: Commands[Put, Get, Remove]
    ) raises {mut puts, mut total}:
        assert_true(len(program) <= 5)
        for k in range(len(program)):
            total += 1
            if program.steps[k].isa[Put]():
                puts += 1

    given(
        commands[Put, Get, Remove](
            KvModel(), weights=[20, 1, 1], max_commands=5
        ),
        mostly_puts,
        fast(),
    )
    assert_true(total > 100 and puts * 10 > total * 7, String(puts, "/", total))


def test_bad_weights() raises:
    var msg = String()
    try:
        _ = commands[Put, Get, Remove](KvModel(), weights=[1, 1])
    except e:
        msg = String(e)
    assert_true("commands() got 2 weights for 3 command types" in msg, msg)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
