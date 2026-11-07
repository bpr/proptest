# The "Die Hard" water jug puzzle, solved by stateful testing: claim that
# the big jug never holds exactly 4 gallons, and let proptest find (and
# shrink) the sequence of pours that refutes it.
#
#   pixi run mojo run -I . examples/die_hard.mojo

from proptest import *
from proptest.stateful import StateMachine, run_state_machine_as_test


struct DieHard(StateMachine):
    var small: Int  # the 3 gallon jug
    var big: Int  # the 5 gallon jug

    def __init__(out self):
        self.small = 0
        self.big = 0

    def rule_count(self) -> Int:
        return 6

    def rule_name(self, rule: Int) -> String:
        var names: List[String] = [
            "fill_small",
            "fill_big",
            "empty_small",
            "empty_big",
            "pour_small_into_big",
            "pour_big_into_small",
        ]
        return names[rule]

    def run_rule(mut self, rule: Int, mut data: ConjectureData) raises:
        if rule == 0:
            self.small = 3
        elif rule == 1:
            self.big = 5
        elif rule == 2:
            self.small = 0
        elif rule == 3:
            self.big = 0
        elif rule == 4:
            var old_big = self.big
            self.big = min(5, self.big + self.small)
            self.small = self.small - (self.big - old_big)
        else:
            var old_small = self.small
            self.small = min(3, self.small + self.big)
            self.big = self.big - (self.small - old_small)

    def check_invariants(self) raises:
        if self.big == 4:
            fail("the big jug holds exactly 4 gallons")


def main():
    try:
        run_state_machine_as_test[DieHard](
            Settings(max_examples=10000, database=None)
        )
        print("No solution found")
    except e:
        print(e)
