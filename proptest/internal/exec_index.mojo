# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Execution indexing (Zest's `ExecutionIndexingGuidance`, from JQF): a key
for each choice that names where in the test's structure it was drawn,
so that a mutated test case can be replayed by key instead of by
position.

A span's key is its parent's key mixed with its label and how many
siblings with that label came before it; a choice's key is its
innermost span's key mixed with how many choices that span drew directly
before it. Zest computes the same thing from the call stack, with
bytecode instrumentation; the spans give it to proptest for free.

Replaying by position, a mutation that changes the structure (a list's
length, a `one_of` branch) shifts every later choice onto a different
draw. Replaying by key, the later draws find the values they had: the
third element of the second list is still the third element of the
second list. A key the parent never drew is drawn afresh.

`ConjectureData` tracks keys while an `ExecIndex` is set on it; the fuzz
loop computes a finished test case's keys with `choice_keys`
(`fuzz.mojo`).
"""

from proptest.internal.choice import (
    ChoiceValue,
    Constraints,
    INTEGER,
    choice_permitted,
)


comptime _TOP_KEY: UInt64 = 0x45584543494E4458
"""The top span's key."""
comptime _CHOICE_SALT: UInt64 = 0x43484F494345
"""Keeps a choice's key apart from a child span's."""


def _mix(a: UInt64, b: UInt64) -> UInt64:
    var z = (a ^ (b + 0x9E3779B97F4A7C15 + (a << 6) + (a >> 2))) * (
        0xBF58476D1CE4E5B9
    )
    return z ^ (z >> 31)


struct KeyTracker(Copyable):
    """Span and choice keys as a test case's spans and choices arrive in
    order."""

    var span_keys: List[UInt64]
    """Each span's key, by span index."""
    var direct: List[Int]
    """How many choices each span has drawn directly."""
    var siblings: Dict[UInt64, Int]
    """How many spans have started with each (parent index, label)."""

    def __init__(out self):
        self.span_keys = [_TOP_KEY]
        self.direct = [0]
        self.siblings = Dict[UInt64, Int]()

    def start_span(mut self, parent: Int, label: UInt64):
        """Span number `len(self.span_keys)` starts, under `parent`."""
        var group = _mix(UInt64(parent), label)
        var n = self.siblings.get(group, 0)
        self.siblings[group] = n + 1
        self.span_keys.append(
            _mix(_mix(self.span_keys[parent], label), UInt64(n))
        )
        self.direct.append(0)

    def choice(mut self, span: Int) -> UInt64:
        """The key of the next choice drawn directly in `span`."""
        var n = self.direct[span]
        self.direct[span] = n + 1
        return _mix(self.span_keys[span], UInt64(n) ^ _CHOICE_SALT)


struct ExecIndex(Copyable):
    """Values to replay by key (see the module docstring), with the keys of
    the test case being drawn."""

    var values: Dict[UInt64, ChoiceValue]
    var keys: KeyTracker

    def __init__(out self, var values: Dict[UInt64, ChoiceValue]):
        self.values = values^
        self.keys = KeyTracker()

    def start_span(mut self, parent: Int, label: UInt64):
        self.keys.start_span(parent, label)

    def lookup(
        mut self, span: Int, constraints: Constraints
    ) -> Optional[ChoiceValue]:
        """The value to replay for the next choice drawn directly in
        `span`, if there is one that fits `constraints` (an integer out of
        range is clamped into it, as in replay by position)."""
        var key = self.keys.choice(span)
        var found = self.values.get(key)
        if not found:
            return None
        var v = found.take()
        if v.kind != constraints.kind:
            return None
        if choice_permitted(v, constraints):
            return v^
        if v.kind == INTEGER:
            var x = v.i
            if constraints.has_min and x < constraints.min_value:
                x = constraints.min_value
            if constraints.has_max and x > constraints.max_value:
                x = constraints.max_value
            var clamped = ChoiceValue(integer=x)
            if choice_permitted(clamped, constraints):
                return clamped^
        return None
