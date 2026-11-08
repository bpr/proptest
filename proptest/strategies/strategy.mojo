# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""The `Strategy` trait and the machinery shared by all strategies.

Port of `hypothesis.strategies._internal.strategies.SearchStrategy`.

A strategy does not generate values directly: it *parses* them out of the
choice sequence held by a `ConjectureData`, by calling `data.draw_integer`,
`data.draw_boolean` and friends, or by drawing from other strategies. That
is what lets the engine replay and shrink failing examples.

Strategies are ordinary structs with an associated `Value` type:

```mojo
struct Points(Strategy, Copyable):
    comptime Value = Point
    def do_draw(self, mut data: ConjectureData) raises -> Point:
        return Point(data.draw(integers(0, 10)), data.draw(integers(0, 10)))
```

Combinators (`map`, `filter`, `flatmap`, ...) are free functions rather than
methods, because Mojo traits cannot yet declare default methods generic over
closures of `Self.Value`.
"""

from std.reflection import reflect

from proptest.internal.data import (
    ConjectureData,
    calc_label_from_name,
    ONE_FROM_MANY_LABEL,
)
from proptest.internal.provider import calc_p_continue, average_size


comptime Drawable = Movable & Writable & Deinitable
"""What a strategy's values must be: movable and writable (falsifying
examples are printed). Not copyable: the engine rebuilds values from their
choices instead of keeping them, so move-only types can be generated."""


trait Strategy(Deinitable, Movable):
    """A recipe for drawing values of type `Value` from a `ConjectureData`."""

    comptime Value: Drawable
    """The type of the values this strategy produces."""

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        """Draw one value. Strategies implement this; callers should use
        `data.draw(strategy)`, which also records the span structure the
        shrinker relies on."""
        ...

    def label(self) -> UInt64:
        """The label of spans drawn by this strategy. Spans with the same
        label are treated as interchangeable by the shrinker."""
        return calc_label_from_name(reflect[Self].name())


def format_value[T: Writable](value: T) -> String:
    """How values appear in failure reports: as written by `write_to`,
    except that strings are quoted (like Python's `repr`)."""
    comptime if T == String:
        return repr(value)
    return String(value)


def draw[S: Strategy](mut data: ConjectureData, strategy: S) raises -> S.Value:
    """Draw a value from `strategy`, wrapped in a span."""
    data.start_span(strategy.label())
    var v = strategy.do_draw(data)
    data.stop_span()
    return v^


# ===----------------------------------------------------------------------=== #
# many(): collection size control
# ===----------------------------------------------------------------------=== #


struct Many(Copyable):
    """Decides when a collection should stop growing.

    Port of `hypothesis.internal.conjecture.utils.many`. Use it as:

    ```mojo
    var elements = Many(min_size, max_size)
    while elements.more(data):
        var x = data.draw(element_strategy)
        if not acceptable(x):
            elements.reject(data)
    ```

    Each element is drawn inside its own span, preceded by a boolean "keep
    going" choice, so deleting an element's span (with its boolean) deletes
    the element -- which is what makes collections shrink well.
    """

    var min_size: Int
    var max_size: Int
    var p_continue: Float64
    var count: Int
    var rejections: Int
    var force_stop: Bool
    var in_element: Bool
    var rejected: Bool
    var done: Bool

    def __init__(
        out self,
        min_size: Int,
        max_size: Int,
        avg_size: Float64 = -1.0,
    ):
        self.min_size = min_size
        self.max_size = max_size
        var avg = avg_size if avg_size >= 0 else average_size(
            min_size, max_size
        )
        self.p_continue = calc_p_continue(
            avg - Float64(min_size), Float64(max_size - min_size)
        )
        self.count = 0
        self.rejections = 0
        self.force_stop = False
        self.in_element = False
        self.rejected = False
        self.done = False

    def more(mut self, mut data: ConjectureData) raises -> Bool:
        """Whether to draw another element."""
        if self.in_element:
            self.in_element = False
            data.stop_span(discard=self.rejected)
        if self.done:
            return False
        if self.force_stop and self.count < self.min_size:
            data.mark_invalid(
                String(
                    "stopped with ",
                    self.count,
                    " elements, below min_size=",
                    self.min_size,
                )
            )
        data.start_span(ONE_FROM_MANY_LABEL)
        var should_continue: Bool
        if self.min_size == self.max_size:
            should_continue = self.count < self.min_size
        else:
            var forced: Optional[Bool] = None
            if self.force_stop:
                forced = False
            elif self.count < self.min_size:
                forced = True
            elif self.count >= self.max_size:
                forced = False
            should_continue = data.draw_boolean(self.p_continue, forced=forced)
        if should_continue:
            self.count += 1
            self.in_element = True
            self.rejected = False
        else:
            self.done = True
            data.stop_span()
        return should_continue

    def reject(mut self, mut data: ConjectureData) raises:
        """Reject the element just drawn: it does not count towards the size,
        and its span is marked discarded."""
        self.count -= 1
        self.rejections += 1
        self.rejected = True
        if self.rejections > max(3, 2 * self.count):
            if self.count < self.min_size:
                data.mark_invalid("too many rejected elements")
            else:
                self.force_stop = True
