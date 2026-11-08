# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# A port of Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Generated functions: `functions[A](returns)`.

Port of Hypothesis's `st.functions()` (`strategies/_internal/functions.py`),
in the shape of QuickCheck's `Fun`. A generated function is memoized:
the first call with an argument draws the result from `returns`, and later
calls with an equal argument return the same result. Results are drawn
from the test case's choice sequence when the function is called, so they
shrink like any other data. Reports print the calls made, as a table:

```
given({0->0, 3->1})
```

A function can only be called while its test case runs; calling it later
(for example on a value returned by `example()` or `find()`) raises.
"""

from std.memory import ArcPointer

from proptest.internal.data import ConjectureData, calc_label_from_name
from std.iter import downcast

from proptest.strategies.strategy import Strategy, Drawable, format_value
from proptest.strategies.core import BoxedStrategy


comptime _FUNCTION_CALL_LABEL = calc_label_from_name("function call")


struct _FunctionState[
    A: KeyElement & Copyable & Writable & Deinitable, R: Copyable & Drawable
](Movable):
    var data: Pointer[ConjectureData, MutUntrackedOrigin]
    var live: ArcPointer[Bool]
    var returns: BoxedStrategy[Self.R]
    var results: Dict[Self.A, Self.R]
    var order: List[Self.A]

    def __init__(
        out self,
        mut data: ConjectureData,
        var live: ArcPointer[Bool],
        var returns: BoxedStrategy[Self.R],
    ):
        self.data = Pointer(to=data).unsafe_origin_cast[MutUntrackedOrigin]()
        self.live = live^
        self.returns = returns^
        self.results = Dict[Self.A, Self.R]()
        self.order = List[Self.A]()


struct Function[
    A: KeyElement & Copyable & Writable & Deinitable, R: Copyable & Drawable
](Copyable, Writable):
    """A generated function from `A` to `R`; see `functions()`. Copies
    share their results."""

    var state: ArcPointer[_FunctionState[Self.A, Self.R]]

    def __init__(out self, var state: _FunctionState[Self.A, Self.R]):
        self.state = ArcPointer(state^)

    def __call__(self, x: Self.A) raises -> Self.R:
        """The result for `x`: drawn on the first call with `x`, the same
        afterwards."""
        ref st = self.state[]
        if x in st.results:
            return st.results[x].copy()
        if not st.live[]:
            raise Error(
                "functions(): a generated function was called after its"
                " test case ended"
            )
        ref data = st.data[]
        # not `data.draw`: calls aren't test arguments, so they mustn't be
        # counted as top-level draws (the explain phase varies those)
        data.start_span(_FUNCTION_CALL_LABEL)
        var v = st.returns.do_draw(data)
        data.stop_span()
        st.results[x.copy()] = v.copy()
        st.order.append(x.copy())
        return v^

    def write_to(self, mut writer: Some[Writer]):
        ref st = self.state[]
        writer.write("{")
        for i in range(len(st.order)):
            if i > 0:
                writer.write(", ")
            try:
                writer.write(
                    format_value(st.order[i]),
                    "->",
                    format_value(st.results[st.order[i]]),
                )
            except:
                pass
        writer.write("}")


struct Functions[
    A: KeyElement & Copyable & Writable & Deinitable, R: Copyable & Drawable
](Copyable, Strategy):
    """Generated functions; see `functions()`."""

    comptime Value = Function[Self.A, Self.R]
    var returns: BoxedStrategy[Self.R]

    def __init__(out self, var returns: BoxedStrategy[Self.R]):
        self.returns = returns^

    def do_draw(self, mut data: ConjectureData) raises -> Self.Value:
        var live = ArcPointer(True)
        data.live_tokens.append(live)
        return Self.Value(
            _FunctionState[Self.A, Self.R](data, live^, self.returns.copy())
        )


def functions[
    A: KeyElement & Copyable & Writable & Deinitable, S: Strategy & Copyable
](var returns: S) -> Functions[A, downcast[S.Value, Copyable & Drawable]]:
    """Functions from `A` to values of `returns` (Hypothesis's
    `functions(returns=...)`, QuickCheck's `Fun`): memoized, drawing each
    new argument's result from the test case, so they shrink, and printed
    as a table of the calls made, `{x->y, ...}`. Results must be
    `Copyable`.

    ```mojo
    def prop(f: Function[Int, Int], xs: List[Int]) raises:
        var ys = List[Int]()
        for x in xs:
            ys.append(f(x))
        ...
    given(functions[Int](integers(0, 9)), lists(integers()), prop)
    ```
    """
    comptime R = downcast[S.Value, Copyable & Drawable]
    return Functions[A, R](BoxedStrategy[R](returns^))
