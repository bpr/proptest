# Writing strategies: the low-level API

Most strategies are built from other strategies, with combinators,
`composite`, or a struct whose `do_draw` calls `data.draw`. This page
covers the layer beneath: the `Strategy` trait, the primitive choices a
`ConjectureData` offers, and the tools for making collections that shrink
well.

## `Strategy`

```mojo-sig
trait Strategy(Deinitable, Movable):
    comptime Value: Drawable
    def do_draw(self, mut data: ConjectureData) raises -> Self.Value
    def label(self) -> UInt64      # default: derived from the type's name
```

`do_draw` produces one value. Callers use `data.draw(strategy)` (or the
free function `draw(data, strategy)`), which wraps the call in a *span*
labeled `strategy.label()`. The shrinker treats spans with the same label
as interchangeable, so it can, for example, swap two list elements. Give
a strategy a label of its own (with `calc_label_from_name("...")`, from
`proptest.internal.data`) when its default, the type's name, would make
unrelated draws look alike.

### `Drawable`

```mojo-sig
comptime Drawable = Movable & Writable & Deinitable
```

What a strategy's values must be: movable, printable for reports, and
destructible. Not necessarily `Copyable`.

## Primitive choices

All generation comes down to these `ConjectureData` methods. Each records
one choice, which the shrinker can then simplify.

| Method | Choice |
|---|---|
| `draw_integer(min_value=, max_value=, *, shrink_towards=0, forced=, weights=) -> Int128` | An integer, in the range if given. Shrinks towards `shrink_towards`. `weights` are the probabilities of each value in the range. |
| `draw_float(min_value=-inf, max_value=inf, *, allow_nan=True, smallest_nonzero_magnitude=, forced=) -> Float64` | A float. |
| `draw_boolean(p=0.5, *, forced=) -> Bool` | `True` with probability `p`. Shrinks towards `False`. |
| `draw_bytes(min_size=0, max_size=) -> List[UInt8]` | A byte string. |
| `draw_string(intervals, min_size=0, max_size=) -> List[UInt32]` | A string, as codepoints from an `IntervalSet`. |

`forced=` makes the choice take a given value while still recording it,
which keeps the choice sequence's shape the same whether or not a value is
forced.

Some rules for strategies that make primitive choices:

- **Make the simplest choice give the simplest value.** The shrinker
  moves each choice towards its simplest form (0, `False`, the empty
  string), so arrange that this produces the value you'd want in a minimal
  example.
- **Keep generation deterministic.** The same choices must produce the
  same value, and make the same further choices. Don't consult the clock,
  a separate random generator, or captured mutable state.
- **Prefer drawing over filtering.** Draw values in a form that's always
  valid instead of rejecting invalid ones.

## Spans

```mojo-sig
data.start_span(label: UInt64)
data.stop_span(discard: Bool = False)
```

Group the choices between them into a span. `data.draw` does this for you.
Use them directly for structure inside a strategy, such as one span per
element. `discard=True` marks the span's choices as not contributing to the
value, as for a rejected draw.

## Collections: `Many`

`Many` decides when a collection should stop growing, in a way that
shrinks well (Hypothesis's `many`). Each element is preceded by a boolean
"keep going" choice, inside a span with the element, so deleting the span
deletes the element:

```mojo
from proptest import Strategy, ConjectureData, Many, integers, example

struct EvenLists(Copyable, Strategy):
    comptime Value = List[Int]

    def __init__(out self):
        pass

    def do_draw(self, mut data: ConjectureData) raises -> List[Int]:
        var out = List[Int]()
        var elements = Many(0, 10)                # min_size, max_size
        while elements.more(data):
            var x = data.draw(integers(0, 100))
            if x % 2 != 0:
                elements.reject(data)             # doesn't count; may stop early
                continue
            out.append(x)
        return out^

def main() raises:
    print(example(EvenLists()))
```

`Many(min_size, max_size, avg_size=)` takes an optional average size.
`reject` drops the current element; after too many rejections, `Many`
stops the collection, or rejects the test case if it's below `min_size`.

## Rejecting a test case

```mojo-sig
data.mark_invalid(why: String = "")
```

Abandons the test case as invalid (what `assume(False)` and filters do).
The `why` is counted in the `filter_too_much` health check's report.

## Type erasure: `BoxedStrategy`

`BoxedStrategy[T]` holds any `Copyable` strategy with values of type `T`,
behind a pointer and a few function pointers. `boxed(s)` makes one. Use it
for collections of strategies (`one_of` with a list), recursion, and
return types that would otherwise be long. A draw through a box costs an
indirect call.

## Running the engine directly

`run_test(test_fn, settings, name)` runs a `def(mut ConjectureData)
raises` function under the full engine and returns a `RunReport`. It's
what `given`, `given_data`, and the state machine runners are built on.
