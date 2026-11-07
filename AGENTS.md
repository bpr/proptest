# AGENTS.md

Project context for AI coding assistants working in this repository.

## Overview

proptest is a port of Hypothesis (Python property-based testing) to Mojo 1.3.

- Hypothesis source (reference for porting): `~/src/python/hypothesis/hypothesis/src/hypothesis`
- `README.md`: user-facing API, the proptest <-> Hypothesis file map, and the list of deliberate differences.
- `docs/differences-from-hypothesis.md`: every deviation from Hypothesis and why.

## Tech stack

- Mojo 1.3 (nightly), managed with pixi.
- Stdlib sources: `~/src/mojo/repos/modular/Mojo/stdlib/std`
- Docs/changelog: `~/src/mojo/repos/modular/Mojo/docs` (check these when unsure of an API).
- Optional: NuMojo, used only by `extras/`.

## Project layout

| Path | Contents |
|---|---|
| `strategies/` | Strategy structs and combinators |
| `strategies/types.mojo` | `from_type`, **generated** by `tools/gen_from_type.py` |
| `internal/` | Engine internals (e.g. `pareto.mojo`) |
| `internal/charmap_data.mojo` | **Generated** by `tools/gen_charmap.py` |
| `tests/` | `test_*.mojo` suites and `run_all.sh` |
| `extras/` | NuMojo integration and its tests |
| `tools/` | Code generators (Python) |
| `docs/` | Design notes, including the differences doc |

## Architecture

### Strategies
- Strategies are structs conforming to `Strategy`, with an associated
  `comptime Value` and `do_draw(self, mut data: ConjectureData)`.
- Always draw through `data.draw(s)` / `draw(data, s)`, which wraps the draw in a
  span labelled `s.label()`. The shrinker relies on spans.
- Combinators are free functions over closure type parameters, e.g.
  `map[S, R, //, F: def(S.Value) raises -> R](var s: S, var f: F)`.
  Trait default methods generic over closures of `Self.Value` hit a compiler bug.
- Combinator structs are `Copyable where` their parts are.
- `BoxedStrategy[T]` type-erases a strategy with a raw heap pointer and thin
  function pointers (draw/clone/free) built from nested non-capturing defs in its
  generic `__init__` (pattern from `std/format/tstring.mojo`). Used by `one_of`
  and `recursive`.

### Control flow
- `ConjectureData.mark_*` sets `status`, freezes, and raises `Error(STOP_TEST)`.
- `assume` raises `Error(UNSATISFIED_ASSUMPTION)`.
- Any other error is a test failure; its "interesting origin" is the
  `At file:line:col: Kind` prefix (`engine.interesting_origin`).

### Engine and ownership
- `ConjectureRunner[F]` is generic over the test closure type and owns it.
- `Shrinker[F]` takes the runner by move and returns it with `release()`.
- Results are shared as `Result = ArcPointer[ConjectureResult]`; identity is `result[].id`.
- Mojo has no globals, so per-run state (constants pools, RNG, tree) lives on the
  runner and is passed down.

### Choice representation
- Integer choices are `Int128`.
- Strings/bytes are `List[UInt32]` in `ChoiceValue.seq`.

### Shrinking
- Passes are numbered (`N_PASSES`) and run one position at a time by
  `Shrinker.step` / `greedy_shrink` (Hypothesis's `fixate_shrink_passes`).
- To add a pass, extend `pass_name`, `positions`, and `pass_at`.
- After shrinking, `Shrinker.explain` varies each top-level draw
  (`ConjectureData.arg_spans`); comments reach the report via
  `ConjectureData.arg_comments` on the final replay.

### Targeting
- Per-label hill climbing in the engine.
- A Pareto front (`internal/pareto.mojo`, only with a database) optimised in
  `core.run_test` with `Shrinker(pareto=True)`, capped at 10 x `max_examples` calls.

### `from_type`
- `strategies/types.mojo` is generated. Struct building writes fields at
  `reflect[T].field_offset` into uninitialised memory.

## Rules

- **Generated files:** edit the generator in `tools/`, never `strategies/types.mojo`
  or `internal/charmap_data.mojo` directly, then regenerate.
- **Deviations from Hypothesis:** record each one, with the reason, in
  `docs/differences-from-hypothesis.md` when porting more.

## Testing

- Each test file ends with `TestSuite.discover_tests[__functions_in_module()]().run()`.
- `tests/run_all.sh` sets `PROPTEST_DATABASE=none`.
- Compiling a test file takes about a minute (generic instantiation); tests run in seconds.
- `TestSuite`'s per-test timings overstate run time. Use `time` on a built
  binary when measuring performance.

## Mojo 1.3 gotchas

- Closure capture lists go after `raises`: `def f(x: Int) raises {mut self} -> Bool:`
- No negative list indexing.
- No `len(String)`.
- `Float64.MAX` is infinity; use `MAX_FINITE`.
