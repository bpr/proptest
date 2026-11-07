# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

proptest is a port of Hypothesis (Python property-based testing; local
source at ~/src/python/hypothesis/hypothesis/src/hypothesis) to Mojo 1.3.
README.md has the user-facing API, the proptest <-> Hypothesis file map, and
the list of deliberate differences.

## Commands

```sh
pixi install
pixi run test                                   # every tests/test_*.mojo
bash tests/run_all.sh tests/test_engine.mojo    # one file (inside `pixi shell`)
pixi run mojo run -I . tests/test_engine.mojo   # same, without the env vars
pixi run examples
pixi run package                                # build/proptest.mojoc
pixi run test-numojo                            # extras/ (needs NuMojo; see extras/run_tests.sh)
python3 tools/gen_charmap.py                    # regenerate internal/charmap_data.mojo
python3 tools/gen_from_type.py                  # regenerate strategies/types.mojo (edit the script, not the output)
pixi run format
```

Each test file ends with `TestSuite.discover_tests[__functions_in_module()]().run()`;
`tests/run_all.sh` sets `PROPTEST_DATABASE=none`. Compiling a test file takes
about a minute (generic instantiation); the tests themselves run in seconds.
`TestSuite`'s per-test timings are unreliable (they overstate run time);
use `time` on a built binary when measuring.

## Architecture

- Strategies (`strategies/`) are structs conforming to `Strategy` with an
  associated `comptime Value` and `do_draw(self, mut data: ConjectureData)`.
  Draw through `data.draw(s)` / `draw(data, s)`, which wraps the draw in a
  span labelled `s.label()`; the shrinker relies on spans.
- Combinators are free functions over closure type parameters
  (`map[S, R, //, F: def(S.Value) raises -> R](var s: S, var f: F)`):
  trait default methods generic over closures of `Self.Value` hit a
  compiler bug. Combinator structs are `Copyable where` their parts are.
- `BoxedStrategy[T]` type-erases a strategy with a raw heap pointer and thin
  function pointers (draw/clone/free) built from nested non-capturing defs
  in its generic `__init__` (pattern from std/format/tstring.mojo).
  `one_of` and `recursive` use it.
- Control flow: `ConjectureData.mark_*` set `status`, freeze, and raise
  `Error(STOP_TEST)`; `assume` raises `Error(UNSATISFIED_ASSUMPTION)`. Any
  other error is a test failure; its "interesting origin" is the
  `At file:line:col: Kind` prefix (`engine.interesting_origin`).
- `ConjectureRunner[F]` is generic over the test closure type and owns it;
  `Shrinker[F]` takes the runner by move and gives it back with `release()`.
  Results are shared as `Result = ArcPointer[ConjectureResult]`; identity
  is `result[].id`.
- No globals in Mojo, so per-run state (constants pools, RNG, tree) lives on
  the runner and is passed down.
- Integer choices are `Int128`; strings/bytes are `List[UInt32]` in
  `ChoiceValue.seq`.
- Shrinking: passes are numbered (`N_PASSES`) and run one position at a
  time by `Shrinker.step`/`greedy_shrink` (Hypothesis's
  `fixate_shrink_passes`); add a pass by extending `pass_name`,
  `positions` and `pass_at`. After shrinking, `Shrinker.explain` varies
  each top-level draw (`ConjectureData.arg_spans`) and the comments reach
  the report via `ConjectureData.arg_comments` on the final replay.
- Targeting: per-label hill climbing in the engine, plus a Pareto front
  (`internal/pareto.mojo`, only with a database) optimised in
  `core.run_test` with `Shrinker(pareto=True)`, capped at
  10 x max_examples calls.
- `from_type` (`strategies/types.mojo`) is generated; struct building
  writes fields at `reflect[T].field_offset` into uninitialised memory.
- docs/differences-from-hypothesis.md records every deviation and why;
  update it when porting more.

## Mojo 1.3 notes

See the stdlib sources at ~/src/mojo/repos/modular/Mojo/stdlib/std and the
docs/changelog in ~/src/mojo/repos/modular/Mojo/docs when unsure of an API.
Closure capture lists go after `raises`: `def f(x: Int) raises {mut self} -> Bool:`.
No negative list indexing; no `len(String)`; `Float64.MAX` is infinity
(use `MAX_FINITE`).
