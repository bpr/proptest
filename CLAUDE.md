# CLAUDE.md

> **Note:** Core project architecture and coding standards are defined in [AGENTS.md](./AGENTS.md).

@AGENTS.md

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
python3 tools/gen_from_type.py                  # regenerate strategies/types.mojo
pixi run format                                 # format / lint
```

## Workflow

- Prefer running a single test file over `pixi run test` while iterating;
  each file takes about a minute to compile.
- Run `pixi run format` before considering a change done.
- When you need a Mojo API, check the stdlib sources and changelog listed in
  AGENTS.md rather than guessing; Mojo 1.3 differs from older Mojo.
