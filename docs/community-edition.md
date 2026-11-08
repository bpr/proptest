# Submitting proptest to modular-community

Wait until Mojo 1.3.0 is released. The modular-community CI builds only
against the stable channel (`https://conda.modular.com/max`), never
`max-nightly`, and proptest needs Mojo 1.3. A recipe that fails CI is
deleted automatically after four weeks.

To check whether 1.3.0 is out:

```sh
pixi search -c https://conda.modular.com/max mojo-compiler
```

Status as of 2026-11-07: the stable channel has 1.2.0. The recipe already
builds and passes its test from GitHub (commit `b3a08e7`) with the
1.3.0.dev2026110705 nightly.

## Checklist

### 1. Update proptest

- [ ] In `pixi.toml`, raise the floor to the release:
      `mojo = ">=1.3.0,<2"`, and move `channels` to
      `https://conda.modular.com/max` (keep `max-nightly` if you still want
      nightlies).
- [ ] Run `pixi install`, `pixi run test`, `pixi run examples`, and
      `pixi run test-numojo`, and fix anything 1.3.0 broke.
- [ ] In `conda.recipe/recipe.yaml`, set `mojo_version: "1.3.0"`. Bump
      `version` too if you're releasing more than 0.1.0, and keep it in
      step with `version` in `pixi.toml`.
- [ ] Build and test the package locally against the stable channel:
      ```sh
      rattler-build build --recipe conda.recipe/recipe.yaml \
        -c conda-forge -c https://conda.modular.com/max
      ```
      The test should print `proptest package OK` and `all tests passed!`.
- [ ] Commit and push. Note the full 40-character hash: `git rev-parse HEAD`.
- [ ] Optional: tag it, `git tag v0.1.0 && git push --tags`.

### 2. Add the recipe to your modular-community fork

- [ ] Sync the fork with upstream and create a branch, e.g. `add-proptest`.
- [ ] Create `recipes/proptest/` with copies of
      `conda.recipe/recipe.yaml` and `conda.recipe/test_package.mojo`.
- [ ] In `recipes/proptest/recipe.yaml`:
  - [ ] Replace the `source` entry (`path: ..`) with the pushed commit:
        ```yaml
        source:
          - git: https://github.com/bpr/proptest.git
            rev: <full 40-character commit hash>
        ```
  - [ ] Delete the header comment, which refers to files in the proptest repo.
- [ ] Build it with the channels the CI uses:
      ```sh
      rattler-build build --recipe recipes/proptest/recipe.yaml \
        -c conda-forge -c https://conda.modular.com/max \
        -c https://prefix.dev/modular-community
      ```

### 3. Open the pull request

- [ ] Commit `recipes/proptest/` and open a PR against
      `modular/modular-community`.
- [ ] Watch the CI. It also builds on linux-aarch64 and osx-arm64, which
      have only been tested here on linux-64.
- [ ] No CodeQL setup is needed. That is required only for packages
      containing Python or other non-Mojo code, and proptest is all Mojo.

### 4. After it's merged

- [ ] In `README.md`, replace the "once Mojo 1.3 is released" note under
      Setup with install instructions: add
      `https://repo.prefix.dev/modular-community` to `channels` in
      `pixi.toml`, then `pixi add proptest`.

## Later releases

- New proptest version: bump `version` (recipe and `pixi.toml`), set
  `build.number: 0`, push, then update `rev` (and `version`) in
  `recipes/proptest/recipe.yaml` and open a new PR.
- New Mojo release, same proptest: change `mojo_version`, increment
  `build.number`, and open a PR. The compiler is pinned exactly because a
  `.mojoc` only loads in the compiler that built it.

See `docs/publishing.md` for how the recipe works and why proptest has to wait for 1.3.0.
