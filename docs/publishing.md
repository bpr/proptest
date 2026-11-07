# Publishing proptest

proptest is packaged as a conda package with
[rattler-build](https://rattler-build.prefix.dev/). The recipe is
`conda.recipe/recipe.yaml`. The package installs one file,
`lib/mojo/proptest.mojoc`, which Mojo finds without any `-I` flag.

## Building locally

```sh
rattler-build build --recipe conda.recipe/recipe.yaml \
  -c conda-forge -c https://conda.modular.com/max-nightly
```

This builds the working tree, runs `conda.recipe/test_package.mojo` against
the installed package, and writes `output/linux-64/proptest-<version>-*.conda`.

## The modular-community channel

Community packages live in
[modular/modular-community](https://github.com/modular/modular-community).
Its CI builds every recipe with the channels `conda-forge`,
`https://conda.modular.com/max` and `https://prefix.dev/modular-community`.
It does **not** use `max-nightly`. A recipe that needs a nightly compiler
can't resolve its dependencies there. The CI records the failure, and a
recipe still failing after four weeks is deleted automatically.

proptest needs Mojo 1.3, which is only on the nightly channel so far, so it
can be submitted once `mojo-compiler 1.3.0` is on the stable `max` channel.

### Submitting

1. Push the release commit to https://github.com/bpr/proptest.
2. In a fork of modular-community, copy `conda.recipe/recipe.yaml` and
   `conda.recipe/test_package.mojo` to `recipes/proptest/`.
3. In `recipes/proptest/recipe.yaml`:
   - replace the `source` entry with
     ```yaml
     source:
       - git: https://github.com/bpr/proptest.git
         rev: <full 40-character commit SHA>
     ```
   - set `mojo_version` to the stable release, e.g. `"1.3.0"`.
4. Build it there with the same channels the CI uses:
   ```sh
   rattler-build build --recipe recipes/proptest/recipe.yaml \
     -c conda-forge -c https://conda.modular.com/max \
     -c https://prefix.dev/modular-community
   ```
5. Open a pull request.

proptest is pure Mojo, so the CodeQL requirement for packages that contain
Python or other languages doesn't apply. The generators in `tools/` aren't
part of the package.

### Releasing a new version

Bump `version` in `conda.recipe/recipe.yaml` and `pixi.toml`, set
`build.number` back to 0, and update `rev` in the modular-community recipe.
To rebuild the same version for a new Mojo release, change `mojo_version`
and increment `build.number`.

The compiler is pinned exactly (`mojo-compiler ==<version>`) because a
`.mojoc` only loads in the compiler that built it.
