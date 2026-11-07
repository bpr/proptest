#!/bin/bash
# Run the NuMojo strategy tests. NUMOJO_PARENT is the directory containing
# a Mojo 1.3-compatible `numojo` package; by default, MojoDEC's vendored
# copy next to this repository.
set -e
NUMOJO_PARENT=${NUMOJO_PARENT:-../MojoDEC/third_party}
if [ ! -d "$NUMOJO_PARENT/numojo" ]; then
    echo "numojo not found in $NUMOJO_PARENT (set NUMOJO_PARENT)" >&2
    exit 1
fi
export PROPTEST_DATABASE=none
mojo run -I . -I extras -I "$NUMOJO_PARENT" extras/tests/test_numojo.mojo
