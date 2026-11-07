#!/bin/bash
# Run every example. Run from the repository root: pixi run examples
set -e
for f in examples/*.mojo; do
    echo "=== $f"
    mojo run -I . "$f"
    echo
done
