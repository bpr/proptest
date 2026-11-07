#!/bin/bash
# Run every proptest test file. Run from the repository root: pixi run test
# (or `pixi run test tests/test_engine.mojo` for one file).
export PROPTEST_DATABASE=none
files=("$@")
if [ ${#files[@]} -eq 0 ]; then
    files=(tests/test_*.mojo)
fi
failed=()
for f in "${files[@]}"; do
    echo "=== $f"
    mojo run -I . "$f" || failed+=("$f")
done
if [ ${#failed[@]} -gt 0 ]; then
    echo "FAILED: ${failed[*]}"
    exit 1
fi
echo "All test files passed."
