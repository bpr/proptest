#!/bin/bash
# Run every proptest test file. Run from the repository root: pixi run test
# (or `pixi run test tests/test_engine.mojo` for one file).
#
# Files run in parallel, PROPTEST_JOBS at a time (default: the number of
# CPUs). Each file's output is printed in one piece when it finishes.
export PROPTEST_DATABASE=none
files=("$@")
if [ ${#files[@]} -eq 0 ]; then
    files=(tests/test_*.mojo)
fi

# One file: run it directly, so its output streams as it goes
if [ ${#files[@]} -eq 1 ]; then
    echo "=== ${files[0]}"
    mojo run -I . "${files[0]}" || { echo "FAILED: ${files[0]}"; exit 1; }
    echo "All test files passed."
    exit 0
fi

jobs_max="${PROPTEST_JOBS:-$(nproc)}"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
start=$SECONDS

run_one() {  # index file
    local t0=$SECONDS
    mojo run -I . "$2" > "$out/$1.log" 2>&1
    echo $? > "$out/$1.status"
    echo $((SECONDS - t0)) > "$out/$1.time"
}

# Print a finished file's output, once
report() {  # index
    local i=$1 f=${files[$1]}
    echo "=== $f ($(cat "$out/$i.time")s)"
    cat "$out/$i.log"
    touch "$out/$i.reported"
}

report_finished() {
    for i in "${!files[@]}"; do
        if [ -f "$out/$i.time" ] && [ ! -f "$out/$i.reported" ]; then
            report "$i"
        fi
    done
}

for i in "${!files[@]}"; do
    while [ "$(jobs -rp | wc -l)" -ge "$jobs_max" ]; do
        wait -n
        report_finished
    done
    run_one "$i" "${files[$i]}" &
done
wait
report_finished

failed=()
for i in "${!files[@]}"; do
    [ "$(cat "$out/$i.status")" -ne 0 ] && failed+=("${files[$i]}")
done
echo "${#files[@]} files in $((SECONDS - start))s, $jobs_max at a time."
if [ ${#failed[@]} -gt 0 ]; then
    echo "FAILED: ${failed[*]}"
    exit 1
fi
echo "All test files passed."
