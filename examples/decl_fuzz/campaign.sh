#!/bin/bash
# Usage: examples/decl_fuzz/campaign.sh BINARY OUT [ROUNDS]
#
# A long decl_fuzz campaign that goes on past failures: ROUNDS (default 3)
# rounds of $STAGE2 stage 2 programs (default 2000), $NEAR near misses of
# all kinds (2000) and $MUTANTS mutants of all kinds (3000), without
# shrinking. BINARY is a built decl_fuzz; MOJO selects the compiler, as
# for the oracles. Run k of round i (k = 0, 1, 2) has seed
# $SEED + 3 (i - 1) + k (SEED defaults to 1000).
#
# Each run's verdicts go to OUT/<run> (one line per program), cases that
# aren't OK to OUT/<run>.bad/ and known crashes to OUT/<run>.known/, each
# with its program and verdict.txt; the run's output to OUT/<run>.log.
# After each run it prints the run's verdict counts.
set -u
if [ $# -lt 2 ]; then
    echo "usage: $0 BINARY OUT [ROUNDS]" >&2
    exit 2
fi
bin=$(realpath "$1")
out=$(realpath -m "$2")
rounds=${3:-3}
seed=${SEED:-1000}
mkdir -p "$out"
cd "$(dirname "${BASH_SOURCE[0]}")/../.." || exit 1  # (the scripts' paths)

run() {  # name seed count [VAR=value...]
    local name=$1 s=$2 n=$3
    shift 3
    rm -rf "$out/$name" "$out/$name.bad" "$out/$name.known"
    env "$@" DECL_FUZZ_LOG="$out/$name" PROPTEST_SEED="$s" \
        PROPTEST_MAX_EXAMPLES="$n" DECL_FUZZ_NO_SHRINK=1 \
        "$bin" "$out/work_$name" > "$out/$name.log" 2>&1
    local status=$?
    echo "== $name $(date +%H:%M) exit $status:" \
        $(sort "$out/$name" 2>/dev/null | uniq -c | sort -rn | tr '\n' ' ')
}

for i in $(seq 1 "$rounds"); do
    base=$((seed + 3 * (i - 1)))
    run "stage2_$i" "$base" "${STAGE2:-2000}"
    run "near_$i" $((base + 1)) "${NEAR:-2000}" DECL_FUZZ_NEAR=1
    run "mu_$i" $((base + 2)) "${MUTANTS:-3000}" DECL_FUZZ_MUTANTS=1
done
