#!/bin/bash
# Usage: check_rejected.sh DIR
#
# DIR/program.mojo is an ill-typed mutant (stage 3 of decl_fuzz): a
# well-typed FM program with one error, on the lines marked `# MUTANT`.
# Builds it at -O0 and prints one line:
#
#   OK                        rejected, with an error on a marked line
#   ACCEPTED                  the compiler accepted it (its output follows)
#   BUILD_CRASH status ...    the compiler crashed
#   KNOWN #<issue> ...        it crashed as a filed bug does (known_crashes.txt)
#   BUILD_TIMEOUT             the compiler ran for over $BUILD_TIMEOUT s
#   WRONG_LINE                rejected, but with no error on a marked line
#   NO_MARK                   no line is marked (a generator bug)
#
# followed by details, kept off the first line so that a failure looks the
# same on every run and proptest can shrink it. The script's own stderr
# goes to DIR/oracle_stderr.txt, so that only the verdict is printed.
#
# MOJO selects the compiler, e.g. a nightly in another pixi environment:
#   MOJO="pixi run --manifest-path ../nightly mojo"
MOJO="${MOJO:-mojo}"
BUILD_TIMEOUT="${BUILD_TIMEOUT:-300}"
source "$(dirname "${BASH_SOURCE[0]}")/known.sh"
cd "$1" || exit 1
exec 2> oracle_stderr.txt
rm -f o0

marked=$(grep -n "# MUTANT$" program.mojo | cut -d: -f1)
if [ -z "$marked" ]; then
    echo NO_MARK
    exit 0
fi

timeout "$BUILD_TIMEOUT" $MOJO build -O0 -o o0 program.mojo > build.txt 2>&1
status=$?
if [ $status -eq 124 ]; then
    echo BUILD_TIMEOUT
    exit 0
fi
if [ $status -gt 128 ] || grep -q "LLVM ERROR\|Assertion\|please submit\|Stack dump" build.txt; then
    issue=$(known_crash O0 build.txt)
    if [ -n "$issue" ]; then
        echo -n "KNOWN #$issue "
    fi
    echo "BUILD_CRASH status $status"
    grep -v "^\s*$" build.txt | head -30
    exit 0
fi
if [ $status -eq 0 ]; then
    echo ACCEPTED
    echo "marked lines:" $marked
    timeout 20 ./o0 2>&1 | head -20
    echo "exit status ${PIPESTATUS[0]}"
    exit 0
fi
errors=$(grep -oE "program\.mojo:[0-9]+:[0-9]+: error" build.txt | cut -d: -f2 | sort -nu)
for line in $errors; do
    if echo "$marked" | grep -qx "$line"; then
        echo OK
        exit 0
    fi
done
echo WRONG_LINE
echo "marked lines:" $marked
grep "error:" build.txt | head -10
