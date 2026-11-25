#!/bin/bash
# Usage: build_and_compare.sh DIR
#
# DIR holds program.mojo (a generated FM program), comptime.mojo (its entry
# points evaluated at compile time) and expected.txt (the generator's own
# evaluation). Builds program.mojo at -O0 and -O3 and comptime.mojo, all
# in parallel, runs the three, and prints one line:
#
#   OK                        all four agree
#   BUILD_CRASH <which> ...   the compiler crashed
#   KNOWN #<issue> ...        it crashed as a filed bug does (known_crashes.txt)
#   BUILD_TIMEOUT <which>     the compiler ran for over $BUILD_TIMEOUT s
#   BUILD_FAIL <which>        the compiler rejected the program
#   RUN_FAIL O0=s O3=s        a build crashed or hung (exit statuses)
#   UNBALANCED                a Res wasn't destroyed exactly once
#   DIFF_O3                   -O0 and -O3 print different results
#   DIFF_COMPTIME             compile time and run time (-O0) differ
#   DIFF_EXPECTED             -O0 differs from the generator's evaluation
#
# followed by details, kept off the first line so that a failure looks the
# same on every run and proptest can shrink it. The script's own stderr
# (bash reporting a crashed build, say) goes to DIR/oracle_stderr.txt, so
# that only the verdict is printed.
#
# MOJO selects the compiler, e.g. a nightly in another pixi environment:
#   MOJO="pixi run --manifest-path ../nightly mojo"
MOJO="${MOJO:-mojo}"
BUILD_TIMEOUT="${BUILD_TIMEOUT:-300}"
source "$(dirname "${BASH_SOURCE[0]}")/known.sh"
cd "$1" || exit 1
exec 2> oracle_stderr.txt
rm -f o0 o3 ct

timeout "$BUILD_TIMEOUT" $MOJO build -O0 -o o0 program.mojo > build_o0.txt 2>&1 &
pid_o0=$!
timeout "$BUILD_TIMEOUT" $MOJO build -O3 -o o3 program.mojo > build_o3.txt 2>&1 &
pid_o3=$!
timeout "$BUILD_TIMEOUT" $MOJO build -o ct comptime.mojo > build_ct.txt 2>&1
status_ct=$?
wait $pid_o0
status_o0=$?
wait $pid_o3
status_o3=$?

report_build() {  # name status log
    if [ "$2" -ne 0 ]; then
        if [ "$2" -eq 124 ]; then
            echo "BUILD_TIMEOUT $1"
        elif [ "$2" -gt 128 ] || grep -q -i "LLVM ERROR\|Assertion\|please submit\|Stack dump\|crash" "$3"; then
            local issue
            issue=$(known_crash "$1" "$3")
            if [ -n "$issue" ]; then
                echo -n "KNOWN #$issue "
            fi
            echo "BUILD_CRASH $1 status $2"
        else
            echo "BUILD_FAIL $1"
        fi
        grep -v "^\s*$" "$3" | head -30
        exit 0
    fi
}
report_build O0 $status_o0 build_o0.txt
report_build O3 $status_o3 build_o3.txt
report_build comptime $status_ct build_ct.txt

timeout 20 ./o0 > out_o0.txt 2> err_o0.txt
run_o0=$?
timeout 20 ./o3 > out_o3.txt 2> err_o3.txt
run_o3=$?
./ct > out_ct.txt 2> err_ct.txt

if [ $run_o0 -ne 0 ] || [ $run_o3 -ne 0 ]; then
    echo "RUN_FAIL O0=$run_o0 O3=$run_o3"
    diff out_o0.txt out_o3.txt | head -10
    exit 0
fi
if grep -q UNBALANCED out_o0.txt out_o3.txt; then
    echo UNBALANCED
    grep -H UNBALANCED out_o0.txt out_o3.txt | head -10
    exit 0
fi
if ! cmp -s out_o0.txt out_o3.txt; then
    echo DIFF_O3
    diff out_o0.txt out_o3.txt | head -20
    exit 0
fi
# The lines for constant arguments start with "c"; comptime.mojo prints
# only those.
grep "^c " out_o0.txt > out_o0_const.txt
if ! cmp -s out_o0_const.txt out_ct.txt; then
    echo DIFF_COMPTIME
    diff out_o0_const.txt out_ct.txt | head -20
    exit 0
fi
if ! cmp -s out_o0.txt expected.txt; then
    echo DIFF_EXPECTED
    diff expected.txt out_o0.txt | head -20
    exit 0
fi
echo OK
