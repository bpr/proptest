#!/bin/bash
# Usage: build_and_compare.sh DIR
#
# DIR holds abi.h, callee.c, ref.c and program.mojo (see abi_fuzz.mojo).
# Builds program.mojo at -O0 and -O3, linked with callee.c, and the C
# reference (ref.c and callee.c) with gcc, runs all three, and prints one
# line:
#
#   OK                        all agree
#   BUILD_CRASH <which> ...   a compiler crashed
#   BUILD_FAIL <which>        a compiler rejected the program
#   RUN_FAIL ...              a program crashed or hung (exit statuses)
#   DIFF_O0, DIFF_O3          a Mojo build differs from the C reference
#
# followed by details.
#
# MOJO selects the compiler, e.g. a nightly in another pixi environment:
#   MOJO="pixi run --manifest-path ../nightly mojo"
MOJO="${MOJO:-mojo}"
CC="${CC:-gcc}"
cd "$1" || exit 1
rm -f o0 o3 ref callee.o

$CC -O1 -w -c callee.c -o callee.o > build_callee.txt 2>&1
status_callee=$?
$CC -O1 -w ref.c callee.c -o ref > build_ref.txt 2>&1
status_ref=$?
if [ $status_callee -ne 0 ] || [ $status_ref -ne 0 ]; then
    echo "BUILD_FAIL C"
    head -30 build_callee.txt build_ref.txt
    exit 0
fi

$MOJO build -O0 -o o0 program.mojo -Xlinker callee.o > build_o0.txt 2>&1 &
pid_o0=$!
$MOJO build -O3 -o o3 program.mojo -Xlinker callee.o > build_o3.txt 2>&1
status_o3=$?
wait $pid_o0
status_o0=$?

report_build() {  # name status log
    if [ "$2" -ne 0 ]; then
        if [ "$2" -gt 128 ] || grep -q -i "LLVM ERROR\|Assertion\|please submit\|Stack dump\|crash" "$3"; then
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

timeout 20 ./ref > out_ref.txt 2> err_ref.txt
run_ref=$?
timeout 20 ./o0 > out_o0.txt 2> err_o0.txt
run_o0=$?
timeout 20 ./o3 > out_o3.txt 2> err_o3.txt
run_o3=$?

if [ $run_ref -ne 0 ] || [ $run_o0 -ne 0 ] || [ $run_o3 -ne 0 ]; then
    echo "RUN_FAIL ref=$run_ref O0=$run_o0 O3=$run_o3"
    head -5 err_ref.txt err_o0.txt err_o3.txt
    exit 0
fi
if ! cmp -s out_ref.txt out_o0.txt; then
    echo DIFF_O0
    diff out_ref.txt out_o0.txt | head -20
    exit 0
fi
if ! cmp -s out_ref.txt out_o3.txt; then
    echo DIFF_O3
    diff out_ref.txt out_o3.txt | head -20
    exit 0
fi
echo OK
