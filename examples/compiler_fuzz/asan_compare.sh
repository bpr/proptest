#!/bin/bash
# Usage: asan_compare.sh DIR
#
# Like build_and_compare.sh, but builds program.mojo at -O0 and -O3 with
# AddressSanitizer (and LeakSanitizer), and skips comptime.mojo. Prints one
# line:
#
#   OK                        all clean, and the two builds agree
#   BUILD_CRASH <which> ...   the compiler crashed
#   BUILD_FAIL <which>        the compiler rejected the program
#   ASAN <which> <kind>       e.g. "ASAN O3 heap-use-after-free"
#   LEAK <which>              memory was never freed
#   RUN_FAIL O0=s O3=s        a build crashed or hung (exit statuses)
#   UNBALANCED                a Tracked value wasn't destroyed exactly once
#   DIFF_O3                   -O0 and -O3 print different results
#
# followed by details. Run the fuzzer with it as the second argument:
#   build/compiler_fuzz build/compiler_fuzz_work \
#       examples/compiler_fuzz/asan_compare.sh
MOJO="${MOJO:-mojo}"
cd "$1" || exit 1
rm -f o0 o3

$MOJO build -O0 --sanitize address -o o0 program.mojo > build_o0.txt 2>&1 &
pid_o0=$!
$MOJO build -O3 --sanitize address -o o3 program.mojo > build_o3.txt 2>&1
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

export ASAN_OPTIONS=detect_leaks=1:exitcode=99
timeout 60 ./o0 > out_o0.txt 2> err_o0.txt
run_o0=$?
timeout 60 ./o3 > out_o3.txt 2> err_o3.txt
run_o3=$?

for w in O0 O3; do
    err=err_$(echo $w | tr A-Z a-z).txt
    if grep -q "ERROR: AddressSanitizer" $err; then
        echo "ASAN $w $(grep -m1 -o 'AddressSanitizer: [a-z-]*' $err | cut -d' ' -f2)"
        head -40 $err
        exit 0
    fi
    if grep -q "ERROR: LeakSanitizer" $err; then
        echo "LEAK $w"
        head -40 $err
        exit 0
    fi
done
if [ $run_o0 -ne 0 ] || [ $run_o3 -ne 0 ]; then
    echo "RUN_FAIL O0=$run_o0 O3=$run_o3"
    head -10 err_o0.txt err_o3.txt
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
echo OK
