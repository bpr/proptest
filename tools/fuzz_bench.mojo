# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""A benchmark for the fuzz loop (`FuzzTarget.fuzz`): how many test cases
it takes to find each target's bug (at most 100_000), or how many
features it covers in 20_000, over a range of seeds.

    pixi run fuzz-bench [guided|blind] [TARGET|all] [FIRST_SEED] [SEEDS]

The defaults are `guided all 1 10`. `blind` fuzzes with `guided=False`,
the baseline. Each target prints its per-seed results (-1: not found)
and a summary. To compare two versions of the fuzz loop, build this file
against each (`mojo build -O3 -I <checkout>`) with the same seeds.
"""

from std.sys import argv
from proptest import *


def settings(seed: Int) -> Settings:
    return Settings(
        database=None,
        seed=UInt64(seed),
        verbosity=Verbosity.quiet,
        phases=Phases(shrink=False, explain=False),
    )


def chain(mut data: ConjectureData) raises:
    var xs = data.draw(lists(integers(0, 15), min_size=6, max_size=6))
    for i in range(6):
        if xs[i] != i + 1:
            return
        data.feature(UInt64(i))
    fail("found it")


def rare(mut data: ConjectureData) raises:
    var noise = data.draw(lists(integers(0, 15), max_size=12))
    for i in range(len(noise)):
        data.event(String("noise ", i, " ", noise[i]))
    var xs = data.draw(lists(integers(0, 15), min_size=6, max_size=6))
    for i in range(6):
        if xs[i] != i + 1:
            return
        data.event(String("matched ", i + 1))
    fail("found it")


def shifted(mut data: ConjectureData) raises:
    # the chain comes after a list of any length: a mutation that changes
    # its length shifts the chain's choices, replayed by position
    var noise = data.draw(lists(integers(0, 15), max_size=8))
    var xs = data.draw(lists(integers(0, 15), min_size=6, max_size=6))
    for i in range(6):
        if xs[i] != i + 1:
            return
        data.feature(UInt64(i))
    if len(noise) >= 4:
        fail("found it")


def checksum(mut data: ConjectureData) raises:
    # progress is recorded before a rarely passing validity check
    var xs = data.draw(lists(integers(0, 15), min_size=6, max_size=6))
    var c = data.draw(integers(0, 63))
    var k = 0
    while k < 6 and xs[k] == k + 1:
        data.feature(UInt64(k))
        k += 1
    var s = 0
    for x in xs:
        s += x
    assume(c == (s * 7) % 64)
    if k == 6:
        fail("found it")


def parse(mut data: ConjectureData, check: Bool) raises:
    # a toy TLV format: magic "PT", then records (tag, len, payload),
    # each tag a branch; a checksum byte must match
    var b = data.draw(binary(max_size=64))
    if len(b) < 3:
        return
    if b[0] != UInt8(ord("P")):
        return
    data.feature(1)
    if b[1] != UInt8(ord("T")):
        return
    data.feature(2)
    var i = 2
    var acc = 0
    var n = 0
    while i + 1 < len(b) - 1:
        var tag = Int(b[i])
        var ln = Int(b[i + 1])
        if ln > 8 or i + 2 + ln > len(b) - 1:
            data.feature(10)
            break
        data.feature(UInt64(100 + (tag % 16) * 16 + min(n, 15)))
        if tag % 16 == 7 and ln == 4:
            data.feature(20)
            if b[i + 2] == 0xFF and b[i + 5] == 0x00:
                data.feature(21)
        acc += tag + ln
        i += 2 + ln
        n += 1
    if check:
        assume(Int(b[len(b) - 1]) == acc % 256)
    data.feature(UInt64(1000 + min(n, 15)))
    if n >= 3:
        data.feature(30)


def parser(mut data: ConjectureData) raises:
    parse(data, True)


def parser_nock(mut data: ConjectureData) raises:
    parse(data, False)


def closeness(mut data: ConjectureData) raises:
    # x + y is never drawn as is: only closeness at the traced comparison
    # guides the fuzzer
    var x = data.draw(integers(0, 100_000))
    var y = data.draw(integers(0, 100_000))
    var sum = Traced(x + y, data.comparisons)
    if sum == 150_001:
        fail("sum")


def _insertion_sort(var xs: List[Int]) -> Int:
    """Sort `xs`, returning how many elements were shifted."""
    var shifts = 0
    for i in range(1, len(xs)):
        var x = xs[i]
        var j = i
        while j > 0 and xs[j - 1] > x:
            xs[j] = xs[j - 1]
            j -= 1
            shifts += 1
        xs[j] = x
    return shifts


comptime _SORT_MAX = 24
comptime _SORT_LIMIT = _SORT_MAX * (_SORT_MAX - 1) // 2 * 95 // 100
"""Near the worst case (a reversed list): 262 of 276 shifts."""


def _sort(mut data: ConjectureData, how: Int) raises:
    # PerfFuzz's kind of bug: an input that makes the sort slow.
    # how: 0 no guidance, 1 data.count, 2 data.target
    var xs = data.draw(lists(integers(0, 1000), max_size=_SORT_MAX))
    var shifts = _insertion_sort(xs^)
    if how == 1:
        data.count(1, shifts)
    elif how == 2:
        data.target(Float64(shifts))
    if shifts >= _SORT_LIMIT:
        fail("slow")


def sort_none(mut data: ConjectureData) raises:
    _sort(data, 0)


def sort_count(mut data: ConjectureData) raises:
    _sort(data, 1)


def sort_target(mut data: ConjectureData) raises:
    _sort(data, 2)


def _two_sorts(mut data: ConjectureData, per_site: Bool) raises:
    # both sorts near their worst case: one count per sort (PerfFuzz's
    # per-site maxima), or one target score for the total
    var a = _insertion_sort(
        data.draw(lists(integers(0, 1000), max_size=_SORT_MAX))
    )
    var b = _insertion_sort(
        data.draw(lists(integers(0, 1000), max_size=_SORT_MAX))
    )
    if per_site:
        data.count(1, a)
        data.count(2, b)
    else:
        data.target(Float64(a + b))
    if a >= _SORT_LIMIT and b >= _SORT_LIMIT:
        fail("slow")


def two_sorts_count(mut data: ConjectureData) raises:
    _two_sorts(data, True)


def two_sorts_target(mut data: ConjectureData) raises:
    _two_sorts(data, False)


def find[
    F: def(mut ConjectureData) raises
](var f: F, seed: Int, cap: Int, guided: Bool) raises -> Int:
    var t = fuzz_target_data(f^, settings(seed))
    try:
        _ = t.fuzz(1e9, max_inputs=cap, guided=guided)
    except:
        return t.totals().inputs
    return -1


def features[
    F: def(mut ConjectureData) raises
](var f: F, seed: Int, n: Int, guided: Bool) raises -> Int:
    var t = fuzz_target_data(f^, settings(seed))
    _ = t.fuzz(1e9, max_inputs=n, guided=guided)
    return t.totals().features


def summary(name: String, results: List[Int], finds: Bool) -> String:
    """`results` per seed, then how many found the bug and the median
    (not found counting as worse than any), or the median feature count."""
    var line = String(name, ":")
    var sorted = List[Int]()
    var found = 0
    for r in results:
        line += String(" ", r)
        sorted.append(r if r >= 0 else Int.MAX)
        if r >= 0:
            found += 1
    sort(sorted)
    var median = sorted[len(sorted) // 2]
    if not finds:
        return String(line, "\n  median ", median, " features")
    return String(
        line,
        "\n  found ",
        found,
        "/",
        len(results),
        ", median ",
        String(median) if median != Int.MAX else String("n/a"),
        " test cases",
    )


def main() raises:
    var a = argv()
    var guided = len(a) < 2 or a[1] != "blind"
    var only = String(a[2]) if len(a) > 2 else String("all")
    var first = Int(a[3]) if len(a) > 3 else 1
    var seeds = Int(a[4]) if len(a) > 4 else 10
    comptime CAP = 100_000
    comptime FEATURE_INPUTS = 20_000
    var names: List[String] = [
        "chain",
        "rare",
        "shifted",
        "checksum",
        "closeness",
        "parser",
        "parser_nock",
        "sort_none",
        "sort_count",
        "sort_target",
        "two_sorts_count",
        "two_sorts_target",
    ]
    for name in names:
        if only != "all" and only != name:
            continue
        var results = List[Int]()
        var finds = not name.startswith("parser")
        for s in range(first, first + seeds):
            if name == "chain":
                results.append(find(chain, s, CAP, guided))
            elif name == "rare":
                results.append(find(rare, s, CAP, guided))
            elif name == "shifted":
                results.append(find(shifted, s, CAP, guided))
            elif name == "checksum":
                results.append(find(checksum, s, CAP, guided))
            elif name == "closeness":
                results.append(find(closeness, s, CAP, guided))
            elif name == "sort_none":
                results.append(find(sort_none, s, CAP, guided))
            elif name == "sort_count":
                results.append(find(sort_count, s, CAP, guided))
            elif name == "sort_target":
                results.append(find(sort_target, s, CAP, guided))
            elif name == "two_sorts_count":
                results.append(find(two_sorts_count, s, CAP, guided))
            elif name == "two_sorts_target":
                results.append(find(two_sorts_target, s, CAP, guided))
            elif name == "parser":
                results.append(features(parser, s, FEATURE_INPUTS, guided))
            else:
                results.append(features(parser_nock, s, FEATURE_INPUTS, guided))
        print(summary(name, results, finds))
