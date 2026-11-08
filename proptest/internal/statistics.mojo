# ===----------------------------------------------------------------------=== #
# proptest: property-based testing for Mojo.
# Inspired by Hypothesis (https://github.com/HypothesisWorks/hypothesis). MIT License; see LICENSE.
# ===----------------------------------------------------------------------=== #
"""Statistics of a test run: events, tables and coverage requirements.

Events are Hypothesis's (`data.event(...)`, reported by
`--hypothesis-show-statistics`); tables and coverage come from
QuickCheck's `tabulate`, `cover` and `checkCoverage`. They are collected
over the generate phase only, like Hypothesis's statistics, so replays and
shrinking don't skew them.

Coverage is checked as QuickCheck does (`Test.QuickCheck.Test`,
`sufficientlyCovered`/`insufficientlyCovered`): after `n` valid examples,
of which `k` met a requirement of fraction `p`, the requirement is
satisfied once the lower end of the Wilson score interval for `k/n` is at
least `tolerance * p`, and failed once its upper end is below `p`, each at
error rate `1 / certainty`.
"""

from std.math import sqrt, erfc

from proptest.internal.data import ConjectureResult, Status
from proptest.settings import Confidence

comptime COVERAGE_UNDECIDED = 0
comptime COVERAGE_SUFFICIENT = 1
comptime COVERAGE_INSUFFICIENT = 2


def _normal_cdf(z: Float64) -> Float64:
    return 0.5 * erfc(-z / sqrt(2.0))


def inverse_normal_cdf(p: Float64) -> Float64:
    """The `z` with `P(Z <= z) = p` for a standard normal `Z` (bisection;
    only used a handful of times per run)."""
    var lo = -40.0
    var hi = 40.0
    for _ in range(200):
        var mid = (lo + hi) / 2
        if _normal_cdf(mid) < p:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def wilson(k: Int, n: Int, z: Float64) -> Float64:
    """One end of the Wilson score interval for `k` successes in `n`
    trials (the lower end for negative `z`)."""
    var nf = Float64(n)
    var p = Float64(k) / nf
    return (
        p
        + z * z / (2 * nf)
        + z * sqrt(p * (1 - p) / nf + z * z / (4 * nf * nf))
    ) / (1 + z * z / nf)


def _percent(k: Int, n: Int) -> String:
    var x = 100.0 * Float64(k) / Float64(max(n, 1))
    var hundredths = Int(x * 100 + 0.5)
    var frac = String(hundredths % 100)
    if hundredths % 100 < 10:
        frac = "0" + frac
    return String(hundredths // 100, ".", frac, "%")


struct Statistics(Copyable, Writable):
    """What the generate phase of a run saw."""

    var cases: Int
    """Test cases run, whatever their outcome."""
    var valid: Int
    """Test cases that passed (tables and coverage count only these)."""
    var invalid: Int
    var overrun: Int
    var events: Dict[String, Int]
    """Number of test cases that recorded each event."""
    var event_order: List[String]
    var tables: Dict[String, Dict[String, Int]]
    """For each table, how often each value was recorded."""
    var table_order: List[String]
    var cover_required: Dict[String, Float64]
    """Required percentage of valid test cases, per coverage label."""
    var cover_hits: Dict[String, Int]
    var cover_order: List[String]

    def __init__(out self):
        self.cases = 0
        self.valid = 0
        self.invalid = 0
        self.overrun = 0
        self.events = Dict[String, Int]()
        self.event_order = List[String]()
        self.tables = Dict[String, Dict[String, Int]]()
        self.table_order = List[String]()
        self.cover_required = Dict[String, Float64]()
        self.cover_hits = Dict[String, Int]()
        self.cover_order = List[String]()

    def record(mut self, r: ConjectureResult) raises:
        """Count one test case."""
        if r.status == Status.INTERESTING:
            return
        self.cases += 1
        var seen = Dict[String, Bool]()
        for e in r.events:
            if e in seen:
                continue
            seen[e] = True
            if e not in self.events:
                self.events[e] = 0
                self.event_order.append(e)
            self.events[e] += 1
        if r.status == Status.INVALID:
            self.invalid += 1
            return
        if r.status == Status.OVERRUN:
            self.overrun += 1
            return
        self.valid += 1
        for entry in r.table_entries:
            if entry[0] not in self.tables:
                self.tables[entry[0]] = Dict[String, Int]()
                self.table_order.append(entry[0])
            ref t = self.tables[entry[0]]
            if entry[1] not in t:
                t[entry[1]] = 0
            t[entry[1]] += 1
        for item in r.covers.items():
            if item.key not in self.cover_required:
                self.cover_required[item.key] = item.value
                self.cover_hits[item.key] = 0
                self.cover_order.append(item.key)
            if item.key in r.covered:
                self.cover_hits[item.key] += 1

    def coverage_verdict(self, confidence: Confidence) raises -> Int:
        """Whether every coverage requirement is met, some isn't, or it
        can't be told yet, at the error rate `1 / confidence.certainty`."""
        if len(self.cover_order) == 0 or self.valid == 0:
            return COVERAGE_UNDECIDED
        var a = 1.0 / confidence.certainty
        var z_low = inverse_normal_cdf(a / 2)
        var z_high = inverse_normal_cdf(1 - a / 2)
        var all_sufficient = True
        for label in self.cover_order:
            var p = self.cover_required[label] / 100
            var k = self.cover_hits[label]
            if wilson(k, self.valid, z_high) < p:
                return COVERAGE_INSUFFICIENT
            if wilson(k, self.valid, z_low) < confidence.tolerance * p:
                all_sufficient = False
        return COVERAGE_SUFFICIENT if all_sufficient else COVERAGE_UNDECIDED

    def under_covered(self, tolerance: Float64) raises -> List[String]:
        """Labels whose observed share is below `tolerance` times the
        requirement, as report lines."""
        var out = List[String]()
        for label in self.cover_order:
            var p = self.cover_required[label]
            var k = self.cover_hits[label]
            if 100.0 * Float64(k) < tolerance * p * Float64(self.valid):
                out.append(
                    String(
                        "only ",
                        _percent(k, self.valid),
                        " ",
                        label,
                        " (in ",
                        self.valid,
                        " examples), but expected ",
                        p,
                        "%",
                    )
                )
        return out^

    def write_to(self, mut writer: Some[Writer]):
        writer.write(
            "  - ",
            self.valid,
            " passing, ",
            self.invalid,
            " invalid and ",
            self.overrun,
            " overrun examples (generate phase)\n",
        )
        try:
            if len(self.event_order) > 0:
                writer.write("  - Events:\n")
                for e in self.event_order:
                    writer.write(
                        "    * ", _percent(self.events[e], self.cases), ", ", e
                    )
                    writer.write("\n")
            for name in self.table_order:
                ref t = self.tables[name]
                var total = 0
                for item in t.items():
                    total += item.value
                writer.write("  - ", name, " (", total, " values):\n")
                # most frequent first
                var keys = List[String]()
                for item in t.items():
                    var j = len(keys)
                    while j > 0 and t[keys[j - 1]] < item.value:
                        j -= 1
                    keys.insert(j, item.key)
                for key in keys:
                    writer.write(
                        "    * ", _percent(t[key], total), ", ", key, "\n"
                    )
            if len(self.cover_order) > 0:
                writer.write("  - Coverage:\n")
                for label in self.cover_order:
                    writer.write(
                        "    * ",
                        _percent(self.cover_hits[label], self.valid),
                        " ",
                        label,
                        " (required ",
                        self.cover_required[label],
                        "%)\n",
                    )
        except:
            pass
