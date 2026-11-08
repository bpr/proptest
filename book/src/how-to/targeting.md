# Guide the search with targets

Random generation is good at finding bugs that many inputs trigger, and
bad at finding ones that only extreme inputs trigger: very large totals,
very deep nesting, long-running operations. *Targeted* property-based
testing helps. The test reports a score, and proptest searches for inputs
that make the score larger (Hypothesis's `target()`).

## Report a score

In a `given_data` test, call `data.target(score, label)`:

```mojo
from proptest import given_data, lists, integers, ConjectureData, Settings

def main():
    def prop(mut data: ConjectureData) raises:
        var xs = data.draw(lists(integers(0, 1000), max_size=10), "xs")
        var total = 0
        for x in xs:
            total += x
        data.target(Float64(total), "sum")
        if total > 9000:
            raise Error(String("sum is ", total))

    try:
        given_data(prop, Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (target.mojo:15:19):
    Draw 1 (xs): [1, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000]
sum is 9001
```

The bug needs a list whose sum exceeds 9000: ten elements, nine of them
almost at the maximum. Random lists of this kind are almost never that big.
In ten runs of this test, proptest found the failure in eight with the
target, and in none of ten without it.

## How it works

After half of the examples have been generated, proptest runs a *target
phase*: for each label, it takes the inputs with the highest scores and
hill-climbs from them, trying small changes to the choices that made them
and keeping changes that raise the score. With the example database
enabled, it also keeps a Pareto front of the best inputs across labels
between runs.

## Tips

- Use a score that rises steadily as inputs approach the bug: a size,
  a count, an error magnitude, an elapsed time. A score that's 0 or 1
  gives the hill climber nothing to follow.
- Use a separate `label` for each score; each is maximized separately.
- Targeting complements a test's assertions; it doesn't replace them.
  The score only steers the search towards inputs that might fail.
- `Phases(target=False)` turns the target phase off.
