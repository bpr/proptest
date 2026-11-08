# Suppress a health check

Health checks catch tests that run but can't test well: strategies that
reject almost everything, or that produce data too large or too slow to
generate. When one fails, the test fails with `FailedHealthCheck` and a
suggestion. Usually you should fix the cause; when you can't, or the check
is wrong for your test, suppress it:

```mojo
~from std.testing import assert_true, assert_equal
~from proptest import *
~def main() raises:
~    var s = integers()
~    def prop(x: Int) raises:
~        pass
~
    given(s, prop, Settings(suppress_health_check=[HealthCheck.too_slow]))
```

## The health checks

| Health check | Fails when | Usual fix |
|---|---|---|
| `filter_too_much` | Most test cases are rejected by `filter`, `filter_map`, `assume`, or `Outcome.discard()`. | Generate valid values directly. The report names the top rejection reasons if you passed `reason=` to `filter`. |
| `data_too_large` | Many test cases exceed the limit on the number of choices (8,192). | Pass `max_size` to collection strategies, or bound recursion. |
| `too_slow` | Generating data is slow: few valid examples after a long time drawing. | Generate smaller data, or move expensive setup out of the strategy. |
| `large_base_example` | Even the simplest input the strategies can produce is very large. | Make large fields optional, or lower `min_size`. |

The stateful runners suppress `data_too_large` and `large_base_example`
themselves, because programs of 50 steps are large by design.

## Before suppressing

A health check usually points at a real problem in the test:

- **`filter_too_much`** means most of the run went to inputs that were
  thrown away. A test that "passes" this way has run on few inputs, and
  those may be the ones the filter happened to let through. See
  [Adapting strategies](../tutorial/adapting-strategies.md#filtering-strategy-inputs).
- **`too_slow`** and **`data_too_large`** mean each example costs a lot,
  so fewer inputs are tried in the same time, and shrinking is slow.

Time limits on the test *body* aren't a health check: that's the
`deadline` setting, which fails individual slow examples.
