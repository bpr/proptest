# Generate functions

Code that takes a function as an argument (a sort with a custom key, a
`map` over a container, a retry policy) should work for *any* function,
not just the few you think to write. `functions[A](returns)` generates
functions from `A` to the values of the strategy `returns` (Hypothesis's
`functions`, QuickCheck's `Fun`).

```mojo
from proptest import given, functions, integers, Function, fail, Settings

def main():
    def monotone(f: Function[Int, Int]) raises:
        if f(1) > f(2):
            fail("not monotone")

    try:
        given(functions[Int](integers(0, 9)), monotone, Settings(database=None))
    except e:
        print(e)
```

```text
Falsifying example (functions.mojo:9:14):
    given({1->1, 2->0})
At functions.mojo:7:17: AssertionError: not monotone
```

A generated `Function[A, R]`:

- **is memoized**: calling it twice with the same argument gives the same
  result, so it behaves like a pure function;
- **draws each new argument's result from the test case**, so the results
  shrink like any other generated value;
- **prints as the table of calls made**, `{x->y, ...}`. So that the table
  is complete, `given` prints its arguments after the test has run.

The argument type `A` must be usable as a dictionary key (`KeyElement`),
`Copyable`, and `Writable`.

## A function only lives as long as its test case

A `Function` draws its results from the test case that created it. After
that test case ends, it can't draw any more, and calling it raises an
error ("... after its test case ended") instead of returning a value. So
don't keep generated functions between test cases, and don't use one from
`example(...)` outside the call.
