# Test generic code

To test a generic function, you have to pick a type to test it at. The
obvious choice, `Int`, can hide bugs: a property may pass because of
something particular to integers, such as arithmetic coincidences, or
because a function quietly relies on behavior only `Int` has.

`PolyA`, `PolyB`, and `PolyC` are opaque stand-in types for this (Haskell
QuickCheck's `Test.QuickCheck.Poly`). Each holds an integer, but supports
only equality, ordering, hashing, and printing. Testing a generic function
at `PolyA` shows that it works for any type with just those operations.

```mojo
from proptest import check, PolyA

def reverse[T: Copyable](xs: List[T]) -> List[T]:
    var out = List[T]()
    for i in range(len(xs) - 1, -1, -1):
        out.append(xs[i].copy())
    return out^

def main() raises:
    def reverse_twice(xs: List[PolyA]) -> Bool:
        return reverse(reverse(xs)) == xs

    check(reverse_twice)
    print("passed")
```

They print with their tag, so a counterexample is easy to read:
`given([A(0), A(1)])`. Use different stand-ins for different type
parameters (`Dict[PolyB, PolyC]`), so that a function that mixes them up
fails to compile, or fails the test.

`Poly[tag]` makes more stand-in types: `Poly["Key"]` prints as `Key(3)`.
