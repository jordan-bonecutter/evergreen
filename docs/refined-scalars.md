# Refined scalar types

```evg
type NonZero usize where self != 0;

impl NonZero {
    fn new(x: usize) -> Self
        where x != 0
        ensures result == x
    {
        x
    }
}

fn main() -> usize {
    let n = NonZero::new(42);
    n
}
```

The named type has its underlying scalar's size and alignment, with no runtime
tag. Entering the type checks its condition; arithmetic uses the underlying
scalar and produces an ordinary scalar result. Assigning that result back to the
refined type checks the condition again. Overflow retains the existing unspecified
machine-value semantics and cannot establish a missing refinement.

The implementation lowers construction and scalar access to the existing
invariant-bearing storage machinery. Borrowing as the underlying scalar projects
that storage: writes through the borrow must preserve the enclosing invariant.
It does not reinterpret arbitrary `&usize` values as `&NonZero`.

Named refinements retain the normal explicit `Copy` rule. Add
`impl Copy for NonZero {}` to copy the named value. Reading its underlying Copy
scalar is a field read; moving the named value still invalidates its old binding.

The current bases are machine integers, Boolean values, and mathematical integers
in ideal declarations. Refined pointers and aggregates are not supported by this
syntax. Existing aggregate types continue to use struct fields and invariants.
See [the executable example](../examples/refined_scalar.evg) for a checked write
through a borrow and layout proofs.
