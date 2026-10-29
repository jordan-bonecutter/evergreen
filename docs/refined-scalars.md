# Refined types

```evg
type NonZero usize where self != 0;

impl NonZero {
    fn new(x: usize) -> Self
        where x != 0
        ensures result == x
    {
        NonZero(x)
    }
}

fn main() -> usize {
    let n = NonZero::new(42);
    n
}
```

The named type has its underlying type's size and alignment, with no runtime
tag. Construction is explicit: `NonZero(x)` proves its condition. A plain
`usize` does not implicitly become `NonZero` in a return, argument, field, or
assignment. Arithmetic uses the underlying scalar and produces an ordinary
scalar result; wrap that result explicitly to enter the refined type again. Overflow retains the existing unspecified
machine-value semantics and cannot establish a missing refinement.

The implementation lowers construction and scalar access to the existing
invariant-bearing storage machinery. Borrowing as the underlying scalar projects
that storage: writes through the borrow must preserve the enclosing invariant.
It does not reinterpret arbitrary `&usize` values as `&NonZero`.

Named refinements retain the normal explicit `Copy` rule. Add
`impl Copy for NonZero {}` to copy the named value. Reading its underlying Copy
scalar is a field read; moving the named value still invalidates its old binding.

There is no base-type whitelist. Records, arrays, references, owners, and nested
refinements use the same ordinary storage and invariant checks. For example:

```evg
type Ordered<T> [T; 2] where self[0] < self[1];
// Construct with Ordered::<usize>([20, 22]).
```

Field access, indexing, and dereferencing project the underlying storage.
Ownership remains ordinary record ownership: wrapping moves a non-Copy payload,
and cleanup drops it normally. This does not add new permissions for extracting
non-Copy fields, returning borrowed fields, or changing storage through aliases.
Ideal bases still require ideal declarations; unsupported underlying operations
remain unsupported.

See [the executable example](../examples/refined_scalar.evg) for a checked write
through a borrow and layout proofs.
