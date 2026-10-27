# Owning references

`plane(T)` is unique allocation ownership. `owner(T)` is a move-only lifetime
claim that may coexist with other claims to the same allocation. Both have one
pointer word of runtime representation. `&T` is a non-owning borrow and adds no
claim. These are generic primitives; the compiler has no Rc counter or algorithm.

```evg
fn main() -> usize {
    let allocation: plane(usize) = alloc(42);
    let first = share_owner(allocation);
    let second = duplicate_owner(&first);
    proof shared: owners(first) == 2;
    release_owner(first);
    let unique = recover_owner(second);
    *unique
}
```

- `share_owner` consumes a unique plane and returns its first owning reference.
- `duplicate_owner` borrows a live owning reference and creates another claim.
- `owners` is an ideal observation of the allocation's total live claims.
- `release_owner` consumes a claim and requires that another claim remains.
- `recover_owner` consumes the sole claim, proved by `owners(value) == 1`, and
  returns the unique plane. Its payload address and existing borrows stay unchanged.

Implicit cleanup of a raw `owner(T)` also requires uniqueness. It recovers the
unique plane, runs payload cleanup, and releases the allocation. Two raw owners
cannot simply fall out of scope: the library must explicitly release a nonfinal
claim before destroying the final one. This keeps raw ownership from becoming
silent forgetting and leaves runtime policy to library code.

An incoming `owner(T)` has a symbolic total of at least one. Its single visible
token does not prove that the caller has no other owners. Calls involving these
capabilities recheck the actual body and storage, as existing heap calls do.
`old(owners(value))` reads the entry census. Moving a handle changes its slot,
while its allocation and census stay intact. Creating or releasing a claim
changes the census revision and expires old census evidence, even if a later
operation restores the same numeric count. Payload writes use a separate logical
region and preserve census evidence. Final destruction invalidates data borrows.

Native code erases claim bookkeeping and census observations. Sharing and
recovery move pointer words; duplication reads the borrowed pointer; releasing a
nonfinal claim emits no counter update. Any runtime counter and its proof belong
in an Evergreen library. The interpreter independently checks live token IDs.

This is the initial sequential capability layer. Ownership transitions in loops
and transitions while representation facts are lifted remain unsupported.
They are rejected rather than approximated by a count of local bindings. These capabilities are an
experimental ownership layer. Arc additionally needs atomic resource
transitions and interference rules. No concurrent shared-ownership claim is made.
The frontend's resource transitions and machine-code erasure remain trusted
implementation boundaries rather than independently checked kernel theorems.

Conditional code can now consume claims when both arms leave exactly the same
live token set and symbolic total for each preexisting allocation. For example,
both arms may release the same nonfinal claim, or both may recover and destroy
the same unique allocation. A temporary duplication/release on just one arm can
also reconverge, but its old census evidence expires at the join. Equal counts
with different live tokens cannot be merged. Different tokens or allocation
lifetimes instead use [resource case proofs](resource-cases.md), checking the
complete remaining continuation separately in each state. No token identity or
live allocation is invented. See
[`conditional_ownership.evg`](../examples/conditional_ownership.evg).

[`owning_references.evg`](../examples/owning_references.evg) runs in the interpreter
and native backend without admissions. The selected Rc direction is
allocation-backed, move-only credits. `allocation_credits::Credit` now wraps real
generic lifetime claims in an opaque source API for duplication, merging, payload
borrowing, and unique recovery. The earlier arithmetic credit libraries still
grant no allocation authority. The [source Rc](rc.md) now couples these claims
to a checked runtime counter, an automatic source destructor, and a `usize`
payload. General payload types and concurrent ownership still need work.
See [allocation-backed credits](allocation-credits.md).
Invariant lifting remains a separate general language facility.

## Reference contracts: intended direction

The reference validity rule should be exposed as a logical specification, rather
than inferred from pointer bits alone. The proposed sketch is a word-sized
`Reference<T>` with a refinement like `typeof(memory_at(address)) == T`.
Generic reference declarations and `memory_at` are not implemented yet.

The observation needs an ideal witness for the live allocation identity and
generation, plus the typed projection and byte range. This establishes bounds,
alignment, initialization, and the interpretation as `T`. A record and its first
field can share an address while having different valid typed projections.
Reusing an address for a later allocation must preserve the distinction between
their identities. Copies preserve the original witness.

Ordinary stores evolve the plane's fact-state revision while retaining its
allocation identity. Facts about contents depend on those revisions. An owning
pointer additionally carries allocation/destruction authority. These witnesses
are ideal metadata; the current target's runtime representation remains one
pointer word. Other targets must specify their own representation.
