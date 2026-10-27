# Owning references

`unique(T)` carries destruction authority for a separately allocated plane.
`shared(T)` carries one owning claim that can coexist with other claims to that
allocation. Both have one pointer word of runtime representation. `&T` is a
non-owning borrow and adds no claim. The compiler recognizes no Rc counter or
algorithm.

```evg
fn main() -> usize {
    let first: shared(usize) = alloc(42);
    let second = first;
    proof two: owner_count(first) == 2;
    leak(first);
    let final: unique(usize) = move(second);
    *final
}
```

A unique rvalue converts to an expected `shared(T)` by transferring its claim.
On the current target, shared pointers have Copy permission through the target's
explicit pointer Copy declaration. Reading one as a runtime value creates a
fresh claim. Specification observations, address calculation, and borrows do not
copy owning pointers. Copy records and arrays copy each shared-pointer leaf;
copying must preserve the source and result refinements. `move(handle)` explicitly
transfers a claim without creating another one.

A consumed shared pointer converts to an expected `unique(T)` only after proving
`owner_count(handle) == 1` in the current state. Its allocation address stays
unchanged. `let final: unique(T) = handle` normally copies first and therefore
cannot prove uniqueness; use `move(handle)` to transfer the original claim.
A non-owning borrow cannot promote, even with a count-one fact.

`leak(handle)` consumes the binding and relinquishes its claim without running
payload cleanup or reclaiming the allocation. Implicit shared-pointer cleanup
does the same, including for the final claim. Payload borrows can still access
the leaked allocation; they cannot manufacture ownership. `drop(shared_value)`
is rejected. To destroy the payload, promote the pointer and drop the resulting
unique value. A source wrapper such as Rc supplies its own checked Drop policy.

The previous special share/duplicate/release/recover owner operations have been
removed. Those names are available for ordinary source functions. The old
`plane(T)`, `owner(T)`, and `owners(...)` spellings are not aliases.

An incoming `shared(T)` has a symbolic total of at least one. Its single visible
token does not prove that the caller has no other owners. Calls involving these
capabilities recheck the actual body and storage, as existing heap calls do.
`old(owner_count(value))` reads the entry census. Moving a handle changes its slot,
while its allocation and census stay intact. Creating or releasing a claim
changes the census revision and expires old census evidence, even if a later
operation restores the same numeric count. Payload writes use a separate logical
region and preserve census evidence. Final destruction invalidates data borrows.

Native code erases claim bookkeeping and census observations. Authority
conversion transfers pointer words; copying copies those words; relinquishing
a claim emits no counter update or deallocation. Any runtime counter and its
proof belong in an Evergreen library. The interpreter independently checks live
token IDs.

This is the initial sequential capability layer. Ownership transitions in loops
and transitions while representation facts are lifted remain unsupported.
They are rejected rather than approximated by a count of local bindings.
Replacing owning fields through references still needs ownership effect
summaries and is rejected, including for shared fields. Opaque shared-pointer
array elements need census snapshots before they can be materialized; a
by-value copy which needs element claims is charged before expansion.
These capabilities are an experimental ownership layer. Arc additionally needs atomic resource
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
and native backend without admissions. The existing source Rc uses
allocation-backed, move-only credits; the loan-scoped arithmetic reservation
proposal is described separately in [pointer-model.md](pointer-model.md). `allocation_credits::Credit` now wraps real
generic lifetime claims in an opaque source API for duplication, merging, payload
borrowing, and unique recovery. The earlier arithmetic credit libraries still
grant no allocation authority. The [source Rc](rc.md) now couples these claims
to a checked runtime counter, an automatic source destructor, and generic
payloads. Concurrent ownership still needs work.
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
