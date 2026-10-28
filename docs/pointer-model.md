# Pointer authority and early ownership

The bootstrap now implements `unique(T)`, `shared(T)`, and `owner_count(pointer)`.
Ordinary shared-pointer copies create census claims, moves transfer claims, and
contextual conversion to unique authority requires a current sole-owner proof.
The special owner-operation intrinsics have been removed. See
[owning-references.md](owning-references.md) for executable syntax and cleanup.
The current source Rc returns ordinary shared pointers from its clone helper.
It has no Credit wrapper or publication step.

## Pointer kinds

`unique(T)` is a live pointer carrying destruction authority. For the allocation
and generation it identifies, `owner_count(pointer) == 1`. The observation is
about that allocation, not every allocation containing the same payload type.

`shared(T)` is a live owning pointer that can coexist with other owning pointers
to the same allocation. Promoting it to `unique(T)` requires a current sole-owner
proof and consumes the shared handle. The allocation's identity and payload
address stay unchanged. A stale count observation cannot authorize promotion.
Moving a handle transfers its claim without changing the census.

Weakening unique authority to shared authority consumes the unique handle and
retains one claim. Copying a shared pointer creates another claim. The current target grants pointer Copy permission explicitly, which
includes `shared(T)`. A copy differs from a move or specification observation.

`&T` remains a non-owning borrow. It adds no owner. A borrow plus a count-one
fact does not manufacture an owning handle. Reads still require the original
plane generation to remain live. Destroying an allocation expires its views.

Destroying shared storage requires promotion first. Abandoning a pointer without
destroying its allocation uses `leak(handle)`. Shared scope exit relinquishes
the claim without reclaiming the allocation; unique scope exit destroys it. Neither route may retain a usable copy of a
consumed handle or create authority from raw address equality.

## Early ownership

A future shared owner may count toward an allocation's lifetime before its
pointer value is materialized. It must be tied to that allocation and generation,
fulfilled exactly once, and accounted for on every returning path. An early
owner prevents unique recovery and deallocation; it supplies no early access or
drop authority. Materialization fulfills the existing ownership claim without
adding another owner. Unfulfilled obligations cannot silently disappear.

An assignment explicitly marks the point where a future owner begins:

```evg
self.data.count = self.data.count + 1 starts_owner(self.data);
proof accurate: nat(self.data.count) == owner_count(self.data);
Self {data: self.data}
```

The marker names a pure stored `shared(T)` place. Its pointer identity is resolved
before the right-hand side runs. At the store event the compiler starts one
additional owner of that allocation and generation, before checking the resulting
invariants. The later ordinary shared-pointer copy materializes that owner;
it does not increment the census again. Multiple places can be listed to start
multiple owners. The marker has no runtime representation.

Rc uses this directly in its clone method, with no allocation helper, Credit
wrapper, or separate publication step. Accuracy is available after the increment
and before construction, including when calling code requiring a valid Rc.
Removing the marker makes that intermediate accuracy proof fail.

A returning function must fulfill every owner it started. An inherited caller
promise may survive a nested call; copies fulfill the most recent pending owner
of the same allocation, so an inner operation fulfills its own promise first.
A copy cannot fulfill a promise for another allocation or generation. Completing
a promise preserves census proofs; a later additional copy expires them.

The host plane store now represents an early owner as a distinct phase of an
already counted token. Only materialization grants an owning-reference handle.
Repeated materialization, a foreign plane/arena/generation, and attempts to use
the early token for reads, release, duplication, or unique recovery are rejected.
Snapshots retain pending obligations independently. Branches must agree on
fulfillment, and a returning function must fulfill every owner it started.
An inherited caller obligation may survive a nested call.

Both the checker and interpreter enforce these transitions. Native code erases
ownership metadata and emits the original checked assignment and pointer copy.
[`examples/early_ownership.evg`](../examples/early_ownership.evg) demonstrates
explicit counting, proof reuse across materialization, and eventual unique
recovery without a wrapper type.

[`proofs/early_ownership.evg`](../proofs/early_ownership.evg) checks the arithmetic
transitions with the internal proof kernel and no admissions. It proves that
an outstanding future owner blocks final release, including when the original
materialized owner disappears first. These arithmetic statements do not mint
pointer authority or prove machine atomicity; token identity and access rights
are checked separately by the host store and its finite-history tests.

For Arc, the successful atomic increment must establish the corresponding early
owner at the same logical event. A failed update supplies no new ownership.
This removes the need for a source-level credit type, but still requires checked
atomic semantics, publication, and interference rules.

## Concurrent work still required

The sequential implementation is not a concurrency proof. Arc needs a
specification for interference, atomic counter observations, publication, and
destruction. A previous count-one observation is not automatically stable.
Borrowed accesses in other threads must also have a checked lifetime argument.
No thread-transfer or shared-access marker may replace these proofs.

Full `match` support, including payload binding and destructuring, remains
grouped with the patterns work. The current implementation supports Boolean
matches and scoped statement arms.

The clause currently marks source assignments. It does not make a store atomic.
An Arc primitive needs a corresponding ownership event at the successful atomic
update, with no event on failure; ordinary function-return boundaries are not
substitutes for that machine event. Atomic annotations and concurrent interference
remain unfinished. Ownership transitions in loops and while invariants are lifted
still require additional resource frames and are rejected.
