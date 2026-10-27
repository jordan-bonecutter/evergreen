# Pointer authority and sequential credit design

The bootstrap now implements `unique(T)`, `shared(T)`, and `owner_count(pointer)`.
Ordinary shared-pointer copies create census claims, moves transfer claims, and
contextual conversion to unique authority requires a current sole-owner proof.
The special owner-operation intrinsics have been removed. See
[owning-references.md](owning-references.md) for executable syntax and cleanup.
The loan-scoped reservation model below remains a proposal; the current source
Rc uses credits which already hold owning pointers.

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

## Sequential Rc credits

Rc's runtime counter and credit protocol belong in source code. A proposed
accounting relation is:

```
nat(data.count) = owner_count(data) + reserved_credits(data)
```

The additive form also states that credits do not exceed the count. Natural
subtraction is truncated, so `count - credits == owners` alone would also admit
`count == 0, credits == 1, owners == 0`.

For one synchronous clone with a loan-scoped reservation:

| Boundary | Runtime count | Owning pointers | Credits |
| --- | --- | --- | --- |
| Entry | n | n | 0 |
| Reservation produced | n + 1 | n | 1 |
| Credit published as pointer | n + 1 | n + 1 | 0 |

Counter increment and credit creation must form one checked logical operation;
publication must consume the credit when it creates the new pointer. These are
proof-state transitions. A sequential implementation can use an ordinary
counter store and erased bookkeeping; no runtime transaction is implied.

A reservation confined to clone cannot be interleaved by another sequential
caller when it does not escape or invoke client callbacks. The checker must
establish the required loan and effect boundaries rather than recognizing Rc.
How source credits are associated with a plane and conserved is still an
implementation obligation; this proposal adds no compiler-known credit class.

Credits that can escape as independent promises of future owning pointers need
a lifetime argument of their own. Counting only published pointers would permit
a sole published pointer to satisfy the upgrade test while such a promise
remains. Either that credit participates in lifetime ownership, or its loan
must prevent a later publication after the original handle is consumed. This
is separate from the nonescaping sequential case.

## Concurrent work still required

The sequential accounting relation is not a concurrency proof. Arc needs a
specification for interference, atomic counter observations, publication, and
destruction. A previous count-one observation is not automatically stable.
Borrowed accesses in other threads must also have a checked lifetime argument.
No thread-transfer or shared-access marker may replace these proofs.

Full `match` support, including payload binding and destructuring, remains
grouped with the patterns work. The current implementation supports Boolean
matches and scoped statement arms.
