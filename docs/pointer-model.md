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

The source Rc helper currently makes this order explicit using a real shared
local: copy the pointer, increment the count, and return the local. It exposes no
Rc view during the temporary mismatch and restores the caller's full invariant
at return. Compiler scheduling of a future owner's logical start, independently
of runtime pointer construction, is the next step. Such scheduling belongs to
generic ownership checking and must not recognize Rc's counter or layout.

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
