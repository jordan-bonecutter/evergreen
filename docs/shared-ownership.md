# Shared ownership: implementation obligations

Rc and Arc must be Evergreen libraries. The compiler should understand generic
resource ownership, invariant framing, and primitive machine operations. It
must not recognize an Rc type, count field, clone function, or destructor.

This document records the next implementation boundary, not a claim that Rc or
Arc is implemented. Unique `plane(T)` ownership and generic `owner(T)` lifetime
claims work today. Source counter protocols still need guarded token joins and
invariant-opening support for those transitions.

## Counted resources, including intermediate operations

`proofs/SharedOwnership.lean` specifies one allocation with distinct token IDs.
A token is an owner, a reserved clone, or a retiring owner. At every modeled
counter step:

```
count = number of owners + reserved clones + retiring owners
```

Token IDs are unique and never reused within an allocation. A clone reservation
requires an existing owner and spare counter capacity. It increments the count
and creates a fresh reserved token in one step. Publication changes the token
from reserved to owner, without touching the count. Retirement changes an owner
into a retiring token; decrement consumes that token and subtracts one.

The model proves preservation for arbitrary finite interleavings, not just the
previous two-operation arithmetic examples. Every remaining token, including a
pending clone, implies the allocation is still active. Only a decrement that
observes an old count of one issues a reclamation permit. That permit names the
last retiring token. At that point no owner or pending operation remains.
Consuming the permit frees the allocation, and the freed state is terminal:
there is no second free, resurrection, or new clone transition.

This explains the interval where there are no published owners but a clone is
pending: the count remains positive because its reserved token still exists.
An equality counting only completed owners is not an invariant of every step.
The zero-count implication remains valid throughout.

The Lean file also rejects the lost-update state produced by two non-atomic
increments that both read one and both write two. Thus ordinary stores cannot
implement the Arc reserve transition under concurrent access.

## Rc implementation boundary

For Rc, a checked thread-local region can exclude concurrent counter accesses.
A local update can then realize a reserve/decrement transition using ordinary
loads and stores. A lifted representation fact must be restored before an
operation exposes the record to code that relies on it. Ownership of tokens
must remain move-only during that update.

The intended generic mechanism is a reference model with an ownership role.
`&T` borrows access without taking responsibility for the allocation's lifetime;
an owning pointer carries that responsibility and is move-only. Both can have the
same address representation. An allocator may own the backing memory while a
library owns responsibility for one allocated plane inside it.

The compiler ideal primitive `owners(p)` reports the number of live
owning references to the relevant plane. Ordinary borrows do not count. This
must be compiler-maintained semantic state, not a user-supplied number or a scan
of the bindings visible in the current function. Hidden caller references,
fields, arrays, moves, function results, and cleanup all have to participate.
Observing the count must neither create an owner nor generate a runtime load.

Rc then proves that its runtime counter agrees with that owner census when its
representation invariant is closed. When it proves that the releasing handle
is the sole owner, the generic reference rules can establish uniqueness and
permit destruction. The compiler must know neither Rc nor its counter field.
Numeric credits alone do not establish uniqueness or authorize access/freeing.

Borrowed references are excluded from `owners`, but they still obey plane
liveness: release makes subsequent accesses invalid. This does not introduce a
Rust-style requirement that mutable references themselves be unique. A count
observation is a state-indexed fact; creating another owner invalidates an
unprotected earlier uniqueness observation. Arc additionally needs interference
rules rather than treating an earlier count observation as stable.

The owner census must use logical plane identity and generation, not raw address
equality. Interior views and the distinction between dropping a subplane and
releasing its backing allocation need explicit rules. Counted clone reservations
in the abstract ledger represent outstanding lifetime responsibility, even
before a handle is published. They cannot be forged by arbitrary ideal code.

`proofs/Planes.lean`, in `OwnerReferences`, now specifies a generic per-plane
census independently of Rc counters. Its store includes all owning token IDs
and a separate collection of borrowed references. Well-formedness forbids
repeated owner IDs. Admitted transitions require a live owner before duplication,
a fresh token ID, and a current state-indexed uniqueness witness before freeing.
Raw state-construction functions are not themselves admitted ownership rules.

Lean checks that borrowing does not alter or grant ownership; rearranging owner
bindings preserves the census; duplication/release change it by one; count one
plus an actual owning reference identifies the sole owner; and duplication
invalidates a previous uniqueness observation. Freeing clears the owner census
and invalidates borrowed references. Arbitrary finite admitted runs preserve
well-formedness and cannot recreate ownership from a zero-owner state.

The model's uniqueness witness is a proof about one current store, not a second
runtime owning pointer. A source-level recovery operation still has to consume
the previous owning binding and change its type without copying its token.
Compiler affinity, caller framing, storage/projection identity, nominal
invariants, and native refinement are not established by these model theorems.

The shared Rust plane store now has a concrete host-side counterpart in
`src/shared/planes/owners.rs`: unique owners can be transferred to tracked owner
tokens, duplicated into fresh identities, released, or recovered as unique only
when one token remains. Borrows do not affect the census. Direct plane removal
and replacing writes reject tracked shared planes until uniqueness is recovered;
recovery consumes the old token while preserving payload identity and borrows.
Dropping the recovered unique plane invalidates those borrows normally.

These opaque host handles describe semantic token identity. Copying the Rust
handle does not mint an owner; reusing a consumed token is rejected. New token
IDs are fresh even across checker snapshots, and state changes in one snapshot
do not affect another. Tests cover stale/forged identities, cross-plane/arena
use, duplicate release, re-sharing, and attempted bypass of uniqueness.

The store also exposes immutable `OwnerCensus` observations. They name a live
plane generation, an ownership revision, and the total registered token count.
Borrowing and ordinary payload writes preserve that revision. Sharing,
duplication, release, and uniqueness recovery create fresh revisions, including
across checker snapshots. Returning to the same numeric count cannot revive an
old observation. `recover_unique_owner_at` requires both a live owning token
and a current count-one observation for that exact plane. An observation alone
grants no ownership. The source checker now connects owning references to these
identities, with a separate symbolic total for unknown caller-held claims.

The low-level host store permits releasing the last token without reclamation;
that operation leaks and never manufactures a uniqueness right. The source API
is stricter: `release_owner` must prove another claim remains, while implicit
cleanup or `recover_owner` must prove sole ownership. Raw owning values cannot
silently lose the last allocation responsibility.

See [`owning-references.md`](owning-references.md) for the source capability API,
its native erasure, and checked examples. Incoming owner counts are symbolic and
include opaque caller ownership; they are not the number of handles visible in
the callee. Actual heap calls recheck resource transitions against caller storage.

The next Rc work is guarded ownership joins and opening its accounting invariant
around a source counter update plus a generic claim transition. Numeric credits
are retained as generic ideal-resource tests, not as Rc's allocation authority.
Independent kernel checking of the resource-state rules and native preservation
also remains unfinished. The capability tests do not establish a complete Rc or
Arc implementation or a concurrent memory model.

## Arc and the memory model

Arc needs linearizable counter operations. A suitable first algorithm is a
compare-exchange loop: read a candidate count, prove it is below the maximum,
and attempt to replace that exact count with its successor. Failed attempts do
not mint a token. Successful attempts create the reservation at that atomic
step. Incrementing first and detecting overflow afterward could expose a
wrapped count; it does not implement this protocol.

A dropping handle consumes its token with an atomic decrement. The old value,
not a separate later zero check, determines who receives reclamation authority.
This does not require a mutex around the whole Arc operation.

Linearizable counting is only one obligation. The proposed initial ordering
contract is a relaxed successful clone increment, a release decrement, and an
acquire fence before final payload destruction. The implementation must prove
that preceding releases become visible to the final destructor under the chosen
memory model. Publishing a handle to another thread also needs a proven
synchronization edge; a relaxed count increment alone does not publish data.
These ordering contracts are not implemented or proved under a weak-memory model.
The first generic `extern compare_exchange64` target operation now emits a
locked x86-64 compare-exchange and has a sequential interpreter specification.
Its contract lives in `stdlib/x86_64_atomics/x86_64_atomics.evg` and remains explicitly trusted;
this is not yet an implementation of the concurrent resource transition.

The Lean ledger abstracts each counter operation as indivisible. It does not
model caches, reads-from edges, release sequences, hardware instructions,
thread scheduling, or payload accesses. Those must be connected by a refinement
proof before this becomes an Arc safety argument.

The generic retry loops live in `stdlib/atomic_counter/atomic_counter.evg`; increment checks
saturation before choosing its desired word, and decrement returns the observed
old count. They are actual Evergreen code executed by both backends, with only
the target compare-exchange contract trusted. Their present checked contracts
still describe sequential execution.

Retries use verified `while` loops rather than self-recursion, so the native
recursive-activation budget does not limit the number of attempts. Each loop
states its unchanged-until-completion invariant and explicitly proves the CAS
observation and preserved invariant before iteration-local values are cleaned
up. Saturation and empty decrements retain their existing checked behavior.
The interpreter's execution fuel still bounds interpreted retries. No concurrent
interference or progress guarantee is claimed by these sequential contracts.

The Lean protocol relates each attempt's word effect to a strong CAS at the
atomic point. With the corresponding token held, a successful attempt is a
permitted ledger step; a failed or saturated attempt is a stutter. It does not
claim that the compiler has implemented that joint word/resource update yet.

## Facts across interference

The existing checker reasons about sequential execution. An ordinary `old(...)`
snapshot denotes function entry; it does not automatically denote an atomic
operation's linearization point. A shared counter can change between an earlier
load and the compare-exchange. The concurrent rule must therefore open the
shared invariant at the atomic step, use the observed word from that step, and
close the invariant with the appropriate token transition.

Afterward, stable resource facts such as ownership of a reservation can persist;
a raw equality saying the shared counter still equals an earlier observation
cannot persist without protection. Failed compare-exchange attempts do not
publish a reservation, even if an earlier load appeared to permit incrementing.
A helper's ordinary sequential postcondition is not automatically a concurrent
specification. The thread checker must reject sharing until those interference
and resource obligations have been discharged.

## Thread transfer and shared access

Thread safety must follow from verified access/resource effects. An Rc handle
has local counter-update authority and therefore cannot be transferred into a
context that may race those updates. Arc counter authority uses atomic steps,
but that alone says nothing about whether its payload can be shared safely.

Moving ownership to another thread requires a transfer proof, including that
its eventual destructor may execute there. Concurrent shared reads require a
shared-access proof for the payload. Mutation needs exclusive/disjoint resource
authority or a synchronization protocol whose invariant protects that access.
User-written marker declarations alone must not establish these properties.

No thread API or checked transfer/shared-access predicate exists yet. Weak
references, upgrades, uniqueness queries, cyclic allocation, and resurrection
are outside this first protocol. Each needs its own library contract and
resource proof; none should become an Rc-specific compiler exception.
