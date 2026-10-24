# Shared ownership: implementation obligations

Rc and Arc must be Evergreen libraries. The compiler should understand generic
resource ownership, invariant framing, and primitive machine operations. It
must not recognize an Rc type, count field, clone function, or destructor.

This document records the next implementation boundary, not a claim that Rc or
Arc is implemented. Unique `plane(T)` ownership works today; a plane owner cannot
yet be split into independently live shared allocation capabilities.

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
must remain affine during that update.

The missing generic mechanism is allocation authority behind a library-owned
invariant: the invariant owns the allocation, while each public handle owns an
affine fragment sufficient to keep it live. A final-release proof must recover
the unique authority needed to destroy the payload and deallocate the plane.
The existing numeric credits cannot do this: they do not authorize access or
freeing, and must not silently acquire that power.

Connecting this mechanism to the checker must preserve plane identity and
generation checks, opaque library representations, and returned-reference
provenance. The current proof does not establish that an Evergreen program
cannot forge the modeled tokens. That requires the actual resource rules and
valid/invalid compiler tests, not another trusted contract asserting Rc safety.

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
Its contract lives in `stdlib/x86_64_atomics.evg` and remains explicitly trusted;
this is not yet an implementation of the concurrent resource transition.

The Lean ledger abstracts each counter operation as indivisible. It does not
model caches, reads-from edges, release sequences, hardware instructions,
thread scheduling, or payload accesses. Those must be connected by a refinement
proof before this becomes an Arc safety argument.

The generic retry loops now live in `stdlib/atomic_counter.evg`; increment checks
saturation before choosing its desired word, and decrement returns the observed
old count. They are actual Evergreen code executed by both backends, with only
the target compare-exchange contract trusted. Their present checked contracts
still describe sequential execution.

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
