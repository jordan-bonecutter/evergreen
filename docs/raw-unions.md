# Raw union implementation

The intended language construct is the README's untagged `A | B`, including
`T | shape(T)` for optional initialization. No hidden runtime discriminant is
part of this representation. A programmer-visible flag and a proved invariant
can distinguish alternatives; the compiler must prove the active type before
interpreting the bytes as a member.

The initial implementation layer supplies shared syntax and layout:

- `|` combines type members, including fields, arrays, and function signatures.
  Nested unions flatten. Reference prefixes bind first: `&A | B` differs from
  `&(A | B)`.
- Payloads start at the same address. Storage uses the maximum member alignment
  and maximum member size rounded to that alignment, without a tag word.
- `shape(T)` has T's size and alignment and no initialized fields or destructor
  work. `shape(shape(T))` is not another initialization state.
- Raw unions are move-only and require explicit active-member elimination;
  structural Copy permission cannot silently duplicate their resources or
  synthesize a destructor.
- Module qualification, primitive representation lowering, dependency ordering,
  and expansion limits traverse the member types. Duplicate members and invalid
  layouts are rejected.

The next layer now executes reference-free union values in the interpreter and
native backend. This includes scalar members, arrays, nominal records, and
records with destructors whose representation contains no references or heap
owners. `typeof(value)` is an ideal active-type observation. It has no runtime
tag and cannot be evaluated by runtime code. A function can require
`where (typeof(value) == usize)`; using that value as a `usize` then proves the
active-member obligation and consumes the original union binding. References to
union storage can copy an active Copy member without consuming the union.

An explicitly typed binding injects a member into shared storage. A source flag
and a refinement such as `present == (typeof(data) == usize)` can distinguish an
optional payload. Boolean equality expresses the equivalence here. Both branches
must eliminate their raw union; neither unused unions nor enclosing records
without a suitable destructor can silently discard them. Native injection clears
the shared storage before copying the member at offset zero.

Member refinements are assumed under their selector case. An impossible inactive
member cannot erase an overflow obligation for another member. Type observations
participate in the plane/revision evidence model, and admitted member evidence
expires on storage replacement. The interpreter additionally detects an admitted
inactive-member interpretation rather than interpreting its payload as a
different runtime type.

Ideal execution cannot consume a runtime union or an array of runtime unions
and erase the required runtime elimination. Pure ideal code can construct and
eliminate its own unions; proof-only sum values remain erased.

`examples/raw_union.evg` implements a source-defined optional word using
`usize | shape(usize)`. `examples/raw_union_drop.evg` demonstrates that only the
selected nominal member runs its destructor, and that an enclosing Drop method
eliminates its raw payload by ordinary source-level branches. Both execute natively; no built-in
Option representation or destructor dispatch is involved.

Owning plane members now follow the active selector. `examples/raw_union_owner.evg`
selects between `unique(usize)` and `shape(unique(usize))`, returns that union through
a checked function contract, and consumes the active member in another function.
Only the active payload grants owner authority. Virtual allocations for inactive
members do not grant owners, and only admission-free checked reachability can
justify discarding their counterfactual storage at a branch join. Actual moves
and releases still invalidate handles through the generation-checked plane store.
Allocation identities remain distinct across branch snapshots.

References to an owning union cannot move its owner out. If a union has exactly
one pointer member,
a dereference can follow it after proving that member active. This observes
the existing pointer header without transferring ownership or inventing a plane.
`examples/raw_union_borrow.evg` returns a view into the active allocation and
updates it through a declared write footprint. Its exchange contract uses
`old(**value)` to describe the pre-write value; existing aliases observe the
new value. Borrow and write ports are collected only for checked active members.
Proof subjects follow the existing pointee plane, so writes invalidate proofs
about that data while preserving independent active-type facts.

`examples/raw_union_owner_paths.evg` moves one unique owner into either of two
record members. Its combined footprint permits writes through an existing view
because both exclusive alternatives own the same allocation. Eliminating the
union releases that allocation once and invalidates the view.

`examples/raw_union_owner_drop.evg` implements an owning optional container with
constructors, a borrowed accessor, and Drop in Evergreen. Its destructor
decomposes the receiver, selects the active member using the stored flag, and
passes it to a parameter-disposal helper. The active allocation runs its payload's
destructor once; an empty container has no payload cleanup. Native compilation
orders ordinary calls together with implicit cleanup dependencies, including
helpers that themselves release owned payloads.

An existing union slot can now be initialized when its current active member is
proved to be a shape. This works for local slots, record fields, and declared
write footprints through references. `examples/slot_initialization.evg` defines
a generic source initializer for `T | shape(T)` and initializes an owning byte
pointer without creating a copy of that owner. The declared union layout stays
unchanged; aliases to the union slot observe its new active type.

The empty-member obligation is checked after evaluating the replacement. If the
right-hand side initializes the same slot first, the outer assignment cannot
overwrite its now-live payload. Each write advances the affected plane's proof
state and rechecks enclosing requirements. A past empty-slot proof cannot
authorize a second initialization. Union-write calls recheck their actual bodies
so a summary cannot replace the slot with an unrelated invented payload.

This is initialization without old-payload cleanup, not arbitrary replacement
of an initialized union. Moving a member out and leaving its shape in the slot
remains the next storage transition to implement.

Borrowed-reference members remain rejected until return-plane contracts and
conditional borrow footprints describe their provenance. Joining two different
allocations in the same member, initialized-member replacement through a borrowed
union, partial initialization of enclosing records, dynamic array member
interpretation, and generic Option remain work in progress. Member cases are
bounded and currently elaborated eagerly; deferred member constraints are also
pending. `Option`, Vec, Rc, and Arc remain ordinary library code built on the
eventual generic rules.
