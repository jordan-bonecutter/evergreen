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
selects between `plane(usize)` and `shape(plane(usize))`, returns that union through
a checked function contract, and consumes the active member in another function.
Only the active payload grants owner authority. Virtual allocations for inactive
members do not grant owners, and only admission-free checked reachability can
justify discarding their counterfactual storage at a branch join. Actual moves
and releases still invalidate handles through the generation-checked plane store.
Allocation identities remain distinct across branch snapshots.

Borrowed-reference members remain rejected until return-plane contracts and
conditional borrow footprints describe their provenance. References to an owning
union cannot move its owner out. Joining two different allocations in the same
member, general member replacement through a borrowed union, partial initialization
of enclosing records, dynamic array member interpretation, and generic Option
remain work in progress. Member cases are bounded and currently elaborated eagerly; deferred
member constraints are also pending. `Option`, Vec, Rc, and Arc remain ordinary
library code built on the eventual generic rules.
