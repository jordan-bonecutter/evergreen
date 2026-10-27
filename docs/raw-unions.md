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

This layer is not executable raw-union support. Verification still rejects union
and shape values until active-member evidence, initialization transitions, and
explicit elimination are connected to both execution backends. In particular,
layout compatibility must never authorize reading an inactive member, and union
injection must never synthesize ownership for an inactive pointer member.

The next layer needs ideal type observations (`typeof`), guarded member
interpretation, invalidation when a member changes, and consumption of the
active member without implicit raw-union drop. Ownership and borrowed-reference
leaves must follow the actual member; inactive alternatives carry no owner or
borrow authority. `Option`, Vec, Rc, and Arc remain ordinary library code built
on those generic rules.
