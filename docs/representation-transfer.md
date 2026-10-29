# Representation copying and type transfer

The bootstrap now separates copying a representation from granting access to
the represented value. See [representation_transfer.evg](../examples/representation_transfer.evg).

```evg
let source: T | shape(T) = value;
let target: T | shape(T) = copy_representation(&source);
proof copied: same_representation(&source, &target) by {omega};
transfer_type(&source, &target);
```

`copy_representation` produces `shape(T)`. It neither duplicates ownership nor
grants permission to read a `T`. The source remains live. The checker stores an
opaque representation identity, not a second owning payload. The interpreter
retains an inaccessible copy of the representation; its cleanup never follows
the pointers inside that copy.

`transfer_type` requires a live source `T`, a vacant destination `shape(T)`, and
proved representation equality. Both slots currently use `T | shape(T)` storage.
The source becomes `shape(T)` and the destination becomes `T`. Ordinary plane,
borrow, write-contract, and retained-invariant checks still apply. A second
transfer from the retired source is rejected. Destructuring/eliminating the raw
unions afterward determines which value is cleaned up.

Representation identity tracks storage revisions. Copying establishes equality;
writing the source or replacing the destination does not silently preserve it.
Equal record fields alone do not establish byte equality, including padding.
The transfer preserves the established representation while moving its live
interpretation. Explicit `trustme` admissions remain part of the trust boundary.

The x86-64 backend uses its existing inline byte-copy instructions for the copy;
the type transfer emits no memory copy. No libc `memcpy` dependency is required.
Whole fixed-size owning arrays work without per-element ownership proofs.

The source-defined `arrays::relocate::<T>(source, target)` helper combines the
copy and transfer for one vacant destination slot. It works on individual
sparse heap-array elements, including owning pointers; source and destination
capacities need not match. See
[representation_array_slot.evg](../examples/representation_array_slot.evg).
Verification observes only the selected cells, not every cell in the capacity.
The helper does not yet supply the quantified frame contract needed to replace
an entire prefix relocation loop.

This is the first storage primitive, not the completed Vec relocation API.
Dynamic prefix views, independently verified byte loops, and equality assembled
from subrange copies are still unimplemented. The checker currently derives
equality from representation copies rather than reconstructing arbitrary bytes.
Bootstrap calls to helpers using these primitives recheck their bodies so their
storage identities and effects are preserved. Wasm lowering is not implemented.
Aggregate invariants continue to use the existing update/lifting rules; this
operation does not introduce transactions or synchronization for concurrent use.

As with allocation and existing moves, these are frontend memory rules. The
kernel checks the generated proof obligations; preservation by the emitted
machine code is not independently certified yet.


`arrays::relocate_last` adds a quantified frame contract around this operation:
it retires the last live source-prefix slot and extends the destination's live
interval backward by one. Both arrays retain their other initialized/vacant
regions. The implementation and all four frame proofs are Evergreen source;
there is no compiler rule for this array operation. See
[representation_range.evg](../examples/representation_range.evg), which moves
two unique owners, extracts them, and releases both vacant allocations.
The focused regression also checks certificate replay, rejects skipping a
required transfer or reading a retired slot, and compares verification obligation
counts at three-slot and billion-slot destination capacities.

`arrays::relocate_prefix` now uses the bulk forms of these generic operations.
Its caller supplies vacant destination storage:

```evg
copy_representation(&*data, &*target, length);
proof copied: same_representation(&*data, &*target, length) by {omega};
transfer_type(&*data, &*target, length);
arrays::release_empty::<T>(data);
target
```

The copy writes bytes while leaving the destination vacant. Ideal equality
compares current storage revisions and prefix length; writes invalidate prior
observations. Transfer checks that equality, source-prefix initialization,
source-suffix vacancy, destination vacancy, bounds, and disjointness. It moves
the existing payload tree once without invoking payload destructors. Enclosing
invariants are checked after both metadata updates; no source statement observes
an intermediate type state.

A sparse prefix recipe preserves source contents below the boundary and vacant
contents above it. The trusted frontend imports the operation's checked type
postcondition with its precondition/equality evidence as dependencies. Replay
checks generated arithmetic certificates; the memory-operation model remains
part of the frontend's trusted boundary, as with scalar transfer.

Native code emits one range byte copy and erases the type transfer. The reference
interpreter checks representations and updates dense debug metadata. There is no
external memcpy dependency. Proving that an independently written Evergreen
byte-copy loop establishes this same range representation relation remains
future work.
