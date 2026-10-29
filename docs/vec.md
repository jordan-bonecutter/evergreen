# Generic vector groundwork

[`stdlib/vec/vec.evg`](../stdlib/vec/vec.evg) defines `Vec<T = usize>` in
Evergreen. There are no compiler rules for Vec. Each used concrete instance goes
through the existing ownership, bounds, effect, and proof checks.

```evg
fn main() -> u8 {
    let values = vec::Vec::<u8>::new(2);
    values.push(7);
    values.push(42);
    values = values.reallocate(4);
    values.pop()
}
```

The header contains capacity, length, and `Null | unique(T, cap)`. Zero capacity
stores the pointer-sized `Null` scalar, whose only valid value is zero, and does
not allocate. `Null` grants no reference or allocation authority. The source destructor
releases the allocated case. Allocation bounds use `size_of(T)` from the target,
so byte vectors use byte-sized elements. Bounds, borrows, and sparse array
histories do not require expanding every capacity slot.

For now every capacity slot is initialized. `new(capacity)` uses integer zero;
`filled(capacity, initial)` copies an initializer across backing capacity while
leaving logical length zero. Boolean vectors use `filled(2, false)`, for example.
`reallocate_filled(new_capacity, initial)` provides an initializer for fresh
storage, copies the live prefix, and retains logical length. Assigning the result
over the original releases the old allocation and invalidates its element
references. Borrowed header storage remains valid across replacement.

Integer, Boolean, and reference-free Copy-record instances support push, pop,
get, and explicit reallocation. Their value contracts use ideal `same_value`,
which compares every scalar field of a record, including nested records. It
requires no runtime equality implementation and grants no Copy or ownership
permission. Constructors use explicit type arguments such as
`vec::Vec::<u8>::new(2)`; methods use the receiver's specialization. Omitting type
arguments selects the default `usize`.

`arrays::copy_range` and `arrays::fill_range` now prove exact element values and
preservation for these records as well as scalar arrays. Reallocation uses that
verified source copy routine. Its public contract preserves length and every
element of the old live prefix, and sets the requested capacity. The empty case
does not read through `Null`. Both the range and the input contents use entry
snapshots, so the specification describes the values being copied. The older
`vec::copy_prefix` API remains available for existing callers.

[`record_collections.evg`](../examples/record_collections.evg) proves record
copy/fill results and Vec push/pop results, replaces the vector twice with grown
buffers, and immediately pops and proves the original record value. Body rechecks
retain checked storage candidates, so an extra element observation is no longer
needed before the pop. Admissions are not inherited by that automatic lookup;
writes and cleanup still invalidate the affected storage facts. The native and
interpreter tests both exercise this sequence. The checker follows the copy
relations through saved proof states, observing only the requested scalar fields
of the intermediate contents. Cleanup does not erase mathematical values saved
by `old`; it still prevents reading the released allocation. Each range instance
requires its domain, original captures, and a checked proof at the saved revision.
Sparse range proofs over nested records verify at a billion-element capacity
with the same obligation and certificate counts as small arrays; tests do not
allocate the large buffer.

This is a precursor to the README's vector, not its full implementation. Repeated
initialization requires actual Copy permission; pointers with unique authority
and resource values cannot be duplicated into storage. Move-only elements still
need range initialization proofs and cleanup of exactly the initialized prefix.
Those rules must be general storage rules rather than
Vec-specific compiler behavior.

Initialization of an existing union slot and extraction into its matching shape
are now available independently of Vec; see
[slot_initialization.evg](../examples/slot_initialization.evg) and
[slot_extraction.evg](../examples/slot_extraction.evg). Sparse repeated
uninitialized storage and empty-buffer conversion are also implemented; see
[sparse-storage.md](sparse-storage.md). Typed member borrowing now retains each
slot's real plane and rechecks its active type on use. Range initialization
postconditions can now describe the known-empty result of a source allocator.
Opaque input-union range contracts can be forwarded and restricted without
materializing slots. Demanded input cells can use those range proofs
for typed member loans and checked extraction; see
[range_slots.evg](../examples/range_slots.evg) and
[range_index.evg](../examples/range_index.evg). Runtime indices require proven
equality or separation from existing observations. Conditional cell identities
remain unfinished. Range promises can also live in nominal type invariants;
[range_type.evg](../examples/range_type.evg) demonstrates a generic initialized
slot with typed borrowing and complete consumption. Vec still needs conditional
capacity observations and integration of the resource frames and prefix
cleanup described below. Generic single-slot prefix/suffix transitions now work in
[range_store.evg](../examples/range_store.evg): push initializes the boundary,
pop extracts the last owner, and explicit frame proofs preserve the untouched
ranges. These are general source-level storage operations; the existing Vec
implementation has not yet switched to that representation.
[range_drop.evg](../examples/range_drop.evg) provides source cleanup for one
initialized owning slot. Destructor loops now use the ordinary loop checker,
and iterating over a changing family of unique owners now has a resource frame
in [`range_drain.evg`](../examples/range_drain.evg). It proves a shrinking
initialized prefix and runs each payload destructor once. Shared and borrowed
payloads still need additional frame rules, and Vec has not adopted this storage.
The final buffer-release step now accepts a checked full-range shape proof,
through `arrays::release_empty::<T>(buffer)`; it does not need to observe every
vacant slot. [`range_empty.evg`](../examples/range_empty.evg) demonstrates this
step, including keeping an extracted payload alive after releasing its buffer.

The source library now also provides `arrays::relocate_prefix` for moving an
initialized prefix into a new allocation without Copy permission. See
[`range_reallocate.evg`](../examples/range_reallocate.evg). It supports growth,
shrinking, and an empty prefix; the proof establishes the returned initialized
prefix and vacant suffix, then permits releasing the emptied source. Unique-owned
payloads and records containing them are supported. Element-value preservation
contracts and external payload identity preservation across the loop are still
missing. Vec continues to use its previous Copy implementation until these
operations and the nominal invariants are integrated.

[`conditional_buffer.evg`](../examples/conditional_buffer.evg) now checks the
intended conditional storage invariant, zero-allocation empty construction,
typed element borrowing, and complete destruction of a move-only prefix.
`arrays::drain_prefix` implements that cleanup in Evergreen. The remaining
in-place mutation work must change length and slot initialization together;
[`buffer_updates.evg`](../examples/buffer_updates.evg) now performs push and pop
inside checked invariant-update blocks. Each operation transports the old prefix
and suffix proofs to the changed array revision, and restores both invariants
before closing the block. No admission or element-by-element proof expansion is
needed: capacity eight and a billion have identical obligation and certificate
counts. The example is storage groundwork, not a second public Vec API.

[`buffer_reallocation.evg`](../examples/buffer_reallocation.evg) combines source
prefix relocation with the nominal buffer type and destructor. Actual body
rechecks export the checked logical invariant of the returned record, and
destructors retain current, unadmitted storage evidence as lookup candidates.
Caller-local fact and proof names remain lexical. Reads through a returned
buffer still depend on its allocation's current revision; extracting a live
slot or reading after destruction cannot reuse an earlier range guarantee.
The public Vec migration and larger compositions of these operations remain
unfinished; nested resource-case rechecks can still hit the work budget.

Run [vec_generic.evg](../examples/vec_generic.evg) with:

```sh
cargo run --locked --offline -- run examples/vec_generic.evg
cargo run --locked --offline -- build examples/vec_generic.evg
```
