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
copy/fill results and Vec push/pop results, replaces the vector with its grown
buffer, and immediately pops and proves the original record value. Body rechecks
retain checked storage candidates, so an extra element observation is no longer
needed before the pop. Admissions are not inherited by that automatic lookup;
writes and cleanup still invalidate the affected storage facts. The native and
interpreter tests both exercise this sequence. Repeated growth without observing
the intermediate buffer still needs composition of historical range relations.
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
equality or separation from existing observations. Conditional cell identities,
resource range loop frames, and cleanup of a dynamically initialized prefix
remain unfinished. Range promises can also live in nominal type invariants;
[range_type.evg](../examples/range_type.evg) demonstrates a generic initialized
slot with typed borrowing and complete consumption. Vec still needs conditional
capacity observations, resource loop frames, and destruction of exactly its
initialized prefix. Generic single-slot prefix/suffix transitions now work in
[range_store.evg](../examples/range_store.evg): push initializes the boundary,
pop extracts the last owner, and explicit frame proofs preserve the untouched
ranges. These are general source-level storage operations; the existing Vec
implementation has not yet switched to that representation.
[range_drop.evg](../examples/range_drop.evg) provides source cleanup for one
initialized owning slot. Destructor loops now use the ordinary loop checker,
but iterating over a changing family of owners still needs a resource frame.

Run [vec_generic.evg](../examples/vec_generic.evg) with:

```sh
cargo run --locked --offline -- run examples/vec_generic.evg
cargo run --locked --offline -- build examples/vec_generic.evg
```
