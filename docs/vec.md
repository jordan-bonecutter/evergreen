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

The header contains capacity, length, and `Zero | unique(T, cap)`. Zero capacity
stores a source-defined zero word and does not allocate. The source destructor
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

Integer and Boolean instances support push, pop, get, and explicit reallocation.
Flat scalar records with an explicit Copy implementation can initialize backing
storage and transfer it using `into_data()`. Their push/pop contracts still need
a general equality interface. Free functions accept explicit type arguments,
such as `vec::push::<u8>(&values, 42)`; methods use the receiver's specialization.
Existing calls without arguments continue to use `usize`.

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
remain unfinished.

Run [vec_generic.evg](../examples/vec_generic.evg) with:

```sh
cargo run --locked --offline -- run examples/vec_generic.evg
cargo run --locked --offline -- build examples/vec_generic.evg
```
