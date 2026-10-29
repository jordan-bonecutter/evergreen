# Owning Vec

[`stdlib/vec/vec.evg`](../stdlib/vec/vec.evg) defines `vec::Vec<T = usize>`
in Evergreen. Its storage, methods, destructor, and range proofs are library
code; the compiler has no Vec-specific operation.

```evg
fn main() -> usize {
    let values = vec::Vec::<usize>::new(2);
    values.push(7);
    values.push(42);
    values = values.reallocate(4);
    let answer = values.pop();
    proof preserved: answer == 42;
    answer
}
```

The opaque header has capacity, length, and
`Null | unique(T | shape(T), cap)`. Its invariants require an initialized prefix
`[0, len)` and a vacant suffix `[len, cap)`. Zero capacity uses the pointer-sized
zero value `Null` and performs no allocation. The raw union has no runtime tag.
Element size and alignment come from the target, so `u8` elements occupy one byte.

`new(capacity)` reserves vacant storage. It requires no initializer and no Copy
permission. `push(item)` transfers the value into the first vacant slot; `pop()`
transfers the last live value out and leaves a shape behind. Ordinary Copy values
work as well. The destructor consumes the header, drops the initialized prefix
in reverse order, and releases the allocation. It never drops vacant capacity.

## API

| Operation | Requirement and effect |
| --- | --- |
| `Vec::<T>::new(capacity)` | Allocation size must fit the target's addressability bound; returns length zero. |
| `values.length()`, `values.capacity()` | Return the corresponding header values. |
| `values.push(item)` | Requires spare capacity; moves `item` into the vector. |
| `values.pop()` | Requires nonzero length; returns the last value and vacates its slot. |
| `values.get(index)` | Requires `index < length`; borrows that element's actual storage. |
| `values.reallocate(capacity)` | Consumes the vector; requires positive capacity sufficient for every live element; returns fresh storage with the same length and values. |
| `values.truncate(length)` | Consumes the vector; requires positive capacity and `length <= old length`; drops the removed suffix. |
| `values.release_empty()` | Consumes a vector of length zero; releases reserved storage and returns zero capacity. |
| `values.into_storage()` | Consumes a vector with positive capacity; transfers the actual `unique(T | shape(T), cap)` allocation, with prefix/suffix guarantees. |

Capacity growth remains explicit: `push` does not allocate automatically.
Allocation may still fail at runtime; the interpreter also has a fuel budget.
There is no small fixed capacity limit in the language's vector representation.

Growth uses [`arrays::relocate_prefix`](../stdlib/arrays/prefix.evg).
Representation copying carries no ownership. A checked type transfer makes the
source slot vacant and its destination live. The source loop proves initialization
and value preservation, then releases the old allocation. Existing element
references into that released allocation become invalid. Growth also consumes
the old header, so acquire header borrows again after assigning the result.
Pushes within capacity
retain the allocation and leave earlier elements in place.

For reference-free elements, relocation uses a checked ownership-effect summary:
every incoming unique allocation is consumed and the result owns fresh storage.
The checker derives this from the function body on every return path. Callers
invalidate the old allocations and apply the verified result contract, without
replaying the relocation loop. This is a general function rule, not a Vec builtin.
Functions that can return an input allocation, accept borrowed storage, or carry
nested pointers retain actual-body checking.

`same_value` in the contracts describes logical values, not ownership or arbitrary
byte equality. Growth preserves every value in the live prefix. Ordinary reads
can recover scalar fields from that range guarantee, including reference-free
records with destructors. No runtime equality implementation is required.

`into_storage()` does not pretend vacant capacity is initialized `T` storage.
The caller takes responsibility for consuming its live prefix and releasing the
allocation. Preserve the capacity and length needed for that cleanup; the
[`owned_method_transfer`](../examples/owned_method_transfer.evg) example uses
`arrays::drain_prefix` and shows that an element borrow survives transfer of the
header's allocation authority.

## Examples and current limits

- [`vec.evg`](../examples/vec.evg): scalar growth, a checked borrowed read, and pop.
- [`vec_generic.evg`](../examples/vec_generic.evg): byte-sized storage.
- [`buffer_growth.evg`](../examples/buffer_growth.evg): owning allocation elements.
- [`buffer_record_values.evg`](../examples/buffer_record_values.evg): records with
  destructors, growth, borrowed and moved value proofs, and cleanup exactly once.
- [`buffer_release.evg`](../examples/buffer_release.evg): zero capacity, allocation,
  push/pop, and direct release of proven-empty storage.
- [`vec_local_storage.evg`](../examples/vec_local_storage.evg): a helper with a
  local Vec and a scalar contract, called repeatedly without replaying its heap
  implementation. No references or owners cross that helper's boundary.

The former Copy-only `filled` and `reallocate_filled` APIs are removed. Use `new`
and initialize live elements explicitly. `into_data` is replaced by
`into_storage`; the previous implementation's initialized spare capacity no
longer exists. The temporary `vec::Buffer` implementation is now this public Vec.
The independent Copy-array utility remains in
[`vec/copy.evg`](../stdlib/vec/copy.evg).

This is still a bootstrap implementation. Repeated populated growth and the
combined [`record_collections`](../examples/record_collections.evg) example now
verify within the unchanged work budget. Longer sequences remain subject to that
budget, particularly when nested owning pointers require actual-body checking.
Sparse resource branches use separate checked continuations when their storage
cannot be joined; growth followed by a conditional pop is supported.
`reallocate(0)` is not yet supported;
use `release_empty()` when length is zero. Pointer-bearing payload value recovery,
more general borrowed/shared payloads, and narrowing an entire initialized union
array to `unique(T, cap)` still need work. Unsupported cases are rejected rather
than granted weaker guarantees.
