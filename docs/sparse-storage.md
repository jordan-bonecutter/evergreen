# Sparse uninitialized storage

`alloc(capacity, shape(T))` can reserve an owning array of `T | shape(T)`.
The shape marker grants no initialized values or ownership claims to copy.
The array remains move-only; reserving its slots does not give Copy permission
to T or to its union.

```evg
fn new_buffer<T>(capacity: usize) -> unique(T | shape(T), capacity)
where integer(capacity) * integer(size_of(T)) <= integer(isize::MAX) {
    alloc(capacity, shape(T))
}

fn main() -> usize {
    let buffer = new_buffer::<unique(usize)>(8);
    (*buffer)[7] = alloc(42);
    let value: unique(usize) = (*buffer)[7];
    let empty: unique(shape(unique(usize)), 8) = buffer;
    drop(empty);
    *value
}
```

The checker keeps one immutable empty default and only demanded cells. Writes
create new contents versions while retaining the sparse cell map, so entry
snapshots through `old()` retain their earlier contents. Capacity does not
enumerate elements. A billion-slot version of this example checks, compiles,
and replays its certificate without materializing a billion values.

Each cell represents one actual location. Forming a place compares its index
with the already materialized indices. Equal indices reuse the same cell;
distinct indices can demand a new one. Unresolved equality uses the existing
resource-continuation checks to validate both cases. Separate maps are retained
for alternatives whose alias or initialization states differ. Read observations
cannot create independent owners for potentially identical slots.

Initialization requires the slot's current shape and an authorized write.
Extraction requires a current active-member proof and leaves its matching shape.
Ordinary Copy reads retain the initialized slot; explicit `move` extracts Copy
members too. Overwriting a live member, double extraction, and using an old
empty-slot proof after an aliased write are rejected.

The typed assignment to `unique(shape(T), capacity)` closes an emptied buffer.
The checker requires genuine unique authority, unchanged extent, unchanged
element size and alignment, and admission-free evidence that every tracked cell
has that shape. The remaining range must have an empty default or complete
observed coverage. Explicit literal elements can provide complete coverage;
zero length follows from the same coverage rule. A live member cannot disappear
through the conversion, including by an incorrect `trustme` claim.

This assignment preserves storage identity and advances its proof state.
Existing slot references can observe their current shapes. Ordinary cleanup of
the shape array then releases the allocation without visiting its capacity.
Freeing the allocation invalidates slot references. References into a separately
allocated payload remain usable while the extracted owner keeps it alive.

Native shape allocation reserves the mapping without a repeated element-fill
loop. Native extraction and the emptied-buffer conversion need no tags or
additional runtime metadata. The reference evaluator independently checks actual
cell states; it still stores runtime cells and rejects allocations exceeding its
execution fuel before reserving host storage. That execution limit is separate
from the sparse proof representation.

Run [sparse_slots.evg](../examples/sparse_slots.evg),
[sparse_slot_aliases.evg](../examples/sparse_slot_aliases.evg), or
[sparse_rc_slots.evg](../examples/sparse_rc_slots.evg). The Rc example combines
ordinary generic storage with the source library's ownership and destructor
protocol; the compiler has no Rc-specific storage rule.

Source universal proofs can now describe slot types over integer ranges:

```evg
proof empty: forall(i: integer) where (0 <= i && i < 8) {
    typeof((*buffer)[i]) == shape(unique(usize))
} by {intro i; omega};
```

The checker builds a selector definition on demand from the immutable empty
default and sparse exceptions. Its arguments retain every free integer involved
in the index and selectors. It creates no element views or owner claims. Bounds
are separate well-formedness obligations under the quantified domain, including
for `!=` queries. Balanced Boolean formulas describe the exceptions; capacity is
not enumerated. A billion-slot version uses the same number of obligations and
certificates as the eight-slot example.

[sparse_ranges.evg](../examples/sparse_ranges.evg) proves the initial empty range,
an empty suffix after initializing one slot, and the complete empty range after
extraction. Alias stores advance the same array's contents identity. An old
theorem cannot describe the changed buffer. These proofs erase completely in
native code. The selector's correspondence to storage is checked by the frontend;
the kernel checks definitions and arithmetic, rather than a complete memory model.

An active slot also supports a contextual member borrow:

```evg
fn as_ref<T>(slot: &(T | shape(T))) -> &T
where typeof(*slot) == T
borrows(slot) {
    slot
}
```

The returned reference retains the slot's plane and generation. Its checked
interpretation names the member type; it creates no payload copy or ownership
claim. Every read, projected address, and write requires that member to be active
at the time of use. Writes recheck after evaluating the right-hand side. Mutating
through a member view expires facts about the overlapping union slot.

Extraction makes the slot view dormant. Keeping that reference is allowed;
reading it while the slot is a shape is rejected. Reinitializing the same slot
with the same member makes it readable again, using the new contents and facts.
An empty-buffer conversion can erase the union interpretation altogether; such
an old member view remains dormant and cannot read the narrowed shape array.

[member_borrows.evg](../examples/member_borrows.evg) demonstrates the difference
between a view of an owning slot and a view into the separate allocation it
owns. Extraction invalidates the former. The latter remains readable after
freeing the buffer, until the extracted payload owner is released. Moving a
non-Copy owner out through a typed member reference remains rejected; extraction
uses the raw union slot and its checked shape transition.

Resource range loop frames, unknown input-union selector summaries, and cleanup
of a dynamically initialized prefix remain unfinished. The general move-only
Vec still needs those rules.
Sparse resource arrays currently separate
incompatible branch states rather than merging them into a universal range
summary. Proof and case work remain bounded by the bootstrap's general budgets.
