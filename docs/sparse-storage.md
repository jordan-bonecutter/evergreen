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

Range initialization proofs, typed borrowing of an active arbitrary member, and
cleanup of a dynamically initialized prefix remain unfinished. The general
move-only Vec still needs those rules. Sparse resource arrays currently separate
incompatible branch states rather than merging them into a universal range
summary. Proof and case work remain bounded by the bootstrap's general budgets.
