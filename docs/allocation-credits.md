# Allocation-backed credits

`allocation_credits::Credit` is an opaque, move-only source type containing one
generic owning claim. Its implementation is in
[`stdlib/allocation_credits/allocation_credits.evg`](../stdlib/allocation_credits/allocation_credits.evg).
It currently specializes the payload to `usize`; type generics will remove that
specialization. The compiler recognizes no allocation-credit type or algorithm.

```evg
let first = allocation_credits::attach(alloc(42));
let view = allocation_credits::target(&first);
let second = allocation_credits::duplicate(&first);
proof shared: allocation_credits::outstanding(&first) == 2;
let sole = allocation_credits::merge(first, second);
let allocation = allocation_credits::recover(sole);
proof unchanged_plane: &*allocation == view;
```

`attach` transfers unique allocation ownership into a credit. `duplicate` creates
another real claim to that allocation. `merge` consumes two credits to the same
allocation and returns one, reducing the outstanding total by one. `recover`
requires exactly one outstanding claim and transfers it back into unique
allocation ownership. Counts include claims outside the current function.
`target` borrows the existing payload plane and adds no claim. Moving credit
records does not move the payload; freeing the allocation invalidates its views.

The source functions prove their contracts, including total-count changes and
payload identity. `old(target(&credit))` observes the entry pointer through the
opaque accessor even after the credit record is consumed. Returning that pointer
does not recreate its former owning claim. Generic lifetime operations enforce
actual token membership, allocation generation, and unique recovery; their
frontend resource rules remain part of the compiler's trusted boundary.

Native credits occupy one pointer word. `outstanding` is ideal; claim bookkeeping
and these observations are erased. No runtime reference counter is added by this
library or by the compiler. The public API cannot turn an arithmetic budget or a
borrowed pointer into allocation authority. Copy implementations, forged record
construction, merging different allocations, and recovery while shared fail.

The earlier `credits::Credit` conserves an abstract arithmetic quantity and grants
no allocation authority. This library instead carries actual lifetime claims;
it does not implement fractional splitting of those arithmetic budgets.

This library is a lifetime-capability layer without a runtime counter.
The separate [source Rc](rc.md) now combines allocation-backed credits with
checked runtime count updates and a source destructor that automatically selects
final or nonfinal release. General payload types and fractional credit splitting
still need work. Arc additionally requires atomic transitions and interference
rules.

Run the complete example with:

```sh
cargo run --locked --offline -- run examples/allocation_credits.evg
cargo run --locked --offline -- --deny-trust build examples/allocation_credits.evg -o /tmp/allocation-credits
```
