# Source Rc

[`stdlib/rc/rc.evg`](../stdlib/rc/rc.evg) implements sequential counted ownership
of a generic payload `T`. The allocation contains a runtime `count` and `value: T`.
Each opaque `Rc<T>` contains one ordinary `shared(Data<T>)` claim. Its checked facts
require the runtime count to equal the ideal total of live claims, and zero to
imply no claims. The compiler has no Rc counter, type rule, or release algorithm.

```evg
let first = rc::new(42);
let view = first.value();
let second = first.clone();
proof shared: first.strong_count() == 2;
drop(first);
proof unique: second.strong_count() == 1;
let answer = *view;
drop(second);
```

`clone` checks that incrementing the counter cannot overflow. Its source helper
borrows the underlying owner slot, with write permission only for the counter.
The helper has no `Rc` view from which it could use the accuracy invariant during
the two steps: incrementing the counter and duplicating the allocation claim.
It returns an opaque unpublished `Credit` whose refinement proves equality has
been restored. Publishing that credit as an `Rc` moves its claim without changing
the counter. There is no lifted invariant or runtime transaction in this path.
Caller invariants are checked at the call boundary. This is sequential reasoning;
it establishes no atomicity under concurrent interference.

The credit is an actual allocation-backed claim, not an arithmetic allowance.
Claims include hidden caller handles. `Credit<T>` stores `shared(Data<T>)`.
The standalone [`allocation_credits`](allocation-credits.md) library still
specializes its separate payload to `usize`; its wrapper is not used here.

The source `Drop` implementation consumes and completely destructures its handle.
When the count is one, it proves uniqueness, recovers the unique plane, and
deallocates it. Otherwise it decrements the runtime count and releases its claim.
Its conditional postcondition proves that the surviving count and claim total
each decreased by one. Payload preservation follows from the checked count
writes and actual heap-body rechecks; these generic contracts do not require an
equality operator on `T`.
`old(self.data)` names the original allocation identity after consuming the
handle; dereferencing it outside `old` observes the live current payload. That
observation creates no new owning claim. The final path need not write zero to
storage that is about to cease existing. Explicit `release_nonfinal` and
`release_last` remain available with their corresponding preconditions.

The checker proves the two destructor continuations in separate storage states.
This also checks a helper whose incoming Rc has an unknown number of caller
handles: final release leaves its allocation dead, while nonfinal release leaves
it live. No fictitious live allocation is created to join those states. See
[resource case proofs](resource-cases.md) for how continuations, trust dependencies,
and replay work.

The native representation is one pointer per handle or unpublished credit and
a `usize` count followed by `T` with its ordinary target size, alignment, and
padding. Runtime increments and decrements compile
from the library source. Generic lifetime-claim bookkeeping and census
observations are erased. A payload borrow adds no claim; moving a handle keeps
the allocation in place. Final release invalidates payload borrows. A borrow of
the handle's own slot expires when that handle moves.

Ordinary scope exit, `drop`, array cleanup, and cleanup while transferring a
returned owner all use this destructor. Final release runs `T`'s normal cleanup
exactly once. Nonfinal release never copies or drops `T`. Custom Drop records,
unique pointers, fixed arrays, and nested Rcs are covered by tests. Weak
references and Arc remain unfinished. Arc needs atomic resource transitions and interference
rules; this sequential library grants no concurrent access guarantee.

`Rc` and `new` retain a `usize` default. Use an explicit type argument for other
payloads:

```evg
let first = rc::new::<Resource>(Resource {tag: 42});
let second = first.clone();
let payload: &Resource = second.value();
```

Runtime payloads still require supported fixed layouts and cannot contain
borrowed references, as required by the generic allocation rules. Unsupported
instances fail during normal checking. Borrowing a unique-pointer payload cannot
move its authority out of the Rc. Final release invalidates all payload borrows.

The examples, counter-drift and overflow rejection tests, lifetime tests, and
native/interpreter comparisons use no `trustme`. The existing generic ownership
frontend and native erasure remain trusted implementation boundaries rather
than independently checked kernel theorems.

```sh
cargo run --locked --offline -- --deny-trust run examples/rc_generic.evg
cargo run --locked --offline -- --deny-trust build examples/rc_generic.evg -o /tmp/evergreen-rc
```

The example returns `42` as its process exit status and produces no output.
