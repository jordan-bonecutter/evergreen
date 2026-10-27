# Evergreen bootstrap

Build with `cargo build`. The executable is `target/debug/evg`.
The CLI uses Clap and proof artifact fingerprints use `sha2`. The arithmetic
kernel and evaluator use the Rust standard library. `evg --help` describes
available commands.

```sh
cargo run -- emit examples/lean_reference.evg
cargo run -- check examples/contracts.evg
cargo run -- run examples/contracts.evg
```

`check` and `run` use the internal certificate checker and need no external
tools or downloads. `run` checks every declaration before evaluating `main`.
The optional `lean-check` and `lean-run` commands use the Lean version in
`lean-toolchain`; set `EVG_LEAN` to its executable if necessary. `emit` prints
Lean source without claiming verification. The Lean frontend currently covers
nonrecursive mathematical ideal functions and vectors. `lean-run` evaluates a
ideal reference model inside Lean; it is not Evergreen runtime execution.

The supported language contains typed functions, local `let` bindings,
named `fact` declarations, preconditions (`where`), postconditions (`ensures`),
length-indexed arrays (`[T; n]`), array literals, calls to earlier verified
functions, and conditional expressions. Conditionals can select scalar values,
unit, or records with scalar fields, including nested records. Their checked
relations preserve which branch supplied each result field. Matching array
layouts and scalar-array references within one plane also support guarded joins,
as described below. See `examples/conditional_records.evg`.
Array access requires a proof of its bound.
A semicolon discards an expression and cleans up its temporary, including at the
end of a function. A returned tail expression has no semicolon.
Nominal structs support dependent fields and `where` invariants. Construction
and field assignments must establish those invariants. `update(place, ...) lifts
fact_name, ... { ... }` explicitly opens selected named requirements on struct
plane roots, including `*owner` and `*borrowed_record`. Other requirements remain checked at every write. Type-local
facts are declared inside `where (fact name = proposition; name && ...)` and
can be referenced as `place::name` in proof code. Merely declaring a type fact
does not require it to hold: only the final `where` proposition imposes a
constraint. Lifted names must be declared facts used as independent conjuncts
of that constraint. `Type::name` can qualify a lifted selector. Its body allows
checked scalar writes, local scalar values/borrows, and pure facts; each
invariant must hold again on exit. Runtime calls require an inferred scalar
ownership-free effect summary: total execution, scalar values or scalar-reference
interfaces, no allocation or cleanup effects, and no access to a whole refined
object. Summaries compose through previously checked helpers.
`examples/update_helpers.evg` demonstrates
this distinction: `&pair.left` and a read-only scalar helper work while `&pair`
and a whole-object observer cannot rely on the open invariant. Unknown runtime
effects, runtime allocation and ownership transfers, early exits, and suspension
remain rejected. Borrow locals are scoped to the update. Runtime owning fields
cannot be replaced. Opening
an invariant does not destroy the object or relinquish its initialized fields.
The update erases to ordinary stores, not a hardware transaction; concurrency
will require separate visibility permissions. Outside this construct, assigning
a value that violates its nominal type is rejected immediately. Postconditions refer to
the entry values of parameters, even when the function reassigns its locals.
Unknown obligations fail verification. A `fact name = proposition;` declaration
names a proposition and may be false. It does not introduce an assumption.
`proof witness: proposition by { ... };` must establish that proposition before
its witness can be used. Preconditions are explicit assumptions in a universally
quantified function contract and become obligations at calls.

```evg
fn increment(n: usize) -> usize where (n < usize::MAX) ensures (result > n) {
    fact grows = n + 1 > n;
    proof successor_grows: grows by { omega };
    n + 1
} proof { omega }
```

Proof scripts support `intro hypothesis`, `apply proof_name`, `constructor`,
`left`, `right`, `cases`, `assumption`, and `exact proof_name`. Separate steps with
semicolons. `intro` opens an implication (or negation) and makes its premise a
local checked hypothesis; that hypothesis and its path assumptions leave scope
when the subgoal closes. `apply` uses a checked implication and creates its
premise goals in declaration order, including curried implications. It can also
apply a checked negation to prove false. `constructor` proves both conjuncts;
`left` and `right` select a disjunct. `assumption` finds a matching named checked
proof or introduced hypothesis; it does not invoke arithmetic search or treat a
raw fact as a proof. `exact` requires the same normalized proposition, rather
than merely another true statement.

`cases h with first | second` requires a checked disjunction and creates two
proof goals. The first branch assumes only its first alternative; the second
starts again from the original context and assumes only its second alternative.
`cases h with first, second` requires a checked conjunction and provides both
conjuncts for one subproof. These names leave scope when their subproof ends;
the original proof `h` remains available. Separate branches may reuse the same
name, but the two names of a conjunction must differ. `cases impossible` closes
a goal only when `impossible` is a checked proof of false. These operations
inspect logical proofs; they do not destructure runtime data or move resources.

```evergreen
proof combined: a => b => (a && b) by {
    intro first;
    intro second;
    constructor;
    exact first;
    exact second
};
```

The default is `omega`. The automation names `omega`, `rfl`, `simp_all`, and
`decide` currently all use the bounded arithmetic certificate procedure in the
internal backend; they do not implement Lean's individual automation strategies.
Scripts must finish every generated goal and consume every supplied step.
Unknown steps, escaped hypotheses, raw facts passed to `apply`, and incomplete
scripts are rejected. `examples/reject_proof_scope.evg` fails in both backends
because an introduced hypothesis leaves scope before the next conjunct.
Scripts have at most 1024 steps in either backend. The internal verifier also
bounds goal nesting to depth 64 and charges saved branch contexts against its
symbolic work limit. `examples/propositional_proofs.evg`
checks implication composition and logical introduction rules, runs, replays,
and builds natively. `examples/lean_propositional.evg` checks the corresponding
scripts with Lean's own tactics through the optional reference backend.
`examples/proof_cases.evg` exercises conjunction and disjunction elimination,
including repeated names in separate branches; it runs, replays, and builds.
`examples/lean_proof_cases.evg` checks these scripts in Lean. The invalid
`examples/reject_case_scope.evg` is rejected by both backends for using one
case's hypothesis in the other case.
Arbitrary Lean source and unproven axioms are not accepted. Lean warnings are
errors; `sorry` is unavailable. Explicit audited `trustme` is described below. A fact name denotes its
proposition in proof code, never a runtime boolean. Local fact definitions are
re-evaluated against the current places; an old witness cannot certify a changed
state. `examples/named_facts.evg` includes an unused false fact and actual proof
reuse; `examples/reject_false_proof.evg` rejects a false proof. Exported and
parameterized proposition declarations are not implemented yet. Type-local
named propositions and their instance references are supported.

The bootstrap target is 64-bit: `usize` is `u64`, and `isize` is `i64`.
Explicit `u8`, `u16`, `u32`, `u64`, `i8`, `i16`, `i32`, and `i64` types are
supported. Every machine arithmetic result must be proved within its type's
bounds. There is no implicit wrapping. `T::MIN` and `T::MAX` denote bounds.
For example, `fn increment(n: usize) -> usize { n + 1 }` is rejected; adding
`where (n < usize::MAX)` supplies the required proof assumption. Negating a
signed minimum is rejected as well.

`int` and `nat` are proof-only mathematical integers and naturals. They may occur
in `ideal fn` and `ideal type` definitions and proof expressions, but cannot be
stored in executable variables, structs, or function interfaces. Ideal functions
cannot be called by runtime expressions; all fact/proof declarations and
contracts are erased. `nat(value)` and `int(value)` provide mathematical views
in proof code; the natural view requires nonnegativity. Entry conditions of
`main` are proved before execution, so ideal predicates are never run by the
runtime. Unannotated runtime integer literals default to `isize`.
Natural subtraction saturates at zero. Logical operators in propositions
are `&&`, `||`, and `!`. Array indices and lengths must be proved nonnegative,
including when a signed index is used. The optional Lean frontend supports
`int` and `nat` but does not yet lower machine arithmetic.

References use `&place`, dereference uses `*reference`, and reference types use
`&T`. Multiple mutable aliases are allowed. Scalar writes preserve identity and
are visible through all aliases. Overwriting an array or struct in place also
preserves references when its storage layout stays the same. A layout-changing
replacement, `move(place)`, or `drop(place)` invalidates references to the plane.
Reassignment restores a moved
slot without restoring old references. References into structs and known array
elements are supported. Records move by default when used as values, including
assignment, arguments, and return values. `impl Copy for T {}` explicitly enables
implicit copying when every field is Copy and the type has no Drop implementation.
Machine/mathematical scalars, Booleans, unit, ordinary borrowed references, and
arrays of Copy elements are Copy. Owning planes are not. A moved source slot
becomes `shape(T)` and cannot be read.
Assignments restore that slot. Overwriting a live owner runs its destructor;
scope cleanup runs in reverse binding order, with owned fields cleaned after
the parent destructor. Partial moves and overwriting owners through borrowed
references remain rejected when runtime cleanup/ownership effects are required.

```evg
impl Drop for Resource {
    fn drop(self) {
        fact valid_tag = self.tag == 7;
        proof valid_at_destruction: valid_tag;
    }
}
```

Destructors are checked against every value of their receiver type and cannot
add preconditions. They permit scalar work, borrows, facts, and calls with a
checked scalar ownership-free effect summary. This summary is inferred from
the verified body and its callees: it requires total execution, a scalar/reference
interface, and no creation, transfer, or cleanup of runtime ownership. It is not
a programmer-supplied marker. These helpers may write through their explicit
`modifies` contracts and are also usable in selective invariant updates.

A destructor can pass its own scalar fields to modifying helpers, and can declare
external writes with `modifies(self.target)` or another incoming reference path.
Every explicit drop, discarded temporary, scope exit, and replacement checks
that the caller owns the target or has matching write permission. A function
consuming such an owner must include its cleanup writes in its own effect
contract. The ordinary alias checks, plane validity, and nominal invariants still
apply. Returning from a function preserves the value computed before cleanup,
even when cleanup changes referenced storage.

Effectful cleanup bodies are elaborated against the actual receiver. Child
cleanup uses fields left by the parent body, follows declaration order, and must
fit the parent's declared effects. Local scope cleanup runs in reverse binding
order; expression temporaries clean up in reverse creation order. Proof bundles
include the resulting conditions. This bootstrap currently rechecks effectful
bodies at cleanup sites; it does not yet have reusable summaries of final receiver
state. Their helper callees must be verified before the consuming function. Opaque arrays with effectful element cleanup require element summaries and
are rejected; known array values are supported.

Receiver invariants must remain valid while the receiver exists. A destructor
can now consume its entire `self` with a complete record pattern, moving every
field into a local. The consumed receiver becomes inaccessible; those locals
receive normal reverse-binding-order cleanup instead of a second parent Drop.
After decomposition, complete local bindings can be moved or explicitly dropped;
ordinary ownership, liveness, and effect checks still apply. `drop(self)` and
moving the receiver directly remain rejected. Record construction, other
destructuring, and ownership-carrying helper calls remain unsupported in Drop
bodies. The invariant-update rules are unchanged. `Drop` postconditions
use entry parameter bindings like other functions: `*self.target` follows that
entry pointer into current memory, while `old(*self.target)` reads entry memory.
`examples/drop_effects.evg` checks caller effects and saved return values;
`examples/drop_children.evg` checks final child fields. These are generic cleanup
examples, not an RC ownership or allocation implementation.

`evg run stdlib/counter.evg examples/drop_count.evg` demonstrates the type boundary:
the parent's invariant requires a positive count while its body runs; after the
parent is consumed, a field destructor can release the final count to zero. The
same write in the live parent's body is rejected. This checks a sequential count
transition, not a correspondence between counters and actual allocation owners.

`evg run stdlib/counter.evg examples/drop_helpers.evg` checks scalar cleanup
helpers and read-only observations. The native backend compiles these helpers
before dependent destructors. `examples/drop.evg` checks a refined parent that
owns a resource with its own destructor. The debug API `run_with_events()` returns
a detached result snapshot and destructor trace.

The initial implementation conservatively treats an aggregate's storage as one
plane, so replacing a nested aggregate may invalidate unrelated references in
the same root. Partial moves remain unsupported. Scalar array references support proved
symbolic indices, including aliasing as described below.
Reference returns require the exact alias contracts described below. Scalar writes
require the explicit contracts described below.

Assignments check record invariants against the resulting symbolic store. A
stored reference can point back into the record being assigned, so checking the
proposed fields against the old memory would read the wrong value. Both ordinary
field writes and writes through borrows install the new store before validating
the enclosing record; an invalid result rejects the assignment immediately.
The same rule applies to nested records and known record-array elements.
`examples/self_observing_fields.evg` preserves an equality between a field and
the value read through its stored pointer, including a helper checked against
actual overlapping inputs. `examples/reject_self_observing_write.evg` rejects
the first zero store through a self-observing positive view, before a later
helper could restore it. The valid example runs, builds, and replays internally.

Ideal recursion requires `decreases (measure)` after the postcondition. Runtime
recursion may omit it, in which case safety and return contracts are checked
without a termination claim. A supplied measure must be an integer proved
nonnegative; every recursive call must prove that its value
is strictly smaller than the entry measure. The callee contract is available
only under this well-founded induction rule. Recursive calls in specifications
are rejected. Mutual recursion is not implemented yet.

Not yet supported: non-record patterns, shared heap ownership, general C FFI, foreign aggregate
layouts. Unsupported syntax
is rejected. No memory safety claim is made for these unimplemented features.

Unique heap ownership uses `plane(T)` and `alloc(value)`. An owner is affine and
owns a separately allocated, stable data plane. Moving the owner invalidates its
old binding but preserves borrows of the data. `*owner` reads its payload;
`&*owner` borrows it. Dropping an owner or replacing it runs payload cleanup and
frees the allocation. Old data borrows become `never`; a later allocation or
owner restoration cannot revive them. A borrow of the owner *slot* observes a
same-layout replacement of that slot and then refers to its new owner value.

Payloads currently require fixed runtime layouts and cannot contain borrowed
references, including erased borrowed fields. Nested owned planes, fixed arrays,
runtime records, and reference-free proof fields are supported. Owning payload
fields remain subject to the existing complete-pattern and partial-move rules.
`&plane(T)` borrows an owner without receiving its allocation authority. A
function writing through it declares a footprint such as `modifies(&**owner)`;
it cannot move or drop the borrowed owner. Calls involving owned-plane types
recheck the actual body and memory, preserving transfers and frees across the
call boundary. This is conservative execution, not a reusable allocation-effect
summary; recursive heap programs may hit verifier limits. Conditional selection
of different allocation identities remains unsupported. Heap record invariants
can be opened with `update(*owner) lifts fact { ... }`. A borrowed record can use
`update(*record)` with ordinary matching `modifies` footprints for its writes.
The update target is a structural storage observation, resolved once before
opening, and must denote a whole record plane. A plane can be opened only once,
even through differently named aliases. Nested inline record projections and
record-array cells still need subplane invariant tracking.

Open requirements are tracked by physical plane identity, including through
owner fields and borrowed owner handles. Dormant containers are checked against
retained requirements without making lifted facts available to observations.
Passing a whole broken record to an observer still fails full type validation.
Helper writes recheck retained requirements at each actual store. The update
exit validates each originally opened plane with all its requirements restored.
`examples/heap_updates.evg` combines borrowed updates, a heap owner carried in a
record, erased numeric bookkeeping, and owner-first release ordering. This is
still a numeric protocol, not authority over a shared allocation or an Rc type.
`examples/reject_heap_update_intermediate.evg` rejects a helper that stores zero
before restoring the count, breaking the retained zero-is-safe requirement.

Allocation and ownership transfer require runtime execution with closed
invariants. Proof calls observe heap owners through borrowed interfaces; they
cannot take owners or produce owning results. Ideal code cannot allocate, hide,
or consume an owner. Interpreter allocation uses the generation-checked store.
Native allocation uses anonymous private Linux `mmap` and `munmap`. Allocation
failure or a failed release exits with status 126 rather than returning a
language value. There is no fixed native heap quota. The private word ABI gives
each owner an eight-byte home. Inline layouts retain a 64 KiB compiler limit;
filled heap arrays instead prove that their byte size fits `isize::MAX`. These allocator/backend rules remain trusted
implementation code. The Lean owner-slot model separately proves that an owner
move preserves payload references and a free invalidates them; it does not prove
affine enforcement, the allocator, or compilation correctness.

`examples/owned_planes.evg` runs, builds, and replays with stable data borrows,
borrowed write contracts, entry payload snapshots via `old(*owner)`, owner-slot
replacement, and nested payload cleanup.
The `reject_heap_*` examples reject duplicates, use after free, and undeclared
borrowed writes. This primitive is unique allocation ownership, not Rc or Arc:
shared ownership authority and atomic state transitions still need language
support and library implementations.
The [shared ownership implementation obligations](shared-ownership.md) describe
the missing allocation capabilities and concurrency contracts.
`proofs/SharedOwnership.lean` now checks an identity-based per-allocation ledger:
all finite modeled interleavings preserve accounting and unique token IDs,
pending tokens prevent reclamation, and only the final decrement grants the
single-use reclamation phase. This is a protocol specification, not verified
Evergreen Rc/Arc code or a weak-memory proof.

`src/shared/planes.rs` provides the internal generation-checked plane store used by
both verification and execution. Arena identities prevent handles from crossing
stores. Allocation has a 100,000-plane limit. `proofs/Planes.lean` separately
specifies plane identity, epochs, invalidation,
aliasing, and publication of invariant-carrying states. The Lean model is not a
proof of the Rust implementation. It does not yet model descendant planes,
pointer provenance, concurrent access, or physical storage reuse.

## Validation

```sh
cargo test
cargo clippy --all-targets -- -D warnings
EVG_LEAN=/path/to/lean cargo test --test verification -- --ignored
cargo test --lib symbolic_array_entries_each_reject_a_wrong_contract -- --ignored
```

The external integration suite checks valid programs, false contracts,
unproven array accesses, and the plane specification. Missing Lean is an error,
never a successful verification.

An independent two-cell Rust array model checks 64 combinations of writes,
conditional updates, early or late borrows, and overlapping helper arguments.
Each case must prove, execute with the model's result, replay its certificate
without search, and reject a wrong result contract. `examples/array_model.evg`
also checks a symbolic helper universally and observes its sixteen input
combinations in both execution backends. The optional exhaustive audit above
checks wrong entry contracts separately for those sixteen symbolic calls.
These finite checks are regression evidence, not a compiler correctness proof.

## Direction

The internal pipeline is syntax → symbolic elaboration → verification
conditions → certificate search → independent certificate checking. The small
checker in `src/compiler/kernel.rs` accepts nonnegative weighted sums of integer linear
inequalities that establish a contradiction. Proof search uses bounded
Fourier–Motzkin elimination. Search failure, overflow, and resource limits all
fail verification. Integer strict inequalities are normalized with a unit gap.
The solver is incomplete for general integer arithmetic and rejects nonlinear
products of symbolic values. Boolean conditions retain at most 64 paths. When an expansion exceeds that
limit, the verifier deduplicates conjunctions with exactly the same rows,
ignoring order and repetitions only in the comparison key. It retains the first
path's original rows for certificate indexing. If necessary it then probes the
remaining paths and discards only contradictions accepted by the independent
kernel. Solver misses remain live, and more than 64 surviving paths still fail.
This overflow work uses the common symbolic-work and query budgets;
search is limited to 2,048 constraints and 64 elimination steps.

The parser, type elaborator, condition generator, certificate checker, evaluator,
and native backend remain trusted Rust code. The kernel is not a full dependent type
theory yet. There is no theorem of compiler correctness. Arithmetic is
mathematical in verification; the reference evaluator uses checked i128 and
reports an error for values beyond its range. It never wraps silently.
The interpreter has a 100,000-unit expression/value-work budget, a 128-call depth
limit, and a combined
expression-depth limit of 256. It uses one worker with a bounded 16 MiB stack
so these diagnostics do not depend on the calling thread’s stack size.

Lean remains an optional reference backend and specification tool. The intent
is to grow the internal proof language toward dependent types and explicit
derivations while keeping search outside the kernel.

## RC proof experiment

`cargo run -- check proofs/rc_protocol.evg` verifies a shared ideal count
protocol for RC and ARC: reserve, publish, retire, decrement, retain, and release.
Each complete ideal transition preserves `count == owners + credits` and the
target's maximum-count bound, without lifting. Zero count implies zero owners
and credits. The physical implementation must still prove that its ordinary
store (RC) or atomic operation (ARC) realizes the corresponding ideal transition.
There are no RC intrinsics or special type names in the compiler.

`cargo run -- check proofs/rc_protocol.evg proofs/arc_interleavings.evg` also
checks count-level interleavings, including releasing the old owner before a
reserved clone is published, and the equality needed on successful CAS. The
stale check in `proofs/reject_arc_stale_check.evg` fails. `check` accepts ordered
source units; definitions from an earlier unit are available to later units.

This is a protocol model, not an RC library implementation or a memory-safety
theorem. Its owners and credits are mathematical numbers, not unforgeable
capabilities. Connecting that arithmetic to unique ownership witnesses,
physical heap steps, borrowing, and destruction is still necessary. The
compiler must provide general rules for those concepts rather than RC policy.
The unbalanced transition in `proofs/reject_rc_unbalanced.evg` and reusing a single
credit twice both fail verification. Ideal erasure and restricting mathematical
types to proof code are implemented with explicit ideal declarations. Connecting
the model to linear capabilities and physical heap ownership remains planned.

## Explicit trusted assumptions

`proof assumed: proposition by { trustme };` accepts any proposition without
proving it, including false ones. This is the explicit boundary for assumptions
such as an external function's contract. A false trusted assumption can
invalidate every subsequent safety conclusion. It does not construct runtime
values or implement general foreign linking. Explicit trusted syscall declarations
provide the native OS boundary described below. Named facts alone still introduce
no assumptions.

The checker reports each `trustme` location and labels the result as checked
with trusted assumptions instead of verified. `--deny-trust` rejects the whole
source unit if any such assumption occurs, including in a called helper.
The optional Lean reference emitter rejects `trustme` rather than emitting
an implicit admission.

## Replayable proof artifacts

```sh
cargo run -- prove proofs/rc_protocol.evg -o proofs/rc_protocol.evgproof
cargo run -- --deny-trust check proofs/rc_protocol.evg --proof proofs/rc_protocol.evgproof
```

Artifacts can be committed alongside their source. Replay regenerates types and
verification conditions, then checks arithmetic certificates with the internal
kernel without invoking arithmetic search. Source content, model version, query
digests, and explicit trusted assumptions must match; invalid or missing evidence
fails without a search fallback. SHA-256 from `sha2` supplies fingerprints;
fingerprints do not replace checking the certificates. Artifact size, query count,
and checking work are bounded. Output is replaced only after successful checking,
and the CLI refuses to overwrite an input source file.

This first cache still checks all source and regenerates its conditions. It is
not separate compilation of library interfaces, a zero-knowledge proof, or a
proof of generated machine code. Avoiding repeated frontend work for standard
libraries will require checked module interfaces and their dependency manifests.

## Affine values without destructors

All records, including ideal records, are move-only unless they explicitly
implement Copy. `affine type Permit struct {tag: usize}` additionally declares
that Copy must not be implemented, without requiring `impl Drop`.
`ideal affine type Ticket struct {tag: nat}` applies that restriction to proof data. Passing or assigning such a value
moves it and leaves the old binding as `shape(T)`. Enclosing records and arrays
are affine too. Scalar field inspection borrows the existing storage; moving
individual owned fields still requires partial-initialization support.
Values may be discarded, so this is affine rather than linear ownership.
Types with destructors are non-Copy automatically. Move-only classification
is independent of runtime destruction: a non-Copy record of scalars or borrowed
references can have no destructor work at all. Its fields may still be borrowed
and inspected without copying or moving the containing record.

See `examples/affine_values.evg`. This supplies a general prerequisite for
reservation witnesses without RC-specific compiler rules. It does not make
constructors private or establish that every ticket represents a real atomic
reservation: anyone in the current compilation unit can construct a ticket.
Module visibility, fresh resource identities, and a checked link between
physical transitions and ideal witnesses remain necessary.

## Complete record patterns

`let Pair {left: first, right: second} = pair;` binds every field, with shorthand
`let Pair {left, right} = pair;` when names match. An affine source is consumed
as a whole and becomes `shape(Pair)`; each field then has its own binding and
cleanup. Missing fields, repeated fields, repeated binding names, and using the
consumed parent are rejected. Pattern bindings clean up in reverse binding order.
This supports transferring owned fields without partially initialized records.

Destructuring a type with its own `Drop` implementation is rejected outside its
own destructor because it would bypass that destructor. Inside that destructor,
`let Resource {data, child} = self;` is allowed when it binds every field once.
The parent method is already running; consuming `self` prevents a second parent
cleanup, and its fields become ordinary locals with their own cleanup. References
into an owned allocation survive the pointer move; references to receiver slots
become invalid. Tests check child cleanup once and retained effect obligations.
Fields with their own destructors are also supported when the parent has none. Patterns inside
open invariant updates, nested patterns, and wildcard patterns remain unsupported.
See `examples/destructure.evg`.

`proofs/affine_credits.evg` combines the rules: split a weighted affine credit,
destructure the result, join it again, and prove conservation. Checking it with
`proofs/reject_duplicate_credit.evg` rejects a second use of the consumed input.
The example proves conservation through its functions and prevents copying their
inputs. Its public constructors remain forgeable; these credits do not yet
carry authority over a physical allocation or atomic counter.

## Scalar write contracts

```evg
fn increment(r: &usize) -> ()
where (*r < usize::MAX)
modifies(r)
ensures (*r == old(*r) + 1) {
    *r = *r + 1;
}
```

`modifies(r)` grants permission to change the scalar reached through `r`.
`old(*r)` is its entry-state value, and `old(n)` captures an entry parameter.
These snapshots are proof-only. At a call, the checker proves the precondition,
replaces the target with a fresh symbolic value, and uses the checked
postcondition to constrain that value. Other storage is preserved, aliases
observe the updated target, and enclosing record invariants must still hold.
A wrapper must declare its own permission before forwarding a borrowed target
to a modifying helper. `examples/write_contracts.evg` checks composition,
aliases, overflow bounds, and preservation of an unrelated sibling field.

`old` also accepts entry-state field, dereference, and indexed projections, plus
checked scalar arithmetic, comparisons, Boolean predicates, and conditionals:
`old((*pair).left)`, `old(*handle.count)`, or
`old((*data)[if flag {0} else {1}])`. All names and dereferences inside the expression use the
function's entry bindings and memory. Only functions that use these compound
forms capture an entry store; the snapshot is proof-only and its copying work
counts against the verifier's limits. Reads are checked when used, so a branch
can establish the bound for an old indexed read. Local bindings introduced after
entry, effectful calls, and runtime uses of `old` are rejected. Snapshots do not
recreate consumed ownership.

Total scalar functions without write effects can be called inside `old`, such
as `old(credits::units(credit))` for an incoming reference to an opaque credit.
Arguments and accessor preconditions are checked against entry storage, and
the call retains the defining module's representation access. This permits
public conservation contracts without revealing private fields. Calls returning
references or aggregates, potentially divergent calls, and address construction
inside entry expressions remain unsupported. `examples/old_accessors.evg`
checks both numeric and Boolean accessors against a changed live pointee.

`old((*data)[index])` uses the entry index; an index outside `old`, as in
`old(*data)[index]`, uses the surrounding proof's binding. References remain
reference values: `old(handle.count)` snapshots the pointer, while
`old(*handle.count)` snapshots its pointee's value. A dereference outside `old`
uses live memory and the ordinary generation checks. `examples/old_places.evg`
exercises nested snapshots, rebinding a pointer field, and preserving a caller's
entry state across multiple modifying calls. `examples/old_selection.evg`
changes both an array and its selector, then proves that a conditional snapshot
still reads the entry array using the entry selector. Address construction and
user function calls remain forbidden inside snapshots. Existing reference
values retain their incoming handles; a newly selected symbolic path gets a
separate live view when needed, without reviving a stale generation.

Write contracts can name scalar projections of incoming references, such as
`modifies(&(*data)[index])` or `modifies(&(*pair).left)`. Bounds and the
projection are checked under the entry precondition. Permission stays attached
to that entry place if an index variable later changes; sibling cells remain
unchanged. Targets support machine scalars, Booleans, copyable scalar-field
records, and arrays of these values.

`modifies(data)` for an incoming scalar-array reference grants permission to
write its cells or replace its contents with the same array layout. The call
summary forgets the entire region's contents, then assumes its checked
postcondition. Only memory outside the region is automatically preserved; a
helper promising a smaller change should declare a projected footprint instead.
Existing element references keep their storage identity and read the new
contents, including symbolic indices and references created before the call.
`old(*data)[index]` reads from the entry snapshot.

Several projections from the same input reference form a union of permissions.
They may coincide; listing the same place twice grants no additional authority.
`modifies(&(*data)[left], &(*data)[right])` therefore supports both equal and
distinct indices while framing all other cells. Separate reference parameters
use independent body models for modular summaries; overlapping calls instead
recheck the body against actual shared storage, as described below.

`stdlib/arrays/array.evg` provides `arrays::set`, `arrays::swap`, and
`arrays::replace_pair` in Evergreen. `swap` accepts equal indices because both
places share one incoming array's alias model. Run the example with
`evg run stdlib/arrays/array.evg examples/array_updates.evg`; the same ordered unit
supports certificate replay and native compilation.

Write contracts support references stored in record parameters and behind other
references, including `modifies(view.count)`, `modifies((*view).counter.count)`,
and `modifies(*count)` for `count: &&usize`. Each incoming reference is identified
by its structural argument path. An independent-input summary requires the
incoming reference regions to be disjoint, including nested fields and enclosing
references. Read-only references may alias too; those calls require a body
recheck because code can observe their identity. Several projections from the
same reference path form a permission union and may coincide.

If these disjointness checks fail, the verifier rechecks the function body using
the actual incoming planes and projection paths. It grants only the declared
writes after checking the caller's permissions, isolates the callee's local
facts/proofs, tracks actual stores and cleanup, and proves the postcondition
again. It does not assume the independent-port summary for this configuration.
Returned aliases and input types must remain valid, and caller-only enclosing
invariants are rechecked on return. Thus self-swap and self-copy are allowed;
a false promise that an aliased read-only port stays unchanged is rejected.
A contract can also hold for a particular aliasing input even when it would fail
for other inputs. No programmer-supplied alias-safety marker is involved.

`examples/aliasing_calls.evg` exercises self-swap and nested forwarding of a
written reference. Body rechecks and their proof certificates share the ordinary
evaluation depth, work, and proof-path budgets. Recursive overlapping calls may
hit these limits even when they terminate mathematically. Disjoint calls retain
the ordinary checked-summary path. Effectful Drop already elaborates the actual
receiver and proves its postcondition at cleanup, so its reference fields may
also alias when that body and its invariants remain valid.

The checker compares actual planes and projection paths: distinct fields or
proved-distinct array cells can be disjoint within one plane. Pointer equality
does not merge independent reference fields. Fixed-size input arrays containing
references now model each element's reference ports once. Contracts may name
`refs[1]` or `(*views)[1].target`, including arrays nested in records. Known
reference ports remain stable across reads and forwarding calls. Per-array
materialization is bounded to 2048 elements, with the general symbolic work and
fresh-value limits also applying. Symbolic-size arrays with hidden references
remain unsupported in modifying interfaces. `examples/reference_array_inputs.evg`
checks an element write, a returned alias, and an unchanged sibling.
`examples/reference_fields.evg` checks borrowed
counter views, nested fields, double indirection, and returned aliases. These
views do not represent reference-count ownership or allocation.

`evg run stdlib/counter.evg proofs/count_handles.evg examples/batch_count.evg`
constructs and clones two borrowed count handles, then consumes their array
through the library's `release_pair`. Both stored references target one counter;
the body recheck validates each remaining handle after preceding cleanup.
Constructing two handles over count one instead is rejected at batch release.
This catches that invalid transition but still does not prevent numeric handle
construction from overstating ownership; unforgeable plane authority remains
unimplemented.

References of compatible types support `==` and `!=` as location identity,
not pointee-value comparison. Valid plane identity, generation, and projection
paths determine equality. Two separate variables remain distinct even if their
contents are equal. For cells in one scalar array, equality becomes the checked
index-equality proposition, so symbolic indices work in proofs and runtime
branches. Both references must still be valid: comparing a stale reference,
even with itself, fails. No ordering, address-to-integer conversion, or pointer
arithmetic is supplied by these operators. Equality grants no ownership or write
permission.

`examples/reference_identity.evg` checks direct and forwarded comparisons,
equal-valued separate variables, and symbolic array paths, with VM/native
execution and certificate replay. Read-only functions must also respect aliases:
a summary checked with independent inputs cannot assert that aliased arguments
are distinct. Calls with overlapping input reference regions recheck the body
even when `modifies` is empty, including calls made by proof code or ideal code.
Preconditions still have to hold before that recheck, and its postcondition must
be proved for the actual alias configuration. References stored inside records
and fixed arrays participate in the same check. Independent input summaries
remain conditional on their checked disjointness; this is not an unconditional
proof of a function for every possible alias configuration. Recursive overlapping
calls retain the bounded recheck limitation described above. Comparing locations
does not supply allocation authority or a complete Rc implementation.

Function bodies must preserve their original incoming typed reference views,
even if local parameters are rebound. Calls can use that checked type-preservation
guarantee alongside the explicit postcondition. They also recheck changed storage
roots and the caller's typed views; caller-only enclosing invariants must follow
from the callee's guarantees. Array elements containing references receive the
same validity checks as record fields. An unused plain stale reference may remain
as `never`; observing it still fails generation checking.

`stdlib/swap.evg` implements verified `swap_usize` and `swap_bool` with
`modifies(left, right)` and entry-value postconditions. Run its example with
`evg run stdlib/swap.evg examples/disjoint_writes.evg`; the same ordered unit can
be proved or built natively. Swapping needs no compiler-specific operation.
Modifying calls inside invariant updates use these scalar ownership-free effect
summaries. Modifying calls in proof expressions and ideal functions are rejected. There are no
concurrency or atomic-operation guarantees in this rule.

While an update is open, every modifying helper call is checked against actual
storage, including its nested calls. Lifted requirements stay attached to the
opened planes across lexical function scopes. After every actual store the
checker verifies all remaining requirements of every opened object, including
requirements that read through references into other planes. A checked final
postcondition cannot hide an unsafe intermediate store. Ordinary write grants,
preconditions, and exact returned-alias contracts still apply. Calls with unknown
effects, runtime ownership operations, and whole-object observation remain
rejected. Helper body rechecks share the ordinary evaluation and proof budgets.

`examples/update_calls.evg` returns a scalar field borrow from a modifying helper,
uses a nested forwarding helper to restore the lifted accounting fact, and then
uses an older whole-object borrow after closure. It runs, builds, and replays
internally. `examples/reject_update_call_intermediate.evg` rejects a helper that
temporarily sets an external counter to zero while owners remain, even though
its final postcondition restores the old valid state. The independent trace
model in `proofs/PartialCorrectness.lean` separates validity at every state from
an endpoint postcondition and proves composition of checked traces. This remains
a specification rather than a proof of the Rust implementation.

Direct scalar writes use the same permissions and retained-invariant checks.
An update may assign through a scalar borrow, to a scalar array element, or to
a scalar binding; the typed target and all index bounds must still check.
Closed objects retain their full invariant checks. Only the explicitly named
requirements on opened planes are lifted. Assigning records, arrays, or reference
slots remains outside this scalar rule. The checker inspects the target's type
without evaluating its address twice, so a checked helper that selects the
lvalue executes once, before the right-hand side.

`examples/update_borrow_writes.evg` checks a declared write through an incoming
borrow, a symbolic array cell, a reassigned index with an earlier fixed borrow,
and an effectful lvalue selector. It runs, builds, and replays internally.
`examples/reject_update_borrow_write.evg` rejects a direct borrowed store that
violates the retained zero-count requirement, before a later restoration.

Scalar modifying calls also work inside conditional expressions. Verification
forks the symbolic store, checks each branch, and joins changed values with
relations guarded by the condition. Storage layout and live bindings must agree
on both exits. Consuming the same affine input in both branches works; consuming
it on only one branch is rejected until conditional shapes are implemented.
`examples/conditional_writes.evg` checks nested effects, aliases, and framed
sibling fields. These proof snapshots do not introduce runtime transactions.

Arrays of scalars and copyable scalar-field records record immutable store and
conditional-join histories. Nested record fields are supported; elements that
contain arrays, references, affine fields, or destructors need further rules.
A cell first observed after a write still obeys the store rule: it has the stored
value at the written index and the predecessor's value elsewhere. Reads after a
join inspect each predecessor under its own guard, preserving branch-local
facts. Cache hits replay these definitions and type facts rather than reusing a
proof valid only in the first read's context. Reading through a reference or
capturing `old(*reference)` uses the same semantics. These histories are proof
metadata; they neither allocate runtime storage nor grant write permissions.
History reads have depth at most 64 and charge expansion work to the ordinary
verifier budget.

A field write in one of these records stores the complete updated element in
the history. It preserves the other fields and affects another index's view
only when the indices are equal. `modifies` can grant a whole copyable record
or an array of such records as well as individual scalar fields. Same-layout
replacement preserves existing field borrows. Record invariants are checked
for every materialized cell, including arrays without expanded element lists.
Validation replays each cell's definitions and bounds, including views created
in the other branch of a join, and charges observation scans before cloning.
Temporary alias-merge records grant no invariant assumptions. While a modular
call's writes and postcondition are being instantiated, array reads cannot
assume caller-only record invariants; the caller must re-establish them.
Replaying an intermediate summary version later cannot grant its invariant
either; derived record values rely on their structural history relations.
The callee's declared input types remain implicit checked return contracts.

`examples/record_array_history.evg` exercises conditional field writes and old
field snapshots at symbolic indices. `examples/record_array_values.evg` replaces
whole refined records with nested record fields, preserving field borrows and
unchanged data. Both run, replay certificates, and build natively. An independent
two-field Rust model checks sixteen combinations of indices and conditional
overlapping helper calls, including rejection of wrong result contracts.
`examples/reject_record_array_invariant.evg` rejects a scalar helper call that
would break a record invariant in its caller's array.

`examples/array_frame_history.evg` proves a conditional write changes the selected
cell and preserves its previously unobserved sibling. It also exercises overflow
path pruning and strict replay. `examples/array_branch_history.evg` proves a
third cell is preserved across two different branch-local writes. Both examples
run and build with the internal backend.

Symbolic array reads are cached by contents version. Updating an element creates
a fresh contents version without changing the plane's storage generation, so
old read facts cannot certify the changed contents and existing references stay
valid. Symbolic indexing into reference-containing elements is rejected until
an alias-aware selection rule exists. A statically known index into a concrete
reference array retains the actual reference and works.

## Executable counter library and count refinement

```sh
cargo run -- run stdlib/counter.evg examples/counter.evg
cargo run -- check proofs/rc_protocol.evg stdlib/counter.evg proofs/rc_count_refinement.evg
```

`run`, `check`, and `prove` accept ordered source files. The counter library is
ordinary Evergreen code: checked increment, overflow-handling try-increment,
decrement with a zero-result flag, and an increment/decrement roundtrip. Tests
cover zero, one, `usize::MAX - 1`, and `usize::MAX`, and reject unchecked
underflow/overflow callers. No `trustme` is used.

The refinement wrappers prove that the physical sequential store realizes the
count component of the ideal reserve/release transitions. Their erased numeric
owner/credit arguments are metadata for this experiment, not ownership tokens.
This still does not establish a complete RC library's allocation, authority,
payload lifetime, destruction, or concurrent atomic behavior.

After disjunctions and branch joins, impossible paths are discarded only after the
kernel checks a contradiction certificate. Failed probes retain the path.
Those probes are included in replay artifacts; path and search limits remain
bounded instead of being raised to accommodate counter branches.

## Ideal parameters

`fn checked(value: usize, ideal expected: nat)` accepts scalar proof metadata
which is checked at calls and erased from execution. Contracts and proof terms
can inspect `expected`; runtime expressions, branches, assignments, and borrows
cannot. Actual ideal arguments use checked ideal execution, so affine proof
resources are consumed and runtime effects cannot be skipped by erasure. Their expressions are skipped by the evaluator,
including calls to ideal functions. Runtime arguments retain their source order.
`examples/ideal_parameters.evg` also uses an erased natural recursion measure.

This accepts `nat`, `int`, Boolean, machine and unit values, and ideal
records and arrays, including affine resources with borrowed references.
References may observe runtime storage, including runtime owners, without
transferring its ownership. Proof expressions are
non-consuming views; passing an affine resource as an erased execution argument
consumes it, preventing duplicate witnesses.

The physical count refinement wrappers now use erased owner/credit parameters:

```sh
cargo run -- run proofs/rc_protocol.evg stdlib/counter.evg proofs/rc_count_refinement.evg examples/rc_count.evg
```

That program executes increment/release stores, proves their relation to the
ideal protocol, and reaches zero without evaluating the ideal metadata. The
metadata still supplies no ownership authority.

## Native scalar executables

```sh
cargo run -- --deny-trust build examples/native.evg -o /tmp/answer
/tmp/answer
# The process exit status is 42; native programs currently produce no stdout.
```

`build` verifies the source, then emits a standalone Linux x86-64 ELF executable
with the internal backend. Ordered source files and `--proof source.evgproof`
are supported. No assembler, linker, C compiler, or runtime library is needed.
The supported subset includes machine scalars, Boolean and unit values, fixed
local arrays and records, field references and their writes, local mutation,
complete record patterns, invariant updates, calls, branches, and erased
facts/proofs/erased ideal arguments, and owned destructor cleanup.
Comparison instructions respect signed versus unsigned machine types.

The entry function's scalar result supplies the low eight bits of the process
exit status. The executable uses a private 64 KiB writable stack, with separate
read/execute code pages. Emission checks the entire static call-tree stack bound.
Native self-recursion is supported with a 128-activation budget shared by
self-recursive functions, whether or not a termination measure is supplied. Exceeding that budget
terminates with exit status 125. The static stack estimate reserves space for
all permitted recursive frames before accepting the executable. This estimate
is conservative and can reject large frames or nested recursive callees even
when a particular run would fit. Inline dependent
layouts are rejected. Unsupported or unproved input does not replace
an existing output; input sources cannot be overwritten.

Native tests execute generated programs and compare their results with the
interpreter, including signed minima, unsigned maxima, argument ordering,
Boolean expressions, branches, mutation, and erased arguments. Destructor tests
also compare cleanup counts and order using test-only machine instrumentation,
covering replacement, moves, field cleanup, and borrowed temporaries. These tests are
not a formal proof of compiler correctness. Source certificates do not certify
the generated instructions; the native backend and platform remain trusted.

Native scalar references point into the private stack. Borrowing a local,
following aliases, nested scalar references, and calls with checked scalar
write contracts are supported. Scalars use their declared widths, and references
occupy eight bytes. This internal convention is not a foreign ABI.

```sh
cargo run -- --deny-trust build stdlib/counter.evg examples/counter.evg -o /tmp/counter
cargo run -- --deny-trust build proofs/rc_protocol.evg stdlib/counter.evg proofs/rc_count_refinement.evg examples/rc_count.evg -o /tmp/count-refinement
```

The counter executable exits with status 42. The count-refinement executable
performs the checked sequential reserve/release stores and exits with status 0.
Native differential tests include these programs, scalar alias writes, nested
references, and Boolean updates.

Scalar representations live in `targets/x86_64.evg`, using literal type
construction rather than layout-producing functions:

```evg
module x86_64;

type i8 = make_type(
    size: 1, align: 1,
    represents: repr::Integral {signed: true, bits: 8,
        encoding: repr::TwosComplement, endian: repr::Little}
);
```

The target defines signed and unsigned 8/16/32/64-bit scalars, `usize`, `isize`,
Boolean, unit, and pointer storage. The bootstrap embeds and decodes those
representations once; edits require rebuilding it. The decoder requires a
complete profile compatible with the current x86-64 instruction backend.
`usize`/`isize` are respectively aliases of the 64-bit unsigned/signed layouts.

`make_type` is a primitive literal constructor. It checks storage width,
positive power-of-two alignment, signedness/encoding consistency, and known
representation fields. Native x86-64 currently requires little-endian data;
unsupported endianness or representations are rejected. A pointer descriptor
specifies target address storage, not a way to manufacture a valid reference.
These checks do not prove hardware correctness or establish C ABI compatibility.

Programs can define scalar aliases such as `Octet` with the same constructor;
`examples/scalar_types.evg` uses a one-byte unsigned alias and implements checked
addition as an ordinary Evergreen function. Aliases are transparent: they have
the underlying scalar's bounds, layout, conversions, and arithmetic checks.
They are not distinct nominal types with independent operators. Their layout
must match the active target. Constructors and `MIN`/`MAX` resolve through the
alias, and portable proofs bind the declaration source.

Arithmetic instructions and their proof rules remain generic compiler
primitives. User-defined operator implementations/dispatch and arbitrary
compile-time type generators are not implemented by this constructor. The
optional Lean reference translator rejects these declarations explicitly;
the internal verifier, interpreter, and native backend support them.

Native machine integers occupy their declared width (one, two, four, or eight
bytes), aligned to that width. Booleans occupy one byte; references and plane
owners occupy eight. Records retain declaration order, align each field, and
include tail padding to their maximum field alignment. Fixed arrays contain
consecutive elements, so `[u8; 7]` occupies seven bytes. Empty values reserve at least one
byte, rounded to their alignment, to preserve distinct address identities inside
arrays and records.
The private calling convention passes scalars in eight-byte stack slots and
rounds aggregate argument slots up to eight bytes; that does not change the
layout of addressable values. Copies access exactly the object size, including
short aggregate tails, and signed loads extend the stored value correctly. Inline aggregate layouts must be constant and at most 64 KiB;
ideal, recursive inline, overflowing, and dependent layouts are rejected. Constant
natural length arithmetic follows the frontend's truncated subtraction rules.

`examples/native_layouts.evg` exercises packed bytes, mixed-width fields, signed
loads, borrowed byte mutation, aggregate calls, and heap payloads. It returns 42
in both the interpreter and a compiled executable:

```sh
cargo run -- run examples/native_layouts.evg
cargo run -- build examples/native_layouts.evg -o /tmp/native-layouts
/tmp/native-layouts; echo $?
```

`examples/native_aggregates.evg` compiles owned local records, complete patterns,
field borrows, fixed arrays, and stable-layout replacement. Value reads preserve
snapshot semantics when later expression evaluation can mutate the source.
Pure stored indexing can read directly; effectful index expressions retain the
value copy. Native tests cover this ordering and nested arrays. Destructor cleanup still needs its own lowering rules.

Fixed aggregates can also be passed and returned by value. Arguments are copied
before later arguments are evaluated; returned values are copied into storage
owned by the caller. Native tests cover nested records, affine transfers,
constant-size array returns, empty arrays, equivalent constant length expressions,
and mutations in later arguments. The private stack bound includes argument
blocks, return buffers, callee frames, and expression temporaries. `main` itself
must still return a scalar exit-status value.

For example, `evg build examples/structs.evg -o /tmp/structs` compiles the checked
`Buffer` transformation and exits with status 2; `examples/conditional_records.evg`
compiles nested record returns and exits with status 42.

A field assignment cannot reinitialize a parent consumed while evaluating its
right-hand side. For example, `pair.left = take_left(pair)` is rejected when
`take_left` consumes the pair: restoring `left` would otherwise revive siblings
already moved or dropped by the helper. Replacing the whole parent with a new,
complete value remains valid. `examples/reject_partial_restore.evg` exercises
this ownership boundary; cleanup tests check the valid complete replacement.

`examples/array_contracts.evg` proves element-level contracts across array
parameters and returns, then composes them to prove the final result is 42.
Logical reads are keyed by immutable contents identity and normalized index,
separately from local bindings. Their type properties survive branch and call
scope changes; branch-specific facts do not. Writes still create a new contents
identity. Record-field and nested-array reads use the same logical read table.
Plain array literals at calls infer their element type from the parameter;
dependent length checks occur in the callee's parameter environment.

Discarding an owned expression drops its temporary at the end of that statement,
including values returned from helpers and moved out of a binding. Named locals
retain reverse-binding cleanup order. `examples/temporary_cleanup.evg` checks
that a returned temporary's fields are cleaned up before a later scope exit.

Owned temporaries inspected through fields (for example, `make().tag`) remain
alive until the statement's temporary scope ends, then drop in reverse creation
order. Conditions and branch blocks close their own scopes; a return expression's
temporaries drop before named locals. Nested function calls preserve the caller's
pending temporaries. Proof and fact expressions create no runtime temporaries.
`examples/borrowed_temporaries.evg` exercises these ordering rules.

Implicit temporary cleanup also checks that the destructor receiver still has
its valid type. A later operand cannot consume an owner referenced by a pending
temporary and leave that temporary with a dangling field at cleanup.

Native cleanup follows the interpreter: an owned `Drop` method runs before its
fields, fields clean up in declaration order, and remaining locals clean up in
reverse binding order. A move transfers cleanup responsibility. Replacement
cleans up the old live value, and borrowed owned temporaries survive until the
end of their expression or statement scope. Return values are saved across
cleanup calls. The emitted code uses no external runtime for these operations.

Compiler work limits also apply before proof search: parsed expression trees
have depth at most 128, unfolded named type graphs have at most 2048 nodes and
depth 64, and each verification context bounds symbolic expansion and
expression evaluation. Exceeding these bootstrap limits is a compile error,
not a trusted assumption. These limits are conservative implementation limits;
they are not a proof of a whole-process memory or time bound.

Conditional expressions can select scalar or copyable scalar-field record cells
within one array, for example
`if flag {&data[0]} else {&data[1]}`. Both alternatives must use the same live
plane and generation, the same projection prefix, and compatible target types.
One array index may differ, followed by the same optional record-field path.
For example, selecting `&data[0].point.x` or `&data[1].point.x` is supported for
copyable record elements with scalar leaves. The verifier introduces a proof-only
selected index tied to each branch, proves its bounds, and materializes its view
in the joined array contents. It checks the selected record's suffix and target
type while materializing that view. It does not allocate a replacement target plane.
Reads, writes, identity comparisons, and later same-layout replacement continue
to use that cell. Previously tracked array views survive the join too.
References stored in conditional records use the same rule, including records
with Drop cleanup.

`examples/conditional_borrows.evg` checks both selections at runtime and returns
a selected reference from a helper whose exact entry-index alias is proved.
`examples/conditional_drop.evg` selects a resource containing one of two cell
references, then proves its destructor writes the selected cell. Both examples
run, build, and replay with the internal verifier.
`examples/record_array_borrows.evg` selects both whole record cells and scalar
fields, proves their identities agree, and checks writes and same-layout
replacement through those borrows. It also runs, builds, and replays internally.
Conditional scalar-array
values also join their contents and tracked views. Different target planes,
different record-field suffixes, conditional storage generations, and selections
of owning or reference-bearing record elements remain unsupported. Returned references must match
the exact entry projection declared by `borrows`, including a conditional entry
index as described below. Selecting between different target planes in a
contract remains unsupported.

A reference return requires an exact alias contract, for example:

```evergreen
fn identity(r: &usize) -> &usize borrows(r) {r}
fn right(pair: &Pair) -> &usize
borrows(&(*pair).right) {&(*pair).right}
```

Index expressions in `borrows` and `modifies` can use pure comparisons, Boolean
conditions, and `if`, for example:

```evergreen
fn select(data: &[usize; 2], flag: bool) -> &usize
borrows(&(*data)[if flag {0} else {1}]) {
    if flag {&(*data)[0]} else {&(*data)[1]}
}
```

The selection is evaluated at entry. Rebinding a Boolean selector or updating a
scalar used by its condition cannot retarget the permission or returned alias.
Each selected index must be proved nonnegative and within the array. Conditions
may inspect entry scalar storage or compare incoming references; user calls,
address construction inside indices, ownership operations, and proof escape
hatches remain excluded. Overlapping input reference regions trigger the normal
body recheck, including identity-sensitive selections. `examples/conditional_contracts.evg`
combines a conditional returned alias with a conditional write footprint and
checks both choices at runtime. These expressions remain subject to the same
64-path and symbolic-work limits as other verification code.

`borrows` follows `where`/`modifies` and precedes `ensures`. The contract names
the exact incoming reference or field projection returned, not merely a value
with equal contents. The checker compares plane identity, generation, and
projection independently of arithmetic proofs or `trustme`. The target must
come from an incoming reference value, including a reference stored in a record
parameter. Returning a local, a parameter slot, or a reference different from the
named origin is rejected. Calls instantiate the
contract with the actual caller reference, so later same-layout writes remain
visible and dropping/replacing consumed storage cannot revive the reference.

This contract supports direct reference returns, record projections, and scalar
array elements in the interpreter and native backend. It can be combined with
`modifies`: the returned alias is fixed at entry, writes follow the declared
footprint, and the reference is checked again after the write summary. A returned
reference exposes current contents; it does not grant a caller additional write
permission. Returning a parent record after changing one field still requires
preserving that record's invariants.

`arrays::set_get` in `stdlib/arrays/array.evg` updates one cell and returns its reference.
`evg run stdlib/arrays/array.evg examples/write_borrows.evg` exercises forwarding that
contract, existing aliases, and later same-layout replacement. An index rebound
inside the function cannot retarget its entry alias contract.

Owning records can return inline reference fields with an exact mapping for each
field, for example `borrows(target: target)` or
`borrows(release.count: (*handle).release.count)`. Paths on the left name fields
of the returned record; expressions on the right name incoming references or
storage owned by the returned value.
Every reference field needs exactly one mapping. Calls preserve those actual
planes rather than inventing reference storage. Dependent field extents and
record invariants are checked on the returned value, including after local
cleanup, before callers may rely on them. Moving the returned record does not
extend the lifetime of its borrowed storage.

A returned owner can anchor a companion view with `result` on the right:

```evergreen
type Packet struct {owner: plane(usize), view: &usize}
fn make(value: usize) -> Packet
borrows(view: &*result.owner) {
    let owner: plane(usize) = alloc(value);
    let view = &*owner;
    Packet {owner: owner, view: view}
}
```

The anchor must cross an owned plane in the result. It cannot borrow an inline
return slot, follow a borrowed pointer, or merely name another returned view.
Fields, nested owners, and checked array projections are supported. Index
observations can refer only to the returned value and constants; incoming alias
entries retain their existing entry-state semantics. Representation access is
checked in the function's module. `result` in this contract names the returned
value, so an input with that name must be renamed. Every reference leaf still
needs an alias contract, including erased reference fields.

Result anchors are checked after scope cleanup against the final returned
storage. A destructor cannot change a selector and leave an old view claiming
to match its new selection. Returned owner/data generations must also remain
live after cleanup. All heap calls use actual-body checking; no modular return
shape invents ownership for this case. An independent-port declaration that is
infeasible under its nominal alias invariant may discharge a mismatch only with
a kernel-checked contradiction from its entry configuration. A later `trustme`
cannot discharge a provenance mismatch. Actual calls and `main` always require
concrete alias agreement, including on paths with trusted falsehoods.
`examples/owned_result_views.evg` checks an
opaque owner/view carrier through construction, forwarding, reading, and final
consumption. This remains unique ownership; it does not implement Rc sharing.

`examples/owned_borrows.evg` demonstrates a returned resource whose Drop writes
through its reference field. `examples/borrowed_view.evg` demonstrates a borrowed
array with a dependent extent. `proofs/count_handles.evg` and
`examples/clone_count.evg`, used with `stdlib/counter.evg`, demonstrate constructors,
cloning, and nested cleanup written in Evergreen. This is a borrowed numeric
count model, not allocation authority or a proof of actual Rc ownership.

Literal-size arrays can also return references and owning records containing
references. Use `result[0]` for a top-level element or `items[0].target` for an
array nested in a returned record. Every reference leaf needs one exact alias:

```evergreen
fn neighbors(data: &[usize; 3], index: usize) -> [&usize; 2]
where(index < 2)
borrows(result[0]: &(*data)[index], result[1]: &(*data)[index + 1]) {
    [&(*data)[index], &(*data)[index + 1]]
}
```

Target indices must be nonnegative integer literals; incoming indices may use
checked arithmetic. Reference-bearing return arrays currently require literal
extents and alias expansion is bounded to 2048 visited type nodes and depth 64.
`examples/borrowed_array.evg` demonstrates forwarding and later writes;
`examples/borrowed_array_owners.evg` returns an array of resources whose Drop
writes through the declared references. Its consuming function declares the
implicit cleanup writes through its incoming array elements. Arrays are cleaned
in ascending order.
Symbolic-size reference arrays and contracts selecting between different target
planes remain unsupported.
All call arguments are rechecked together after evaluation, preventing a later
argument from consuming storage borrowed by an earlier one.

The optional Lean suite checks independent specifications:

- `proofs/LinearCertificates.lean` defines weighted combination of original
  integer rows and proves that accepted certificates imply unsatisfiability.
  Negative weights, missing row indices, and nonzero remaining coefficients
  fail in the executable model. The specification also proves that equivalent
  row-membership lists have the same models and that a checked contradiction
  licenses removal of a disjunctive path.
- `proofs/MemoryContracts.lean` models fixed-layout scalar addresses and proves
  that disjoint writes commute, writes preserve other addresses, and the swap
  postcondition and involution hold. Distinct fields of one plane are disjoint.
  Its invariant-framing rule accounts for read footprints spanning multiple planes.
  Guarded index joins preserve bounds and read the selected cell in one plane.
  Its structural record-array model proves the field-store rule and makes
  validity of the replacement record an explicit invariant-preservation premise.
  Its observer rule evaluates a stored pointer after the write, distinguishing
  aliases of the target from other addresses and specifying self-observation.
- `proofs/PropositionalProofs.lean` defines contextual derivations for the
  structural propositional rules and proves their soundness under a valuation.
  Implication introduction extends only its subproof's context; application
  requires both the implication and its premise. Case analysis requires both
  disjunction branches and confines their hypotheses to their respective
  contexts. It also proves the classical
  implication/disjunction identity and that false has no closed derivation.
- `proofs/Planes.lean` also proves that same-layout writes preserve references,
  restoring dropped storage does not revive old generations, and valid handles
  into one current plane share its identity and generation. The indexed-address
  model separately proves that array cell identity agrees with index equality.

These proofs use the pinned Lean toolchain and no admitted propositions. They
are specifications of the rules, not proofs that the Rust implementation,
i128 overflow handling, parser, or native instructions refine those rules.
Run them with the optional ignored integration test described above. Ordinary
Evergreen verification continues to use the internal checker alone.

Array references now also work through abstract array parameters. For example:

```evergreen
fn first(ideal n: nat, data: &[usize; n]) -> &usize
where (n > 0)
borrows(&(*data)[0]) {&(*data)[0]}
```

The checker proves the index bound and records the selected scalar cell lazily
in the array's existing plane. It does not allocate a separate plane or expand
the whole array. The reference retains the root generation and index path, so
ordinary reads, returned aliases, and scalar writes observe the same cell.
Writes change the array contents version while preserving storage identity;
previously observed constant-index siblings remain framed. Branch joins merge
these cell observations with guarded value relations.

`examples/array_borrows.evg` runs, replays from a proof artifact, and builds with
the internal native backend. It returns references from a length-indexed helper,
writes one cell, and proves that the other cell is unchanged. This initial lazy
representation now supports scalar elements at proved symbolic indices too, as
described below. Fixed-size reference-bearing input arrays also support literal
index projections through their modeled elements. Symbolic indices into
reference-bearing elements still require additional alias rules; symbolic-size
arrays with hidden references remain opaque.

Logical implication is written `premise => consequence`. It has lower precedence
than `||` and associates to the right: `a => b => c` means `a => (b => c)`.
Like the other Boolean operators, both operands must be well-defined; it is
not a short-circuit guard around an otherwise invalid operation. The internal
verifier retains its structure for proof steps and normalizes it to
`!premise || consequence` before generating arithmetic certificates. The optional
Lean proposition emitter uses logical implication.

`examples/weak_invariant.evg` demonstrates the proposed selective-lifting rule
with a numeric ledger: exact accounting is lifted, while
`count == 0 => owners == 0` remains required after every store. A proof of that
weaker fact works during the update; claiming exact accounting before restoring
it or setting count to zero while an owner remains is rejected. The ledger is
a language-rule test, not an implementation of `owners(plane)` or `Rc`.

Dynamic scalar array borrows carry a symbolic index snapshot in their plane
projection. For example, `borrows(&(*data)[index])` checks both bounds and the
identity of the returned cell. Reassigning the index variable later does not
retarget an existing reference. An equivalent index may be used in the body
when equality follows from the function's precondition.

Place contracts also accept checked linear arithmetic, scalar field/dereference
reads, and array lookups in indices. For example,
`borrows(&(*data)[index + 1])` and `modifies(&(*data)[index + 1])` capture the
entry value of that expression. Ordinary machine overflow and index bounds
must be proved, including for the contract itself. Proof-only `int`/`nat`
conversions can express mathematical indices; the body must still prove that
its runtime index selects the same cell. User function calls and statement
blocks are not place expressions in this bootstrap.

`examples/computed_places.evg` checks equivalent arithmetic index expressions,
precise writes, and a helper that advances a mutable cursor while returning a
reference selected with its old value. Changing the cursor cannot retarget that
reference or the function's entry write permission.

The symbolic store preserves conditional aliasing: writing through index `i`
updates a tracked cell at index `j` when `i == j`, and preserves it when `i != j`.
Ordinary scalar reads have the same array-selection consistency rule. Writable
places passed through distinct reference parameters require a checked
disjointness proof for a modular summary; otherwise their actual body must be
rechecked. Different symbolic expressions alone do not establish different
locations. Multiple projections from one incoming array share its alias model
and may coincide.
`examples/indexed_borrows.evg` verifies both outcomes of a possibly aliasing
write and works with certificate replay and native emission. These additional
relations remain subject to the verifier's path and proof-work limits.

Modules provide a closed lexical namespace:

```evergreen
module permits {
    opaque affine type Permit struct {tag: usize}
    fn issue() -> Permit {Permit {tag: 42}}
}
fn main() -> usize {let permit = permits::issue(); 42}
```

Within a module, local type and function names resolve to that module. Clients
use qualified names such as `permits::Permit` and `permits::issue()`. Modules
are checked in the same ordered proof unit, introduce no trusted declarations,
and cannot be reopened or nested. Functions and type names are currently all
exported. Explicit call dependencies are checked before their callers regardless
of source order.

`opaque` hides construction, field reads/writes, field borrows, and destructuring
from other modules. It requires a defining module. `affine` separately prevents
implicit duplication. Values can still be passed, moved, borrowed as a whole,
and used through checked functions. Public named type facts remain available.
Function contracts are checked and instantiated in their defining scope; a
callee's representation access never grants that access to caller expressions.
Drop implementations must belong to the type's defining module. Identifiers
have a 256-byte bootstrap limit.

`stdlib/credits/credits.evg` is an opaque affine quantity library with no public mint
operation. Its checked API observes units by reference and splits/joins existing
credits while conserving their total quantity. The client proof in
`proofs/opaque_credits.evg` uses only that API and the public split-result record.
Check both files together. Clients cannot manufacture a new credit from a number
or duplicate an existing credit. This abstract quantity is not yet connected to
a physical allocation, `owners(plane)`, or atomic operations.

`examples/opaque_values.evg` demonstrates runtime opaque values, public facts,
and checked accessors; it runs and builds natively. Module-qualified programs
use the internal verifier; the optional Lean expression emitter remains limited
to its existing non-modular reference subset.

The abstraction tests also run through the CLI: checking
`stdlib/credits/credits.evg proofs/opaque_credits.evg` succeeds, while checking
`stdlib/credits/credits.evg examples/reject_forged_credit.evg` rejects client construction.
Verification and entry-precondition checking use a bounded 16 MiB worker stack,
independent of the caller's stack; existing depth and work limits still apply.

Affine ideal values can now be passed through runtime signatures, for example
`fn consume(ideal ticket: tickets::Ticket, value: usize) -> usize`. Evaluating
an erased actual is ideal execution, so passing a move-only ideal ticket
consumes it. The interpreter and native backend omit its storage and the whole
actual expression. Proof expressions remain non-consuming views.

`examples/erased_resources.evg` forwards a ticket once and returns 42 in both
backends. The checker rejects duplicate forwarding, runtime inspection, and
using `old(ticket)` to recreate a consumed ticket. Scalar `old(...)` snapshots
remain valid erased metadata. Erased arguments may contain ideal records
and arrays with borrowed references. Runtime owners cannot be constructed or consumed by ideal execution,
and erased calls must be ideal code or checked pure scalar helpers. Thus
erasure cannot silently skip a runtime write, move, drop, or owner-producing
operation. This still does not supply allocation authority or `owners(plane)`.

Ideal functions that return references or reference-bearing resources use the
same exact `borrows` contracts as runtime functions: every reference leaf must
come from a declared incoming projection, with its plane, path, and generation
preserved. A returned reference cannot point into an ideal callee's local frame.
Erased references are available in proofs and erased computations, and grant no
runtime write access. Runtime code cannot use them as addresses, return values,
or branch conditions. They still participate in alias and typed-view checks,
including body rechecks when erased and runtime inputs overlap. Dropping and
restoring the target does not make an old erased borrow valid again.

`examples/ideal_borrow_resources.evg` attaches an opaque affine proof view to a
resource field, passes it through an erased parameter, and reads through a
separate runtime argument whose identity is proved equal. The resource still
runs its ordinary Drop exactly once. The example runs, builds, and replays
internally; `examples/reject_ideal_borrow_escape.evg` rejects runtime use of an
erased pointer.

`stdlib/borrow_credits/borrow_credits.evg` binds existing credits to a live reference. Its opaque
affine tokens split and join while conserving quantity and preserving the exact
target. Joining requires equal target identities. Check the client with:

```sh
evg --deny-trust check stdlib/credits/credits.evg stdlib/borrow_credits/borrow_credits.evg proofs/borrow_credits.evg
```

The API has no mint operation. These are conserved proof quantities attached to
borrowed views; they do not authorize allocation or deallocation, count actual
owners, or implement Rc. The Lean plane model separately proves that changing
bookkeeping while preserving a handle preserves its validity test and cannot
revive that handle after drop and restoration. This is not a proof of Rust
erasure or affine checking.

Proof artifacts bind the regenerated verification conditions as well as the
source. Strengthening the checker can invalidate a cache even when source text
is unchanged; re-prove it with the new checker. The checked-in RC protocol
artifact now has a regression test that replays it without proof search.

Function-local proof data uses `ideal let`, including complete patterns:

```evergreen
ideal let original = credits::units(&credit);
ideal let parts = credits::split(credit, nat(amount));
ideal let credits::Split {left, right} = parts;
proof conserved: credits::units(&left) + credits::units(&right) == original;
```

The bindings are checked with ideal execution and ordinary affine ownership
rules, then erased from runtime storage, evaluation, and cleanup. Their values
can be used in proofs and erased arguments, but cannot drive runtime returns,
branches, assignments, or borrows. Opaque representations stay private in ideal
code, and extracting owning fields still requires a complete record pattern.
Erased expressions cannot construct, consume, or destroy runtime owners.

Existing ideal bindings can be replaced with `ideal name = expression;`, including
their structural fields and array cells. The target must be proof storage:
an ideal binding, an ideal function's local storage, or a declared ideal field.
Dereferencing a borrow resets that classification. A mathematical `int`/`nat`
or ideal record pointee is proof storage, while an erased `&usize` can still
point to runtime data and cannot authorize an erased write. Borrowed writes
need a matching effect contract unless the caller owns their target plane.
Updating an ideal copy of a runtime array changes only the proof copy.
Runtime code still cannot read the resulting ideal value or address.

Selective updates also accept `ideal let` bindings, complete ideal patterns,
and ideal assignments. Affine proof resources move normally; replacing a consumed
outer ideal binding restores its value with the ordinary generation rules.
Update-local proof bindings and their phase markers are removed on exit, and
remaining typed views are rechecked after local cleanup. `examples/ideal_update_state.evg`
checks ideal assignment, independent array copies, and reuse of a local name in
runtime code after the update scope closes. It runs, builds, and replays internally.

`proofs/borrow_credit_updates.evg` combines these rules with the borrowed-credit
library. It splits off and consumes one unit, reduces the numeric owner ledger
before the counter, replaces the outer ideal token, and proves the remaining
quantity equals the counter. Check it after `credits.evg` and `borrow_credits.evg`.
The zero-is-safe requirement stays checked at each runtime store, including the
transition from one to zero; reversing those stores is rejected. The Lean trace
model proves the corresponding numeric ordering rule. This is a numeric protocol
example, with no allocation, deallocation, or actual owner-set authority.

`examples/ideal_bindings.evg` runs and builds to exit status 42. Check
`stdlib/credits/credits.evg proofs/ideal_credit_bindings.evg` for a runtime function that
splits an existing ideal budget and consumes each part once through erased
parameters. The shipped library still has no mint operation. The optional Lean
backend evaluates these local bindings as mathematical data in its ideal
reference model, while Evergreen's runtime backends erase them.

Runtime records can carry proof fields with `ideal field: Type`:

```evergreen
type Checked struct {value: usize, ideal expected: nat}
where(expected == nat(value));
```

These fields remain in verification, nominal invariants, alias contracts, and
affine ownership. They are omitted from interpreter values and native layouts,
construction, pattern storage, and runtime cleanup. Their initializer expressions
run in checked ideal execution and are erased completely. An affine ideal field
makes the containing runtime value affine: moving the value transfers its proof
resource, and reusing the old value is rejected. Erased fields may own ideal data
and borrowed views, but cannot hide a runtime owner by value.

Runtime expressions cannot read, borrow, or assign these fields. `ideal` writes
may update a record's ideal fields through owned or authorized borrowed storage; they still
recheck the record invariant. Complete runtime record patterns bind every field,
with names from ideal fields automatically marked ideal. Drop proofs may inspect
ideal fields, while only runtime fields participate in emitted cleanup and its
declaration order. References inside ideal fields remain part of alias checking.
Plane generations still apply to the whole record, so changing a proof
aggregate's logical layout can invalidate other views of that record too.

Ideal functions may declare checked `modifies` footprints for borrowed proof
storage. For example, `ideal fn set(r: &nat, n: nat) modifies(r)
ensures(*r == n) {*r = n;}` updates mathematical state and emits no runtime
write. Scalar slots inside ideal records, and declared ideal fields projected
through runtime records, are also supported. A nested call needs the caller's
own matching footprint unless the caller owns that storage. Calls that modify
proof state are forbidden inside propositions and specification expressions.

Erasure follows the target slot, not the pointer value: an ideal record can
contain `target: &usize`, but an ideal function cannot declare
`modifies((*record).target)` to mutate that runtime pointee. Entering a nested
reference resets the proof-storage classification. Mathematical `int` and `nat`
slots can be modified. Whole affine ideal records are supported when their
representation is an erased tree of scalar fields with no references or arrays.
This allows a client to declare `modifies(credit)` for opaque credits and forward
an authorized library write without exposing private fields. It grants neither
permission to access the representation nor permission to copy the affine value.
Whole runtime affine records, reference-bearing ideal regions, and reference-slot
replacement remain unsupported effect regions. Copyable scalar-field records
retain the ordinary aggregate effect support. Every write during an open update, including
nested ideal calls, checks all retained invariants against actual shared memory.
`examples/ideal_borrow_writes.evg` exercises forwarding, proof-field writes,
transactional invariant restoration, erasure, and certificate replay.

The opaque credit library uses this mechanism in `credits::take(&credit,
amount)`: it decreases the borrowed credit and returns a new affine credit of
exactly `amount`. Its checked postcondition conserves the sum against the entry
quantity using `old`. Sequential calls see the updated balance; overdrafts fail
at the next precondition. `proofs/borrowed_credit_transfer.evg` checks taking and
rejoining existing credits. This API still has no mint operation and grants no
allocation authority. Its footprint names its private scalar slot in the
defining module. `take_existing` forwards through a whole opaque credit footprint
and expresses conservation through the public accessor in `old`. The borrowed
token library forwards through its `budget` field in `borrow_credits::take`,
leaving the target reference outside that footprint. Check
`stdlib/credits/credits.evg stdlib/borrow_credits/borrow_credits.evg proofs/borrowed_token_transfer.evg`
for taking and rejoining an existing token while preserving its target identity.
Overlapping input regions recheck the body on actual shared storage; two aliases
cannot independently withdraw the same last credit.

`examples/ideal_fields.evg` checks affine witnesses carried through runtime
records, complete patterns, selective proof-field updates, and parent/child Drop
order. It also checks distinct identities for records containing only ideal
fields; native storage reserves one byte for each empty value's identity.
The example runs, builds, and replays internally. Check
`stdlib/credits/credits.evg stdlib/borrow_credits/borrow_credits.evg proofs/carried_borrow_credits.evg`
for a runtime carrier that owns a borrowed-credit token without storing that
token in its runtime representation. The Lean record-projection model checks
that ideal-field replacement frames runtime-only properties, while joint
invariants require validation. These models remain separate from implementation
refinement and do not add allocation authority.

The checker derives possible divergence rather than accepting an unchecked
annotation. A runtime self-recursive function without `decreases` may diverge;
that property propagates to its runtime callers. Every returning path must
still satisfy its postcondition, and all ordinary safety checks remain active.
Providing a decreasing measure proves totality only when its callees also have
proved totality. Ideal recursion always requires the termination proof.

Potentially divergent functions cannot be called from proofs, ideal bindings,
erased arguments, or contracts. This prevents a nonreturning function with
`ensures(false)` from becoming logical evidence of falsehood. The CLI reports
when a checked unit contains functions that may diverge. Execution remains
bounded: interpreter exhaustion is an error, and native recursive exhaustion
exits with status 125. Neither is a normal function return.

`examples/partial_recursion.evg` returns 42 without a termination annotation;
`examples/reject_divergent_proof.evg` is rejected. The optional Lean suite also
checks `proofs/PartialCorrectness.lean`, which separates a postcondition on
return from the existence of a return and proves partial-contract composition.
As with the other specifications, this is not an implementation-refinement proof.

Symbolic data expansion is metered independently of syntax depth and fresh
variables. A logical value is limited to 32768 expanded nodes and depth 128;
each verification context has a 262144-node value-work budget. The budget
includes value traversal, environment and branch snapshots, borrowed views,
and indexed replacements. Small source programs that repeatedly double nested
arrays or Boolean formulas therefore fail with a work-limit diagnostic before
unbounded materialization. These are conservative bootstrap availability limits,
not a formal whole-process resource bound or a new proof assumption.

Interpreter work accounting includes expanded expression results, aggregate
copies used for storage views and assignments, detached result snapshots, and
cleanup traversal. Copying an aggregate is charged before explicit snapshot
clones, so a small recursive body cannot repeatedly copy a large argument for
the cost of one AST node. Exhaustion returns an execution-limit error, not a
normal result. These interpreter limits are separate from native stack guards
and do not constitute a formal whole-process time or memory bound.


### Native syscalls and byte output

Build and run the first output example on Linux x86-64:

```sh
cargo run -- build stdlib/linux_io/linux_io.evg examples/hello.evg -o /tmp/hello-evergreen
/tmp/hello-evergreen
```

It prints `Hello, Evergreen` followed by a newline and exits with status zero.
`run` uses the interpreter, which deliberately rejects external syscalls; use
`build` for this example. The compiler has no built-in print or text-encoding
operation. `stdlib/linux_io/linux_io.evg` implements byte output in Evergreen.

The primitive external declaration is an explicit Linux x86-64 syscall number:

```evg
extern syscall(1) fn write_byte(fd: usize, byte: &u8, count: usize) -> isize
where(count <= 1)
ensures(result <= 1);
proof {trustme}
```

Arguments follow the [Linux x86-64 syscall register order](https://man7.org/linux/man-pages/man2/syscall.2.html):
rdi, rsi, rdx, r10, r8, r9. The raw
result is a signed 64-bit integer, including negative error codes. Declarations
accept up to six runtime arguments: 64-bit integers or references to data without
embedded references or owners. Borrowed arrays may have symbolic lengths with
fixed-layout elements. Scalar parameters are in scope throughout a signature,
including when the length parameter follows the buffer. Existing `ideal`
parameters can describe capacities and contracts; they consume no OS arguments. No ownership or borrowed references can be
returned. Referenced array elements use their physical packed representation;
a declaration borrowing `[u8; 3]` can pass all three bytes to `write` in one call.

The explicit `trustme` covers OS behavior, declared access bounds and write
footprints, preservation of types/invariants, and absence of retained access to
borrowed data after return. The checker proves caller preconditions, liveness,
and write permissions, and uses the trusted postcondition on return. A false
external contract can invalidate safety. Every declaration is recorded in the
trust manifest even when unused, replay checks it, and `--deny-trust` rejects it.
A syscall may block or fail to return, so calls are forbidden in specifications,
proofs, ideal execution, and currently in Drop or lifted-invariant updates.
Overlapping reference ports are rejected because there is no body to recheck.
General foreign linking, foreign aggregate ABIs, and interpreter OS emulation
remain unsupported.

`linux_io::print_bytes(length, bytes)` accepts a borrow of `[u8; length]` and
attempts one write of the entire buffer. It returns the raw `isize` byte count
or negative error code. The hello example checks that the returned count equals
17; a nonnegative short count is not full success. The library does not yet retry
short writes or interrupted calls. Printing no longer recurses or makes one
syscall per byte.

The library has one trusted declaration. `write_byte` and `stdout_byte` are
ordinary checked Evergreen wrappers. The generic external `write` also takes an
erased capacity, allowing a checked prefix write:

```evg
let bytes: [u8; 3] = [65, 66, 67];
let written = linux_io::write(1, &bytes, 2, 3);
```

This attempts to write `AB`. The checker rejects a count exceeding capacity or a
capacity inconsistent with the actual borrowed array. Capacity is a proof
argument; Linux receives only the file descriptor, buffer address, and count.
The library neither validates nor assumes UTF-8; encoding validity belongs in an
Evergreen library refinement over the bytes, not in the compiler.

### First target atomic operation

`stdlib/x86_64_atomics/x86_64_atomics.evg` declares an explicitly trusted 64-bit
compare-exchange operation. The declaration is generic over three operands,
not tied to reference counts:

```evg
extern compare_exchange64 fn compare_exchange(
    value: &usize, expected: usize, desired: usize
) -> usize
modifies(value)
ensures(result == old(*value)
    && (old(*value) == expected => *value == desired)
    && (old(*value) != expected => *value == old(*value)));
proof {trustme}
```

It returns the observed old value. On success the stored word becomes desired;
on failure it remains unchanged. The interface requires a matching 64-bit
integer type for the referenced value, expected/desired operands, and result,
and a write footprint for the referenced word. Erased proof parameters follow
the existing external-call rules. The native backend additionally requires
eight-byte alignment and emits `lock cmpxchg`. The interpreter implements the
same sequential state transition. No OS call is involved.

```sh
cargo run -- run stdlib/x86_64_atomics/x86_64_atomics.evg examples/compare_exchange.evg
cargo run -- build stdlib/x86_64_atomics/x86_64_atomics.evg examples/compare_exchange.evg -o /tmp/compare-exchange
/tmp/compare-exchange; echo $?
```

Both executions produce 42. Differential tests also cover unsigned maxima,
signed minima, array-element references, heap payloads, and failed exchanges.
The contract is an audited assumption, replay records it, and `--deny-trust`
rejects it. Like other external operations it is conservatively classified as
potentially divergent, excluded from erased/proof calls, and not currently
admitted inside lifted-invariant updates or destructors.

This is a target primitive and a sequential specification, not concurrent Arc.
In particular, `old(*value)` currently means the existing sequential entry
snapshot. A future concurrent invariant rule must relate the operation to the
value at its linearization point, and must not preserve arbitrary prior loads
as facts about shared memory. No thread API, memory-order parameters, release
sequence proof, or concurrent payload-access guarantee is implemented yet. See
[the shared ownership obligations](shared-ownership.md).

`stdlib/atomic_counter/atomic_counter.evg` implements increment/decrement retry loops entirely
in Evergreen using compare-exchange. Increment refuses saturation instead of
wrapping; decrement refuses underflow and returns the observed old count. The
old value of one identifies a final decrement without a separate zero load.
The library adds no trusted assumptions beyond the target operation:

```sh
cargo run -- run stdlib/x86_64_atomics/x86_64_atomics.evg stdlib/atomic_counter/atomic_counter.evg examples/atomic_counter.evg
cargo run -- build stdlib/x86_64_atomics/x86_64_atomics.evg stdlib/atomic_counter/atomic_counter.evg examples/atomic_counter.evg -o /tmp/atomic-counter
/tmp/atomic-counter; echo $?
```

These retry loops are conservatively partial and subject to execution limits.
Their checked contracts are sequential; they do not establish concurrent Rc/Arc
or permit a shared counter equality to survive interference. The shared ownership
Lean model now proves that an individual successful checked CAS attempt matches
one ledger transition and a failed/saturated attempt leaves the ledger unchanged,
assuming the corresponding owner/retiring token is held and the comparison
happens at the modeled atomic point. Connecting that assumption to the compiler's
future shared-invariant rule and to the instruction memory model remains work.

### Checked machine integer conversions

Calling a machine integer type converts an integer while preserving its
mathematical value: `u8(value)`, `i16(value)`, `usize(value)`, and so on. The
checker proves both destination bounds. This is not a truncating or wrapping
cast, a pointer conversion, or a way to materialize erased data at runtime.

```evg
fn narrow(value: usize) -> u8
where(value <= 255)
ensures(nat(result) == nat(value)) {u8(value)}
```

A branch checking a signed result is nonnegative can use `usize(result)` inside
that branch. Narrowing a value whose range has not been proved fails even if a
particular caller currently passes a small constant. Conversions do not widen
arithmetic inside their argument: `i16(i8::MAX + 1)` still rejects the overflowing
`i8` addition; widen the operand before performing that addition instead.
Untyped literals receive the destination's contextual type.

Conversions are pure and permitted in checked entry snapshots and scalar cleanup
helpers. In ideal/specification code they can relate mathematical integers to
bounded machine values, but ordinary runtime code cannot read ideal inputs or
mathematical views through a conversion. Machine type names are reserved at
function declarations. The native backend needs no conversion instruction after
a correctly extended load when the checker has proved representability.
`examples/integer_conversions.evg` runs and builds without trusted assumptions.

`examples/owned_return_cleanup.evg` exercises a destructor that updates an
allocation already moved into the function's pending return value. The checker
keeps that value's ownership authority live until local cleanup finishes;
postconditions and result alias checks observe the state after cleanup. Cleanup
also recognizes allocations reachable through ordinary live owners and through
the destructor receiver itself. `examples/owned_destructor_cleanup.evg` mutates
its owned allocation before child cleanup frees it. Released roots are not
revalidated as live post-state objects, and stale references remain invalid.
These rules still require write footprints for borrowed, externally owned data
and preserve payload invariants on actual writes.


### Bundled standard library

Internal `check`, `prove`, `run`, and `build` resolve bundled stdlib dependencies
automatically, including transitive dependencies. For example, build
`examples/hello.evg` by itself; mentioning `linux_io::print_bytes` loads its
Evergreen implementation. Dependencies are embedded in the compiler, so the
executable need not run from the repository directory. Explicitly listing stdlib
files remains supported and does not load the same module twice.

Loading is demand-driven: an arithmetic-only program does not acquire the IO or
atomic trusted contracts. Referenced external declarations remain audited, and
`--deny-trust` still rejects them. Certificates bind the bytes of automatically
loaded dependencies as well as the input source. User expression line numbers
are preserved instead of shifting when a stdlib file is added. The optional
legacy Lean translator retains its existing supported subset.

Unknown-function diagnostics now report that error alone; the decreases-clause
hint is emitted specifically for an undeclared self-call in an ideal function,
not appended to every missing-name error.


Ideal scalar extents can now be inferred from array argument types. For example,
`linux_io::write(1, &bytes, 2)` infers the proof-only capacity from `bytes`; the
runtime count remains explicit. Calls may supply all arguments as before, or
omit all ideal arguments. Inference currently handles direct named array
extents, including nested references and ideals in different parameter positions.
It rejects inconsistent lengths and asks for an explicit value when an ideal
parameter is not determined by an argument type. This is type-based inference,
not a runtime capacity argument or a proof-search guess.

### Inline arrays and runtime-sized planes

`array(T, N)` names inline homogeneous storage and requires a compile-time
integer extent (currently literals, machine constants, and constant `+`, `-`,
`*` expressions). Passing it by value passes its elements. `&array(T, N)` borrows
that inline value. `linear_plane(T, n)` is a pointer type bounded by the value
`n`, which may be a runtime argument. Its address is one machine word; a function
that needs its extent during execution passes the delineator separately.
The older bracket/reference spellings remain accepted during bootstrap.

`plane(T, n)` is the owning pointer form. `alloc(count, initial)` allocates a
runtime-sized plane and initializes each element with the given copyable value;
`alloc(value)` retains its original single-payload meaning. Count is evaluated
before the initial value, and the initial expression executes once. The current
filled allocator supports scalar values and flat scalar records without
references or affine ownership. Repeating an owner or destructor-bearing value
is rejected instead of silently duplicating it.

The checker proves nonnegative extents, index bounds, and that the allocation's
byte size fits the x86-64 target's signed pointer range (`isize::MAX`). Incoming
owned array types carry that addressability bound. The 64 KiB inline-layout limit
applies to each repeated element, not the entire heap buffer. The native implementation uses a bounded initialization loop and a private
eight-byte mapping-size header, allowing cleanup without reevaluating a mutable
length variable. The header is not part of `T`'s layout or the source owner value.
Linux rounds mappings to pages; there is no separate native heap quota. Empty
allocations retain distinct identities and are still releasable. The interpreter
retains its execution/value-work limits and rejects allocations exceeding its
remaining work before reserving host storage.

A formed view keeps its proved extent: assigning a larger value to a length
variable does not enlarge existing storage or justify a formerly out-of-bounds
index. Replacing/freeing its allocation invalidates old references as before.
`examples/runtime_planes.evg` exercises a runtime allocation bound, initialization,
mutation, borrowed views, and returned ownership in both backends without trust.
The full relationship between mutable dependent fields and logical Vec length is
being worked through with the vector implementation; this does not claim support
for uninitialized generic element storage or arbitrary resizing in place.

### Owned machine-word vector

`stdlib/vec/vec.evg` supplies an initial `vec::Vec` with an opaque three-word
representation: capacity, length, and an owning pointer whose extent depends on
capacity. `examples/vec.evg` checks and runs without explicitly supplying library
files:

```sh
cargo run -- run examples/vec.evg
cargo run -- build examples/vec.evg -o /tmp/vec
```

`new(capacity)` allocates initialized `usize` storage; `push(&value, item)` requires
spare capacity, `pop(&value)` requires a nonempty vector, and `get(&value, index)`
returns a checked reference to an element below length. `length` and `capacity`
expose those quantities without exposing the representation. Capacity is bounded
by addressability: `int(capacity) * 8 <= int(isize::MAX)` for machine-word elements.
Native allocation can still fail at runtime; the interpreter has a separate work
budget. Neither imposes a 8192-element language limit.

`value = vec::reallocate(&value, new_capacity)` copies the live prefix to a fresh
allocation and releases the previous buffer on assignment. Existing references
into the released buffer become invalid. Pushes within capacity retain the same
allocation, preserving references to existing cells. Reallocation must accommodate
all live elements; shrinking below length is rejected.

This is a machine-word specialization with explicit reallocation, not yet the
README's generic vector. All capacity slots are initialized copyable values;
uninitialized slots and arbitrary element destructors need further work. The
checker proves access bounds, ownership, and the length/capacity invariant. Prefix
copying is implemented in Evergreen with a checked decreasing measure proving
termination, subject to the bootstrap execution limits. Interpreter/native
comparisons exercise its behavior; its contract does not yet prove preservation
of every copied element. No vector-specific compiler primitive or trusted proof
was added.


### Field autodereferencing

Field access automatically follows built-in references and owning planes until
it reaches a record. `person.age` therefore works for `Person`, `&Person`,
`plane(Person)`, and references to those pointer types. Nested paths such as
`outer.inner.value` follow pointers at each field boundary. No user-defined
`Deref` protocol or automatic method dispatch is introduced.

This is elaborated into explicit `*` expressions before verification. The same
rules apply to reads, assignments, `&person.age`, dependent type extents, and
contracts such as `modifies(&person.age)` or `old(person.age)`. Opaque field
visibility, liveness, ownership, invariant, and effect checks remain mandatory.
The elaboration does not copy or consume an owning pointer merely to access a
field. `examples/field_access.evg` exercises a borrowed update and a field read
through an owner reference.

### File modules and package directories

A file can declare its module once, without wrapping or indenting its contents:

```evg
module arithmetic;

fn answer() -> usize ensures(result == 42) { 42 }
```

All `.evg` files in a package directory share its module. Directory inputs load
those files in deterministic filename order; each file keeps its own module
scope and line numbering. A directory's module must match its directory name,
except that executable packages may declare `module main;`. The entry function
in that package remains `main`, while its other declarations are namespaced.
Namespaced bundled libraries now follow this directory layout as well.

```sh
cargo run -- run examples/packages/arithmetic examples/packages/demo
```

Files in the same module can refer to declarations in other files without
qualification. The compiler schedules types and functions within each package
by dependency, so declaration checking does not depend on filename order.
Self-recursive functions retain the existing termination/safety rules; mutually
recursive declarations and recursive types remain rejected. Root source snippets use the same dependency scheduling. Pass dependency
directories explicitly, or use local imports as described below. Legacy
`module name { ... }` blocks remain accepted for existing source snippets.

The Rust API's `syntax::join_source_units` preserves file boundaries when
combining source strings. Plain string concatenation intentionally does not end
a file module. Proof fingerprints include those boundaries and all bundled
source bytes, so certificate replay checks the same assembled program.


### Local package imports

`import arithmetic;` loads the `arithmetic` directory under the package root.
Imports precede declarations. The root defaults to the working directory and
can be selected explicitly:

```sh
cargo run -- --package-root examples/packages run examples/packages/demo
```

The demo imports its arithmetic dependency automatically; its files can be in
any declaration order. The loader recursively places dependencies before their
clients, deduplicates source files, and rejects import cycles, missing packages,
self-imports, and imports of executable `main` packages. Imported paths must
remain inside the selected root. Dependency bytes and source-unit boundaries
are included in proof fingerprints; editing a dependency invalidates replay.
Output protection also covers imported source files.

Bundled standard-library names are available without filesystem lookup when no
local package supplies that name. Their used declarations retain demand loading
and trust auditing. An unresolved explicit import is an error in the Rust API;
API callers provide local packages with `syntax::join_source_units`.

This first import syntax accepts a single package name, not a remote URL or a
nested path. Package manifests, external dependency fetching, and nested import
paths are not implemented. Loading is bounded by 1 MB of combined local source,
1024 source files, import depth 64, and 4096 directory entries per package. These
are bootstrap compiler resource limits, separate from compiled heap allocation.


`examples/drop_receiver_pattern.evg` demonstrates complete receiver consumption,
stable payload borrows, and a child destructor with a checked effect contract.
It checks and runs without trusted assumptions. Partial/repeated decomposition,
subsequent receiver access, external bypass of Drop, and omitted cleanup effects
are rejected. This enables another generic library operation but does not yet
implement shared owning references or Rc/Arc.


### Explicit Copy and move-by-default values

```evg
type Point struct {x: usize}
impl Copy for Point {}

type Person struct {age: usize}
```

`let duplicate = point;` preserves `point`, while `let moved = person;`
consumes `person`. The same distinction applies to arguments, assignments, and
returns. `examples/copy_and_move.evg` demonstrates both behaviors. Copy must be
implemented in the type's defining module and may not conceal a non-Copy field,
a runtime owner, an affine proof resource, or a destructor. Duplicate and foreign
Copy implementations are rejected. Copy does not execute arbitrary user code;
cloning a resource needs an explicit operation instead.

Borrowed field access does not require Copy. The symbolic array histories may
observe reference-free record fields without duplicating a source-level value;
rvalue access still obeys the record's Copy/move rules. Filled allocation, which
actually duplicates its initializer into multiple slots, requires Copy elements.
Dropping a no-destructor value validates it before invalidating its storage,
without attempting to read its self-referential fields afterward.

This is the checked Copy marker and ownership behavior, not a complete general
trait implementation. Generic traits/bounds, associated items, and default trait
methods remain subsequent work. Partial field moves, moving out of borrowed
places, and branches with different remaining live owners are still rejected
where the bootstrap lacks partial/conditional shape support. Complete record
patterns remain the supported way to extract non-Copy owned fields.

### Methods and implicit self

```evg
type Person struct {age: usize}

impl Person {
    fn new(age: usize) -> Self { Self {age: age} }

    method into_age() -> usize { self.age }

    method& birthday()
    where(self.age < usize::MAX)
    modifies(&self.age)
    ensures(self.age == old(self.age) + 1) {
        self.age = self.age + 1;
    }
}
```

`method` supplies an implicit by-value `self`; the receiver copies if its type
implements Copy and otherwise moves. `method&` supplies `self: &Self`, with the
ordinary reference/effect rules. Receiver arguments are omitted from the source
parameter list. Methods may use `self` in bodies, contracts, return-borrow paths,
and decreasing measures. `Self` names the implementing record, including in
constructors and return types. Ordinary `fn` inside an impl defines an associated
function without a receiver.

Calls such as `person.birthday()` automatically borrow/dereference the receiver
as required. Explicit paths such as `Person::new(...)` and
`people::Person::new(...)` are supported. Inherent impls must be in the record's
defining module. Methods lower to ordinary checked functions before dependency
scheduling; names do not grant field visibility, mutation, or ownership rights.
Arguments, including the receiver, retain normal evaluation order. A consuming
method runs ordinary cleanup for any receiver value it does not return or move.
`impl Drop` also accepts `method drop()`; legacy `fn drop(self)` stays supported.

`examples/methods.evg` demonstrates a constructor, borrowed mutation, proof-time
accessor use, and a consuming method. `examples/vec.evg` uses the Vec method
interface; the existing free functions remain available. Vec's `method&`
reallocation returns a fresh Vec to assign over the old value. Its consuming
`into_data` method transfers the existing allocation using complete receiver
destructuring. `examples/owned_method_transfer.evg` proves that an element
borrow survives this header move and becomes invalid when the new owner frees
that allocation. References to the moved header itself do not survive.

This milestone supports inherent record methods and associated functions.
General traits, associated types/constants, generic impls, primitive-type impls,
and representation-polymorphic patterns are still pending. Runtime reference
methods also accept record constructors, record-returning calls, and conditional
record values as temporary receivers. The receiver is evaluated once and remains alive through the enclosing
statement; cleanup runs afterward in reverse temporary order. Conditional
conditions and branches establish their own temporary scopes, which end before
the conditional result is used outside that scope. A returned loan
can be used within that statement, but using it afterward fails. This includes
temporary Copy records without destructors: their storage still expires.
`examples/temporary_methods.evg` demonstrates this lifetime and destructor
ordering. Temporaries do not receive the extended lifetime of a named binding;
store a value in a local when its borrows must survive later statements.
Specification/ideal temporary borrows, Non-Copy moves through borrowed receivers,
and unsupported partial/conditional shape operations are rejected.

Borrowed record receivers can be used by ownership-free helpers inside updates
and destructors. The effect check distinguishes inspecting a place from moving
its value: field/index projections and borrows do not transfer their enclosing
record or allocation. Evaluated pointer and index expressions must themselves
have checked effects. Calls retain ordinary invariant validation and write
permissions; a whole-record method cannot observe a receiver whose required
invariant is lifted. `examples/update_methods.evg` calls methods on a separate,
valid receiver while the pair's invariant is temporarily lifted.

### Inferred runtime lengths and clause spelling

Calls may omit runtime `usize` parameters that are determined by another
parameter's array extent. For example, `linux_io::print_bytes(&message)` infers
the length from `message`'s array type. This elaborates to an ordinary call with
an ordinary runtime integer; the verifier proves the full dependent signature.
Dynamic planes can use an in-scope runtime extent. Different array extents still
fail the dependent type check, and explicit lengths remain accepted.

Simple `where`, `ensures`, and `decreases` clauses accept expressions with or
without surrounding parentheses. Struct clauses containing named facts retain
the existing parenthesized form. `examples/nonzero.evg` shows checked nonzero
construction and addition with an ideal integer view for the overflow bound.
