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
fact_name, ... { ... }` explicitly opens selected named requirements on local
struct places. Other requirements remain checked at every write. Type-local
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
elements are supported. Moves are currently explicit; ordinary values copy.
Types with `impl Drop for T` (and aggregates containing them) move implicitly
when used by value. Their source slot becomes `shape(T)` and cannot be read.
Assignments restore that slot. Overwriting a live owner runs its destructor;
scope cleanup runs in reverse binding order, with owned fields cleaned after
the parent destructor. Partial moves and overwriting owners through borrowed
references remain rejected until their cleanup/effect rules are implemented.

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

Receiver invariants must remain valid while their body runs. Record construction,
destructuring, ownership transfer, and explicit nested cleanup remain unsupported
in Drop bodies. The invariant-update rules are unchanged. `Drop` postconditions
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

Not yet supported: non-record patterns, heap allocation, FFI, foreign aggregate
layouts. Unsupported syntax
is rejected. No memory safety claim is made for these unimplemented features.

`src/memory.rs` provides the internal generation-checked plane store used by
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
checker in `src/kernel.rs` accepts nonnegative weighted sums of integer linear
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
such as a future foreign function's contract. A false trusted assumption can
invalidate every subsequent safety conclusion. It does not construct runtime
values or implement FFI. Named facts alone still introduce no assumptions.

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

`affine type Permit struct {tag: usize}` declares a move-only value without
requiring `impl Drop`. `ideal affine type Ticket struct {tag: nat}` applies the
same ownership rule to erased proof data. Passing or assigning such a value
moves it and leaves the old binding as `shape(T)`. Enclosing records and arrays
are affine too. Scalar field inspection borrows the existing storage; moving
individual owned fields still requires partial-initialization support.
Values may be discarded, so this is affine rather than linear ownership.
Existing types with destructors continue to be affine automatically.

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

Destructuring a type with its own `Drop` implementation is rejected because it
would bypass that destructor. Fields with their own destructors are supported
when the parent has none; tests check each runs exactly once. Patterns inside
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

`stdlib/array.evg` provides `arrays::set`, `arrays::swap`, and
`arrays::replace_pair` in Evergreen. `swap` accepts equal indices because both
places share one incoming array's alias model. Run the example with
`evg run stdlib/array.evg examples/array_updates.evg`; the same ordered unit
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
write contracts are supported. Scalar and reference locals currently occupy
eight-byte homes; this internal convention is not an aggregate or foreign ABI.
Reference returns remain rejected by the source checker.

```sh
cargo run -- --deny-trust build stdlib/counter.evg examples/counter.evg -o /tmp/counter
cargo run -- --deny-trust build proofs/rc_protocol.evg stdlib/counter.evg proofs/rc_count_refinement.evg examples/rc_count.evg -o /tmp/count-refinement
```

The counter executable exits with status 42. The count-refinement executable
performs the checked sequential reserve/release stores and exits with status 0.
Native differential tests include these programs, scalar alias writes, nested
references, and Boolean updates.

The internal word ABI gives each scalar, reference, or empty value an eight-byte
home. Record homes follow declaration order; fixed arrays contain consecutive
element homes. Inline aggregate layouts must be constant and at most 64 KiB;
ideal, recursive inline, overflowing, and dependent layouts are rejected. Constant
natural length arithmetic follows the frontend's truncated subtraction rules.

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

`arrays::set_get` in `stdlib/array.evg` updates one cell and returns its reference.
`evg run stdlib/array.evg examples/write_borrows.evg` exercises forwarding that
contract, existing aliases, and later same-layout replacement. An index rebound
inside the function cannot retarget its entry alias contract.

Owning records can return inline reference fields with an exact mapping for each
field, for example `borrows(target: target)` or
`borrows(release.count: (*handle).release.count)`. Paths on the left name fields
of the returned record; expressions on the right name incoming references.
Every reference field needs exactly one mapping. Calls preserve those actual
planes rather than inventing reference storage. Dependent field extents and
record invariants are checked on the returned value, including after local
cleanup, before callers may rely on them. Moving the returned record does not
extend the lifetime of its borrowed storage.

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
exported. Calls still require an earlier checked function declaration.

`opaque` hides construction, field reads/writes, field borrows, and destructuring
from other modules. It requires a defining module. `affine` separately prevents
implicit duplication. Values can still be passed, moved, borrowed as a whole,
and used through checked functions. Public named type facts remain available.
Function contracts are checked and instantiated in their defining scope; a
callee's representation access never grants that access to caller expressions.
Drop implementations must belong to the type's defining module. Identifiers
have a 256-byte bootstrap limit.

`stdlib/credits.evg` is an opaque affine quantity library with no public mint
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
`stdlib/credits.evg proofs/opaque_credits.evg` succeeds, while checking
`stdlib/credits.evg examples/reject_forged_credit.evg` rejects client construction.
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

`stdlib/borrow_credits.evg` binds existing credits to a live reference. Its opaque
affine tokens split and join while conserving quantity and preserving the exact
target. Joining requires equal target identities. Check the client with:

```sh
evg --deny-trust check stdlib/credits.evg stdlib/borrow_credits.evg proofs/borrow_credits.evg
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
their structural fields and array cells. The target must belong to an ideal
binding or to an ideal function's local storage. Dereferencing a borrowed target
in an ideal assignment is rejected: an erased store must not change a runtime
pointee. Updating an ideal copy of a runtime array changes only the proof copy.
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
`stdlib/credits.evg proofs/ideal_credit_bindings.evg` for a runtime function that
splits an existing ideal budget and consumes each part once through erased
parameters. The shipped library still has no mint operation. The optional Lean
backend evaluates these local bindings as mathematical data in its ideal
reference model, while Evergreen's runtime backends erase them.

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
