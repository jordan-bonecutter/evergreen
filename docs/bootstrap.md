# Evergreen bootstrap

Build with `cargo build`. The executable is `target/debug/evg`.
The CLI uses Clap; the language frontend, verifier, kernel, and evaluator have
no third-party runtime dependencies. `evg --help` describes available commands.

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
nonrecursive mathematical ghost functions and vectors. `lean-run` evaluates a
ghost reference model inside Lean; it is not Evergreen runtime execution.

The supported language contains typed functions, local `let` bindings,
named `fact` declarations, preconditions (`where`), postconditions (`ensures`),
length-indexed arrays (`[T; n]`), array literals, calls to earlier verified
functions, and conditional expressions. Array access requires a proof of its bound.
Nominal structs support dependent fields and `where` invariants. Construction
and field assignments must establish those invariants. `update (place, ...)`
explicitly opens the invariants of named local struct places. Its body allows
checked scalar-field writes, local scalar values/borrows, and pure facts; each
invariant must hold again on exit. Calls with a checked invariant-independent
effect summary are permitted. The current effect analysis accepts scalar values
and read-only borrows of scalar storage, with scalar returns, no allocation or
cleanup effects, and no access to a whole refined object. Summaries compose
through previously checked helpers. `examples/update_helpers.evg` demonstrates
this distinction: `&pair.left` and a read-only scalar helper work while `&pair`
and a whole-object observer cannot rely on the open invariant. Unknown effects,
allocation, moves, drops, early exits, and suspension remain rejected. Borrow
locals are scoped to the update. Owned fields cannot be replaced. Opening
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

The initial proof vocabulary is `omega`, `rfl`, `simp_all`, `decide`,
`assumption`, and `exact proof_name`. The default is
`omega`. Arbitrary Lean source and unproven axioms are not accepted. Lean warnings
are errors; proof escape hatches such as `sorry` are unavailable. In the internal
backend the search tactics currently use the bounded arithmetic prover rather
than implementing Lean's individual tactic semantics. `exact proof_name` is a
checked proof reference: the named witness must prove the same normalized
proposition, not merely another true statement. A fact name denotes its
proposition in proof code, never a runtime boolean. Local fact definitions are
re-evaluated against the current places; an old witness cannot certify a changed
state. `examples/named_facts.evg` includes an unused false fact and actual proof
reuse; `examples/reject_false_proof.evg` rejects a false proof. Exported and
parameterized proposition declarations are not implemented yet.

The bootstrap target is 64-bit: `usize` is `u64`, and `isize` is `i64`.
Explicit `u8`, `u16`, `u32`, `u64`, `i8`, `i16`, `i32`, and `i64` types are
supported. Every machine arithmetic result must be proved within its type's
bounds. There is no implicit wrapping. `T::MIN` and `T::MAX` denote bounds.
For example, `fn increment(n: usize) -> usize { n + 1 }` is rejected; adding
`where (n < usize::MAX)` supplies the required proof assumption. Negating a
signed minimum is rejected as well.

`int` and `nat` are proof-only mathematical integers and naturals. They may occur
in `ghost fn` and `ghost type` definitions and proof expressions, but cannot be
stored in executable variables, structs, or function interfaces. Ghost functions
cannot be called by runtime expressions; all fact/proof declarations and
contracts are erased. `nat(value)` and `int(value)` provide mathematical views
in proof code; the natural view requires nonnegativity. Entry conditions of
`main` are proved before execution, so ghost predicates are never run by the
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
add preconditions. The first subset permits local scalar work and facts, but
rejects calls, borrowing, allocation, and moving/replacing owned fields; these
need explicit effect and cleanup proofs. `examples/drop.evg` checks a refined
parent that owns a resource with its own destructor. The debug API
`run_with_events()` returns a detached result snapshot and destructor trace.

The initial implementation conservatively treats an aggregate's storage as one
plane, so replacing a nested aggregate may invalidate unrelated references in
the same root. Symbolic-index reference projections, partial moves, reference
returns, and writes through reference parameters are rejected until their plane
and effect contracts are implemented. Read-only reference parameters work.

Self recursion requires `decreases (measure)` after the postcondition. The
measure must be an integer proved nonnegative; every recursive call must prove that its value
is strictly smaller than the entry measure. The callee contract is available
only under this well-founded induction rule. Recursive calls in specifications
are rejected. Mutual recursion is not implemented yet.

Not yet supported: patterns,
allocation, FFI, machine layouts, or native code generation. Unsupported syntax
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
```

The external integration suite checks valid programs, false contracts,
unproven array accesses, and the plane specification. Missing Lean is an error,
never a successful verification.

## Direction

The internal pipeline is syntax → symbolic elaboration → verification
conditions → certificate search → independent certificate checking. The small
checker in `src/kernel.rs` accepts nonnegative weighted sums of integer linear
inequalities that establish a contradiction. Proof search uses bounded
Fourier–Motzkin elimination. Search failure, overflow, and resource limits all
fail verification. Integer strict inequalities are normalized with a unit gap.
The solver is incomplete for general integer arithmetic and rejects nonlinear
products of symbolic values. Boolean conditions split into at most 64 paths;
search is limited to 2,048 constraints and 64 elimination steps.

The parser, type elaborator, condition generator, certificate checker, and
evaluator remain trusted Rust code. The kernel is not a full dependent type
theory yet. There is no theorem of compiler correctness. Arithmetic is
mathematical in verification; the reference evaluator uses checked i128 and
reports an error for values beyond its range. It never wraps silently.
Execution has a 100,000-step budget and 128-call depth limit.

Lean remains an optional reference backend and specification tool. The intent
is to grow the internal proof language toward dependent types and explicit
derivations while keeping search outside the kernel.

## RC proof experiment

`cargo run -- check proofs/rc_protocol.evg` verifies an ordinary Evergreen model
of reserve, publish, retire, decrement, retain, and release. The stored-count
model is bounded by the target's maximum count. Its arithmetic safety condition
`count >= owners` is checked at intermediate program points; the stronger
`count == owners + credits` relation is restored when each generic update closes.
Zero count implies zero owners and credits. There are no RC intrinsics or
special type names in this implementation.

This is a protocol model, not an RC library implementation or a memory-safety
theorem. Its owners and credits are mathematical numbers, not unforgeable
capabilities. Connecting that arithmetic to unique ownership witnesses,
physical heap steps, borrowing, and destruction is still necessary. The
compiler must provide general rules for those concepts rather than RC policy.
The unbalanced update in `proofs/reject_rc_unbalanced.evg` and reusing a single
credit twice both fail verification. Ghost erasure and restricting mathematical
types to proof code are implemented with explicit ghost declarations. Connecting
the model to linear capabilities and physical heap ownership remains planned.
