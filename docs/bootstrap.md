# Evergreen bootstrap

Build with `cargo build`. The executable is `target/debug/evg`.

```sh
cargo run -- emit examples/contracts.evg
cargo run -- check examples/contracts.evg
cargo run -- run examples/contracts.evg
```

`check` and `run` use the internal certificate checker and need no external
tools or downloads. `run` checks every declaration before evaluating `main`.
The optional `lean-check` and `lean-run` commands use the Lean version in
`lean-toolchain`; set `EVG_LEAN` to its executable if necessary. `emit` prints
Lean source without claiming verification. The Lean frontend currently covers
the original smaller subset and rejects calls and branching.

The supported language contains pure typed functions, immutable `let` bindings,
named `fact` declarations, preconditions (`where`), postconditions (`ensures`),
length-indexed arrays (`[T; n]`), array literals, calls to earlier verified
functions, and conditional expressions. Array access requires a proof of its bound.
Nominal structs support dependent fields and `where` invariants. Construction,
field assignment, and whole-value replacement must establish those invariants.
Nested struct invariants are rechecked after updates. Postconditions refer to
the entry values of parameters, even when the function reassigns its locals.
Unknown obligations fail verification. Facts cannot introduce assumptions:
each fact must itself have a proof. Only function preconditions are assumptions,
and are universally quantified in the function's type.

```evg
fn increment(n: usize) -> usize ensures (result > n) {
    fact grows = n + 1 > n by { omega };
    n + 1
} proof { omega }
```

The initial proof vocabulary is `omega`, `rfl`, `simp_all`, `decide`,
`assumption`, and `exact local_name`, separated by semicolons. The default is
`omega`. Arbitrary Lean source and unproven axioms are not accepted. Lean warnings
are errors; proof escape hatches such as `sorry` are unavailable. In the internal
backend these steps are proof-search hints: the arithmetic checker must still
prove the obligation, and `exact` must name an already proven fact. They are not
yet an implementation of Lean's tactic semantics.

`isize` and `usize` currently mean mathematical integers and naturals, not
machine integers. Natural subtraction saturates at zero. This is an explicit
bootstrap semantics, not a claim that overflow has been verified. Logical
operators in propositions are `&&`, `||`, and `!`.

References use `&place`, dereference uses `*reference`, and reference types use
`&T`. Multiple mutable aliases are allowed. Scalar writes preserve identity and
are visible through all aliases. Replacing an aggregate, `move(place)`, or
`drop(place)` invalidates references to its plane. Reassignment restores a moved
slot without restoring old references. References into structs and known array
elements are supported. Moves are currently explicit; ordinary values copy.

The initial implementation conservatively treats an aggregate's storage as one
plane, so replacing a nested aggregate may invalidate unrelated references in
the same root. Symbolic-index reference projections, partial moves, reference
returns, and writes through reference parameters are rejected until their plane
and effect contracts are implemented. Read-only reference parameters work.

Not yet supported: recursion, patterns,
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
