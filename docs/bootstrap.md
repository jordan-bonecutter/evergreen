# Evergreen bootstrap

Build with `cargo build`. The executable is `target/debug/evg`.

```sh
cargo run -- emit examples/contracts.evg
cargo run -- check examples/contracts.evg
cargo run -- run examples/contracts.evg
```

At this stage `check` and `run` require the Lean version in `lean-toolchain`.
Install that toolchain with elan, or set `EVG_LEAN` to its `lean` executable.
`emit` prints the generated proof obligations without claiming verification.
`run` checks every declaration before returning evaluation output.

The supported language contains pure typed functions, immutable `let` bindings,
named `fact` declarations, preconditions (`where`), postconditions (`ensures`),
and length-indexed arrays (`[T; n]`). Array access requires a proof of its bound.
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
are errors; proof escape hatches such as `sorry` are unavailable.

`isize` and `usize` currently mean mathematical integers and naturals, not
machine integers. Natural subtraction saturates at zero. This is an explicit
bootstrap semantics, not a claim that overflow has been verified. Logical
operators in propositions are `&&`, `||`, and `!`.

Not yet supported: calls, recursion, mutation, structs, patterns, references,
allocation, FFI, machine layouts, or native code generation. Unsupported syntax
is rejected. No memory safety claim is made for these unimplemented features.

`proofs/Planes.lean` separately specifies plane identity, epochs, invalidation,
aliasing, and publication of invariant-carrying states. It is not connected to
an allocator or the frontend yet. It does not yet model descendant planes,
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

The intended architecture is a Rust parser and elaborator, explicit verification
conditions, an internal proof kernel, and replaceable proof search. Lean is the
first reference backend, rather than part of the intended permanent runtime.
The frontend translation and Lean currently belong to the trust boundary.
Kernel checking proves the generated proposition; it does not by itself prove
the correctness of the translation. Future work must shrink and formalize that
boundary before making systems-level safety claims.
