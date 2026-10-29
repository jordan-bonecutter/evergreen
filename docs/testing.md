# Testing scope and audit

For everyday changes, run the affected test group with two build jobs and two
runner threads. Do not automatically follow a passing focused check with the
whole suite. Broaden validation when the change crosses a boundary, a failure
reveals another affected subsystem, or a release needs broader confidence.

```sh
cargo test --locked --offline -j 2 --lib compiler::generics::tests -- --test-threads=2
```

A regression should protect observable language behavior or a safety boundary.
Prefer extending the relevant existing test over creating another test harness.
Avoid assertions that merely duplicate the implementation's steps.

## Initial audit: refinement and generic matrices

The refinement matrix used to verify, execute, replay certificates, and emit
native code for every positive case. It now verifies and executes each case,
with one representative certificate replay. Native execution remains covered by
the backend suite.

The vector-specialization and generic-method matrices each replayed all six
positive cases. Each now replays one representative case while retaining all
six verification and execution checks. This removes ten redundant replay runs;
it does not remove invalid-program checks or change the accepted language.

## Checks that remain distinct

- Verification rejection tests protect soundness boundaries and malformed input.
- Certificate replay tests exercise proof transport; forgery tests exercise the
  kernel's refusal to accept invalid certificates.
- Interpreter and native/Wasm execution test different implementations. Identical
  source is useful when checking that those implementations agree.
- CLI tests exercise subprocess behavior, filesystem outputs, and operation
  without external proof tools. They are not equivalent to direct library calls.

This is an initial audit, not a claim that the rest of the suite is minimal.
Further consolidation should identify the boundary each test protects before
removing it. Large source lists alone do not establish redundant coverage.
