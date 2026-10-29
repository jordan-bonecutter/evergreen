# WebAssembly target

```sh
cargo run -- build examples/console.evg --target wasm32 -o /tmp/console.wasm
```

`--target wasm32-unknown-unknown` and `--target wasm` are aliases. The default
target remains Linux x86-64. Without `-o`, Wasm builds replace `.evg` with `.wasm`.
Verification and certificate replay happen before emission, and a failed build
preserves the existing output file. `--deny-trust` applies to both targets.

This initial backend supports machine integers, Boolean/unit values, functions
with scalar results, conditionals, arithmetic and comparisons, local scalar
arrays, borrowed references, assignments, and invariant-checked loops.
Proofs, ideal bindings, and contracts are erased after verification.
Records with scalar fields and no destructor, including constructor results,
by-value parameters, and local arrays of those records, are supported. This also
covers named scalar refinements such as `type NonZero usize where self != 0;`.
Owning pointers, raw unions, by-value array parameters and array results,
reference results, Linux syscalls, and atomics are currently rejected with target
diagnostics. Compilation checks all runtime declarations, including unused ones.

The bootstrap retains its existing 64-bit scalar/layout model: `usize` is u64,
`isize` is i64, and stored references occupy eight bytes. The module uses wasm32
linear-memory addresses extended to i64. This is an Evergreen ABI, not the C ABI
or WASI. A distinct 32-bit language layout profile remains future work.

Modules export `main() -> i64` and `memory`. Boolean results are 0/1 and unit is
0. Interpret unsigned results with `BigInt.asUintN(64, value)` in JavaScript.
The module has 4 MiB of memory, a 64 KiB limit per function frame, a 128-call
depth limit, and a shared budget of 100,000 function calls/loop iterations.
Exhausting a limit traps. Instantiate a fresh module for each execution.

## Portable console

```evg
fn main() -> usize {
    console::println(&"Hello, Evergreen!");
    42
}
```

`console::print` writes the supplied byte array; `console::println` adds a newline.
Both infer the length from the borrow. These functions also work in native builds
and `evg run`. The interpreter API `run_with_output` returns `(Value, Vec<u8>)`;
the older `run` and `run_with_events` APIs discard captured console bytes.

Wasm imports `evergreen.console_write(length: i64, pointer: i64) -> i64`.
The host reads exactly `length` bytes from exported memory and returns 0 (unit).
The stdlib declares this boundary using explicit `proof {trustme}`. The verifier
checks its signature and use; it does not prove host behavior. The supplied host
checks bounds and caps output, then decodes collected bytes as UTF-8 with replacement
for invalid sequences. See [runtime.js](../web/public/runtime.js) for a reusable host.

The native implementation writes to stdout with Linux `write`. The console API
is best effort and returns unit; use `linux_io` when syscall results matter.

## Compiler in the browser

The Rust compiler itself also builds for `wasm32-unknown-unknown`, without the
CLI feature or an OS thread requirement. `web/compiler` provides a small buffer
ABI around the same verifier and Wasm emitter. Its linker reserves a 16 MiB
stack, matching native verifier workers. See [website development](../web/README.md).
