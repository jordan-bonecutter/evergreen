# String literals

`"Hello, Evergreen\n"` has type `[u8; 17]`. Literals are fixed inline byte
arrays, passed by value or borrowed with `&` using the ordinary array rules.
There is no trailing zero byte, heap allocation, runtime length field, or
compiler-defined string object.

```evg
fn main() -> usize {
    if linux_io::print_bytes(&"Hello, Evergreen\n") == 17 {0} else {1}
}
```

The print function infers the array extent. A literal borrowed directly in a
call lives through that statement. To keep a reference for later statements,
bind the array first, then borrow it. Literal storage is not a static allocation.

Source text and Unicode escapes encode Unicode scalar values as UTF-8. Byte
extents count encoded bytes: `"λ🦀\n"` has seven bytes. Accepted escapes are
`\n`, `\r`, `\t`, `\0`, `\\`, `\"`, ASCII `\xHH`, and `\u{...}` with one
to six hexadecimal digits. Surrogates, values above U+10FFFF, malformed escapes,
and non-ASCII `\xHH` escapes are rejected. Actual newlines in a literal are
preserved, and following diagnostics retain their source line numbers.

Empty literals have type `[u8; 0]`. The interpreter retains element metadata for
empty arrays; native arrays keep their ordinary zero-length layout.

Literal decoding produces valid UTF-8 bytes, but the resulting value is an
ordinary array. Later mutation can invalidate UTF-8. The source-defined ideal
predicate `utf8::valid(&bytes)` now checks literal data by evaluating its verified
definitions. [`utf8_literal.evg`](../examples/utf8_literal.evg) proves a Unicode
literal valid and rejects an overlong encoding. The UTF-8 algorithm lives in
[`stdlib/utf8/utf8.evg`](../stdlib/utf8/utf8.evg), including restricted first
continuations that exclude surrogates and scalars above U+10FFFF.

The generic definition evaluator reads concrete arguments and immutable snapshots
of referenced data. It uses explicit call and expression stacks, charges bounded
work, executes no FFI, and imports the ordinary function safety dependencies.
Unsupported computations or numbers beyond its bootstrap resolution keep using
verified contracts; reduction never wraps ideal arithmetic. Its interpretation
of source definitions remains part of the trusted frontend. Proof replay repeats
that interpretation and checks the resulting arithmetic certificates.

`utf8::Text` is an opaque borrowed view defined in the same source library. Its
runtime fields are a length and a `linear_plane(u8, length)`. Its named
`valid_encoding` refinement requires `valid(data)`; the compiler has no special
UTF-8 type or validation rule.

```evg
fn main() -> usize {
    let bytes = "Hello, λ🦀\n";
    let text = utf8::Text::from_bytes(&bytes);
    proof extent: text.len() == 14;
    if text.byte(13) == 10 {42} else {1}
}
```

The constructor infers the runtime length from the array type. `len()` returns
the byte extent, `bytes()` returns a view borrowed from the original data plane,
and `byte(index)` requires an in-bounds index. Invalid encodings fail the
constructor's precondition. Mutating backing bytes must preserve the live view's
encoding invariant, and dropping its backing plane invalidates the view. These
are ordinary refinement and plane-liveness checks. See
[`utf8_view.evg`](../examples/utf8_view.evg).

Concrete predicate results are memoized by arguments and observed projection
revisions, so repeated validation does not rescan unchanged bytes. A write
changes the key; a cache hit still imports the function's safety dependencies.
Symbolic input still needs a proof or a contract establishing validity. Creating
runtime data from genuinely erased ideal strings and proving transformations on
symbolic UTF-8 data remain future work.

[`string_bytes.evg`](../examples/string_bytes.evg) checks Unicode bytes and
extent inference without external calls. [`hello.evg`](../examples/hello.evg)
uses the library's existing trusted Linux syscall boundary for output.
