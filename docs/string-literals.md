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
ordinary array. Later mutation can invalidate UTF-8. A source-defined UTF-8 type
with a validity refinement, construction from ideal values, and the proofs
preserving that refinement remains the next layer; no such invariant is silently
assumed for arbitrary arrays.

[`string_bytes.evg`](../examples/string_bytes.evg) checks Unicode bytes and
extent inference without external calls. [`hello.evg`](../examples/hello.evg)
uses the library's existing trusted Linux syscall boundary for output.
