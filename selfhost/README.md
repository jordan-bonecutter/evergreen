# Evergreen compiler components

This is the start of an Evergreen implementation of compiler components. The
Rust compiler remains the compiler and proof checker used to build this code.

The lexer currently scans ASCII identifiers, decimal integers, whitespace, and
punctuation, including `::`, `->`, `<=`, `>=`, `==`, `=>`, `!=`, `&&`, `||`, and
`<=>`. Longer operators take precedence over their prefixes. Tokens are source
byte spans with a numeric category;
unsupported bytes produce an error token, and EOF has an empty span. Strings,
comments, Unicode whitespace, and diagnostics are still
missing. This lexer is not yet interchangeable with the Rust lexer.

`lexer::next` proves that each span stays inside the source and that every
non-EOF result advances. Its scan has a checked termination measure. These
contracts prove memory bounds and progress, not full lexical correctness.
The smoke program checks all compound operators, their token endpoints, and a
lone `<` at the end of input. The expectation helper is checked separately from
the scanning loop, keeping its test table out of the loop's proof state.

From the repository root:

```sh
cargo run -- run --deny-trust --package-root selfhost selfhost/main.evg
cargo run -- build --deny-trust --package-root selfhost selfhost/main.evg -o /tmp/evergreen-lexer
```

The smoke program returns 42 on success. The native executable therefore exits
with status 42.

`lexer::tokenize` builds a `vec::Vec<Token>` in a verified loop, with at most one
token per source byte. Its declaration verifies, but composing its call with
subsequent token inspection currently exceeds the verifier's unchanged path-processing work
budget. The runnable smoke program scans incrementally while that modular
verification cost is addressed. The `examples/vec_loop.evg` example separately
exercises native Vec pushes in a loop.

Next steps are making token collection practical across function boundaries,
completing lexical coverage, and using named variant patterns for token kinds.
Parsing and checking in Evergreen have not started yet.
