use super::*;

#[test]
fn utf8_validity_is_computed_from_library_definitions_and_replayed() {
    let source = include_str!("../../../../examples/utf8_literal.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let wrong = source.replace("!utf8::valid(&invalid)", "utf8::valid(&invalid)");
    assert!(verify(&wrong).is_err());
}

#[test]
fn source_utf8_predicate_matches_scalar_boundaries_and_malformed_sequences() {
    let mut cases = vec![
        Vec::new(),
        b"ordinary ASCII\n".to_vec(),
        "λ🦀\u{10ffff}".as_bytes().to_vec(),
    ];
    for byte in 0..=255 {
        cases.push(vec![byte]);
    }
    cases.extend([
        vec![0xc0, 0x80],
        vec![0xc1, 0xbf],
        vec![0xc2, 0x80],
        vec![0xdf, 0xbf],
        vec![0xe0, 0x9f, 0xbf],
        vec![0xe0, 0xa0, 0x80],
        vec![0xed, 0x9f, 0xbf],
        vec![0xed, 0xa0, 0x80],
        vec![0xef, 0xbf, 0xbf],
        vec![0xf0, 0x8f, 0xbf, 0xbf],
        vec![0xf0, 0x90, 0x80, 0x80],
        vec![0xf4, 0x8f, 0xbf, 0xbf],
        vec![0xf4, 0x90, 0x80, 0x80],
        vec![0xf5, 0x80, 0x80, 0x80],
        vec![0xe2, 0x82],
        vec![0xf0, 0x9f, 0xa6],
        vec![0xc2, 0x7f],
        vec![0xc2, 0xc0],
        vec![0xe0, 0xa0, 0x7f],
        vec![0xe0, 0xa0, 0xc0],
    ]);
    // Bound each caller's proof state; library declarations are checked once
    // per batch, rather than recompiling a program for every possible byte.
    for batch in cases.chunks(64) {
        let mut source = String::from("fn main() -> usize {");
        for (index, bytes) in batch.iter().enumerate() {
            let values = bytes
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(",");
            let not = if std::str::from_utf8(bytes).is_ok() {
                ""
            } else {
                "!"
            };
            source.push_str(&format!("let bytes{index}: [u8; {}] = [{values}]; proof checked{index}: {not}utf8::valid(&bytes{index});", bytes.len()));
        }
        source.push_str("42}");
        let (program, bundle) = prove(&source).unwrap();
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
}

#[test]
fn concrete_ideal_recursion_uses_an_explicit_stack_and_replays() {
    let bytes = "x".repeat(1024);
    let source = format!(
        r#"
        ideal fn count(ideal n: nat, bytes: &[u8; n], index: nat) -> nat
            where index <= n decreases n - index
        {{if index == n {{0}} else {{1 + count(n, bytes, index + 1)}}}}
        ideal fn length(ideal n: nat, bytes: &[u8; n]) -> nat {{count(n, bytes, 0)}}
        fn main() -> usize {{ideal let bytes = "{bytes}"; proof computed: length(&bytes) == 1024; 42}}
    "#
    );
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("== 1024;", "== 1023;")).is_err());
}

#[test]
fn unsupported_reduction_keeps_using_the_verified_contract() {
    let source = "ideal fn echo(n: nat) -> nat ensures result == n {let view = &n; *view} fn main() -> usize {proof computed: echo(42) == 42; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn ideal_definition_work_is_bounded_before_the_host_stack_is_involved() {
    let source = "ideal fn count(n: nat) -> nat decreases n {if n == 0 {0} else {count(n - 1)}} fn main() -> usize {proof computed: count(100000) == 0; 42}";
    let error = verify(source).unwrap_err();
    assert!(
        error.contains("ideal definition evaluation frame limit"),
        "{error}"
    );
}

#[test]
fn reduced_calls_preserve_safety_admissions_without_global_explosion() {
    let source = "ideal fn require42(n: usize) where n == 42 {} ideal fn assumed(n: usize) -> bool {proof assumed: n == 42 by {trustme}; require42(n); true} fn main() -> usize {proof computed: assumed(43); 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        1
    );
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bad = source.replace(
        "proof computed: assumed(43);",
        "proof computed: assumed(43); proof unrelated: false;",
    );
    assert!(verify(&bad).is_err());
}

#[test]
fn pure_ideal_state_and_old_values_remain_distinct() {
    let source = "ideal fn difference(n: nat) -> nat {n = n + 1; n - old(n)} fn main() -> usize {proof computed: difference(41) == 1; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
