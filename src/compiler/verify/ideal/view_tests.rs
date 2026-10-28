//! UTF-8 is a source-library refinement over borrowed ordinary bytes.

use crate::syntax::format::test_edit::SourceEdit;

use super::*;

#[test]
fn utf8_views_preserve_encoding_extent_provenance_and_replay() {
    for source in [
        include_str!("../../../../examples/utf8_view.evg"),
        r#"fn main() -> usize {let bytes = ""; let text = utf8::Text::from_bytes(&bytes); proof empty: text.len() == 0; let view = text.bytes(); 42}"#,
        r#"fn main() -> usize {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); bytes[0] = 98; if text.byte(0) == 98 {42} else {1}}"#,
        r#"fn main() -> usize {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); drop(text); bytes[0] = 255; 42}"#,
        r#"fn main() -> usize {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); let view = text.bytes(); drop(text); proof valid: utf8::valid(view); if (*view)[0] == 97 {42} else {1}}"#,
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
}

#[test]
fn utf8_views_reject_invalid_construction_mutation_and_dangling_storage() {
    for source in [
        "fn main() {let bytes: [u8; 2] = [192, 128]; let text = utf8::Text::from_bytes(&bytes);}",
        r#"fn main() {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); bytes[0] = 255;}"#,
        r#"fn main() {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); drop(bytes); let byte = text.byte(0);}"#,
        r#"fn main() {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); let byte = text.byte(1);}"#,
        r#"fn main() {let bytes = "a"; let text = utf8::Text {length: 1, data: &bytes};}"#,
        r#"fn main() {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); let view = text.data;}"#,
        r#"fn main() {let text = utf8::Text::from_bytes(&"a"); let byte = text.byte(0);}"#,
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn repeated_refinement_validation_reuses_bounded_concrete_computation() {
    let bytes = "x".repeat(1024);
    let source = format!(
        r#"fn main() -> usize {{let bytes = "{bytes}"; let text = utf8::Text::from_bytes(&bytes); proof extent: text.len() == 1024; let view = text.bytes(); proof first: (*view)[0] == 120; 42}}"#
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
}

#[test]
fn computed_predicates_do_not_survive_a_pointee_write() {
    let source = "ideal fn valid(value: &usize) -> bool {*value == 42} fn main() -> usize {let value: usize = 42; proof first: valid(&value); value = 43; proof changed: !valid(&value); 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace_evg("!valid(&value)", "valid(&value)")).is_err());
}

#[test]
fn cached_computations_still_import_safety_admissions_at_every_call() {
    let source = "ideal fn need(n: usize) where n == 42 {} ideal fn valid(n: usize) -> bool {proof assumed: n == 42 by {trustme}; need(n); true} fn main() -> usize {proof first: valid(43); proof second: valid(43); 42}";
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
    assert!(verify(&source.replace_evg(
        "proof second: valid(43);",
        "proof second: valid(43); proof unrelated: false;"
    ))
    .is_err());
}

#[test]
fn symbolic_integer_applications_reuse_values_for_the_same_observation() {
    let source = "ideal fn value(n: integer) -> integer {n + 1} ideal fn observe(p: &usize) -> integer {integer(*p)} ideal fn same(n: integer) {proof _: value(n) == value(n);} fn check(p: &usize) {proof _: observe(p) == observe(p);} fn main() -> usize {let n: usize = 42; check(&n); 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let changed = "ideal fn observe(p: &usize) -> integer {integer(*p)} fn check(p: &usize) modifies(p) {ideal let before = observe(p); *p = 43; proof _: before == observe(p);}";
    assert!(verify(changed).is_err());
    let changed_scalar = "ideal fn value(n: usize) -> integer {integer(n) + 1} fn check(n: usize) {ideal let before = value(n); n = 43; proof _: before == value(n);}";
    assert!(verify(changed_scalar).is_err());
}

#[test]
fn numeric_computation_caches_keep_trust_and_pointee_generations_visible() {
    let source = "ideal fn needs(n: usize) where n == 42 {} ideal fn observe(n: usize) -> integer {proof admitted: n == 42 by {trustme}; needs(n); integer(n)} fn main() -> usize {ideal let first = observe(43); ideal let second = observe(43); proof _: first == second; 42}";
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
    let stale = "ideal fn observe(p: &usize) -> integer {integer(*p)} fn main() {let n: usize = 42; ideal let before = observe(&n); drop(n); ideal let after = observe(&n);}";
    assert!(verify(stale).is_err());
}

#[test]
fn concrete_bounded_ideal_results_remain_valid_across_branch_restoration() {
    let source = "ideal fn byte() -> u8 {42} ideal fn natural() -> nat {42} fn checks(flag: bool) {if flag {proof _: byte() == 42; proof _: natural() == 42;} else {proof _: byte() == 42; proof _: natural() == 42;}}";
    let (program, bundle) = prove(source).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
