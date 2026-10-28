use super::*;

#[test]
fn quantified_payload_equalities_keep_indices_visible_to_congruence() {
    for source in [
        "fn check(data: &[u8; 8]) {proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == (*data)[i]} by {intro i; omega};} fn main() -> usize {42}",
        "fn check(data: &[u8; 8]) {proof _: forall(i: integer) where(0 <= i && i < 8) {forall(j: integer) where(j == i) {(*data)[i] == (*data)[j]}} by {intro i; intro j; omega};} fn main() -> usize {42}",
        "fn main() -> usize {let data: [u8; 3] = [7, 7, 7]; proof _: forall(i: integer) where(0 <= i && i < 3) {data[i] == 7} by {intro i; omega}; 42}",
        "fn main() -> usize {let data: unique(u8, 8) = alloc(8, 7); proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7} by {intro i; omega}; 42}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn quantified_payload_equalities_reject_unknown_values_and_distinct_contents() {
    for body in [
        "(*data)[i] == 7",
        "(*data)[i] == (*other)[i]",
        "(*data)[i] == (*data)[7 - i]",
        "(*data)[i] != (*data)[i]",
    ] {
        let source = format!("fn check(data: &[u8; 8], other: &[u8; 8]) {{proof _: forall(i: integer) where(0 <= i && i < 8) {{{body}}} by {{intro i; omega}};}}");
        let error = verify(&source).unwrap_err();
        assert!(
            error.contains("predicate atoms require logical proof rules"),
            "{source}\n{error}"
        );
    }
    // Declaring a false proposition is allowed; only a proof asserts its truth.
    verify("fn main() {let data: [usize; 2] = [7, 9]; fact bad = forall(i: integer) where(0 <= i && i < 2) {data[i] == 7};}").unwrap();
}

#[test]
fn quantified_payload_reads_require_bounds_even_for_reflexivity_or_admission() {
    for domain in ["true", "0 <= i && i <= 8", "-1 <= i && i < 8"] {
        for proof in ["intro i; omega", "trustme"] {
            let source = format!("fn check(data: &[u8; 8]) {{proof _: forall(i: integer) where({domain}) {{(*data)[i] == (*data)[i]}} by {{{proof}}};}}");
            let error = verify(&source).unwrap_err();
            assert!(
                error.contains("quantified array index bounds"),
                "{source}\n{error}"
            );
        }
    }
    let error = verify(
        "fn check(data: &[u8; 8]) {fact bad = forall(i: integer) {(*data)[i] == (*data)[i]};}",
    )
    .unwrap_err();
    assert!(error.contains("quantified array index bounds"), "{error}");
}

#[test]
fn quantified_payload_reads_preserve_their_element_types() {
    for source in [
        "fn check(data: &[u8; 8]) {proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 256} by {trustme};}",
        "fn check(data: &[u8; 8], other: &[u16; 8]) {proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == (*other)[i]} by {trustme};}",
        "fn check(data: &[shape(usize); 8]) {proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == (*data)[i]} by {trustme};}",
    ] {
        assert!(verify(source).is_err(), "{source}");
    }
}

#[test]
fn quantified_payload_writes_do_not_keep_uniform_contents_or_admitted_revisions() {
    for construction in [
        "let data: [u8; 3] = [7, 7, 7];",
        "let allocation: unique(u8, 3) = alloc(3, 7); let data = &*allocation;",
    ] {
        let place = if construction.contains("allocation") {
            "(*data)"
        } else {
            "data"
        };
        let source = format!("fn main() {{ {construction} {place}[1] = 9; proof _: forall(i: integer) where(0 <= i && i < 3) {{{place}[i] == 7}} by {{intro i; omega}}; }}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("cannot prove"), "{source}\n{error}");
    }
    let before = "fn check(data: &[u8; 8]) modifies(&(*data)[0]) {proof external: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == 7} by {trustme}; proof again: forall(j: integer) where(0 <= j && j < 8) {(*data)[j] == 7} by {exact external};}";
    let (program, bundle) = prove(before).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(before, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for value in ["7", "9"] {
        let stale = before.replace(
            "proof again:",
            &format!("(*data)[0] = {value}; proof again:"),
        );
        let error = verify(&stale).unwrap_err();
        assert!(error.contains("earlier state"), "{stale}\n{error}");
    }
}

#[test]
fn quantified_payload_fill_captures_the_initial_value_not_its_current_binding() {
    let source = "fn check(initial: u8) {let saved = initial; let data: unique(u8, 8) = alloc(8, initial); initial = 9; proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == saved} by {intro i; omega};} fn main() -> usize {check(7); 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let bad = source.replace("== saved", "== initial");
    assert!(verify(&bad).is_err());
}

#[test]
fn quantified_payload_equalities_scale_with_observations_not_array_extent() {
    let large = include_str!("../../../../examples/quantified_array_values.evg");
    let small = large.replace("1000000000", "8");
    let (program, bundle) = prove(large).unwrap();
    let (small_program, small_bundle) = prove(&small).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(program.obligations, small_program.obligations);
    assert_eq!(bundle.certificate_count(), small_bundle.certificate_count());
    assert_eq!(
        verify_with_certificate(large, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&program).unwrap().len() < 16384);
}

#[test]
fn quantified_payload_equalities_preserve_nested_binding_and_specialization() {
    let source = "fn check(data: &[u8; 8]) {proof all: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == (*data)[i]} by {intro i; omega}; proof restricted: forall(j: integer) where(2 <= j && j < 5) {(*data)[j] == (*data)[j]} by {intro j; specialize all(j); omega}; proof shadowed: forall(i: integer) where(i == -1) {forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == (*data)[i]}} by {intro outer; intro inner; omega};} fn main() -> usize {let data: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8]; check(&data); 42}";
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

#[test]
fn quantified_payload_fills_do_not_resolve_unspecified_overflow() {
    let source = "fn main() -> usize {let value = usize::MAX + 1; let data: unique(usize, 8) = alloc(8, value); proof _: forall(i: integer) where(0 <= i && i < 8) {(*data)[i] == value} by {intro i; omega}; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for unsupported in ["0", "usize::MAX", "usize::MAX + 1"] {
        let bad = source.replace("== value", &format!("== {unsupported}"));
        assert!(verify(&bad).is_err(), "{bad}");
    }
}
