use super::*;

#[test]
fn opaque_range_claims_over_empty_domains_need_no_slot_observations() {
    let source = "fn empty(data: &[unique(usize) | shape(unique(usize)); 0]) {proof vacuous: forall(i: integer) where(0 <= i && i < 0) {typeof((*data)[i]) == unique(usize)} by {intro i; omega};} fn main() -> usize {42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let nonempty = source.replace("; 0]", "; 1]").replace("i < 0", "i < 1");
    assert!(verify(&nonempty).is_err());
}

#[test]
fn unknown_input_ranges_forward_checked_premises_and_replay() {
    let source = include_str!("../../../../examples/input_ranges.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let initialized = source.replace("let view =", "(*data)[0] = alloc(7); let view =");
    let error = verify(&initialized).unwrap_err();
    assert!(error.contains("precondition"), "{error}");
}

#[test]
fn opaque_input_selectors_do_not_invent_empty_defaults_or_other_planes() {
    for source in [
        "fn bad(data: &[unique(usize) | shape(unique(usize)); 8]) {proof invented: forall(i: integer) where(0 <= i && i < 8) {typeof((*data)[i]) == shape(unique(usize))} by {intro i; omega};}",
        "fn bad(data: &[unique(usize) | shape(unique(usize)); 8]) where(forall(i: integer) where(0 <= i && i < 8) {typeof((*data)[i]) == shape(unique(usize))}) {proof wrong: forall(i: integer) where(0 <= i && i < 8) {typeof((*data)[i]) == unique(usize)} by {intro i; omega};}",
        "fn bad(a: &[unique(usize) | shape(unique(usize)); 8], b: &[unique(usize) | shape(unique(usize)); 8]) where(forall(i: integer) where(0 <= i && i < 8) {typeof((*a)[i]) == shape(unique(usize))}) ensures(forall(i: integer) where(0 <= i && i < 8) {typeof((*b)[i]) == shape(unique(usize))}) {}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("predicate"), "{error}");
    }
}

#[test]
fn opaque_input_range_contracts_remain_sparse_at_a_billion_elements() {
    let small = include_str!("../../../../examples/input_ranges.evg");
    let huge = small.replace('8', "1000000000");
    let (program, bundle) = prove(small).unwrap();
    let (large, large_bundle) = prove(&huge).unwrap();
    assert_eq!(program.obligations, large.obligations);
    assert_eq!(bundle.certificate_count(), large_bundle.certificate_count());
    assert_eq!(
        verify_with_certificate(&huge, &large_bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 16384);
    assert!(large.run().unwrap_err().contains("before allocation"));
}
