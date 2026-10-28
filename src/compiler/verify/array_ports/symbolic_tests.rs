use super::tests::check;
use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn runtime_indices_borrow_and_extract_range_backed_resources() {
    let source = include_str!("../../../../examples/range_index.evg");
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
    for bad in [
        source.replacen_evg("    &(*data)[index]", "    &(*data)[index + 1]", 1),
        source.replace_evg("let empty:", "proof stale: **view == 42; let empty:"),
        source.replace_evg("modifies(&(*data)[index])", ""),
        source.replace_evg(
            "take::<unique(usize), 8>(&*data, 3)",
            "take::<unique(usize), 8>(&*data, 2)",
        ),
    ] {
        assert!(verify(&bad).is_err(), "accepted {bad}");
    }
}

#[test]
fn equal_runtime_indices_share_one_input_slot() {
    check(
        r#"
        fn equal(data: &[unique(usize); 2], i: usize, j: usize) -> bool
        where(i < 2 && j < 2 && i == j)
        ensures(result) {
            let left = &(*data)[i];
            let right = &(*data)[j];
            left == right && &**left == &**right
        }
    "#,
    );
    check(
        r#"
        fn different(data: &[unique(usize); 2], i: usize, j: usize)
        where(i < 2 && j < 2 && i != j) {
            let left = &(*data)[i];
            let right = &(*data)[j];
            proof slots: left != right;
            proof payloads: &**left != &**right;
        }
    "#,
    );
}

#[test]
fn runtime_input_indices_require_unadmitted_current_alias_relations() {
    let source = r#"
        fn observe(data: &[unique(usize); 2], i: usize, j: usize)
        where(i < 2 && j < 2) {
            let left = &(*data)[i];
            let right = &(*data)[j];
        }
    "#;
    for source in [
        source.to_owned(),
        source.replace_evg("let right", "proof alias: i == j by {trustme}; let right"),
        source.replace_evg(
            "let right",
            "proof separate: i != j by {trustme}; let right",
        ),
    ] {
        assert!(verify(&source).unwrap_err().contains("indices may alias"));
    }
    // Recipes are shared by branch snapshots. A former branch's separation
    // cannot be assumed by a later observation outside that branch.
    let changed_scope = r#"
        fn observe(data: &[unique(usize); 2], index: usize) where(index < 2) {
            if index != 0 {
                let first = &(*data)[0];
                let second = &(*data)[index];
            }
            let later = &(*data)[index];
        }
    "#;
    assert!(verify(changed_scope)
        .unwrap_err()
        .contains("indices may alias"));
    let overlapping = changed_scope.replace_evg(
        "let later = &(*data)[index];",
        "if index == 0 {let later = &(*data)[index];}",
    );
    assert!(verify(&overlapping)
        .unwrap_err()
        .contains("recipes overlap"));
}

#[test]
fn distinct_array_slots_do_not_assert_distinct_borrowed_pointees_at_calls() {
    let source = r#"
        fn separated(data: &[&usize; 2], i: usize, j: usize)
        where(i < 2 && j < 2 && i != j) {
            proof distinct: (*data)[i] != (*data)[j];
        }
        fn main() -> usize {
            let a: usize = 7;
            let b: usize = 42;
            let pointers = [&a, &b];
            separated(&pointers, 0, 1);
            b
        }
    "#;
    check(source);
    let aliased = source.replace_evg("[&a, &b]", "[&a, &a]");
    assert!(verify(&aliased).unwrap_err().contains("body recheck"));
}

#[test]
fn runtime_index_observations_stay_sparse_and_cannot_gain_nested_write_grants() {
    let source = include_str!("../../../../examples/range_index.evg");
    let huge = source.replace_evg('8', "1000000000");
    let (small, certificate) = prove(source).unwrap();
    let (large, large_certificate) = prove(&huge).unwrap();
    assert_eq!(small.obligations, large.obligations);
    assert_eq!(
        certificate.certificate_count(),
        large_certificate.certificate_count()
    );
    assert_eq!(
        verify_with_certificate(&huge, &large_certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 16384);
    assert!(large.run().unwrap_err().contains("before allocation"));
    for source in [
        "fn change(data: &[unique(usize); 2], i: usize) where(i < 2) {let view = &(*data)[i]; **view = 42;}",
        "fn change(data: &[unique(usize); 2], i: usize) where(i < 2) modifies(&*(*data)[i]) {*(*data)[i] = 42;}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}
