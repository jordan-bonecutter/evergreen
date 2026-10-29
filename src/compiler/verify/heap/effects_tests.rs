use super::*;

#[test]
fn fresh_allocation_summaries_preserve_values_and_invalidate_old_borrows() {
    let source = "fn replace(data: unique(usize)) -> unique(usize) ensures *result == old(*data) {let value = *data; drop(data); alloc(value)} fn main() -> usize {let data: unique(usize) = alloc(42); let old_view = &*data; let next = replace(data); proof preserved: *next == 42; *next}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let stale = source.replace("proof preserved: *next == 42; *next", "*old_view");
    assert!(verify(&stale)
        .unwrap_err()
        .contains("reference has type never"));
    let wrong = source.replace("alloc(value)", "alloc(43)");
    assert!(verify(&wrong).unwrap_err().contains("postcondition"));
}

#[test]
fn returning_an_input_on_any_branch_keeps_the_actual_storage_path() {
    let source = "fn choose(data: unique(usize), replace: bool) -> unique(usize) {if replace {let value = *data; drop(data); alloc(value)} else {data}} fn main() -> usize {let data: unique(usize) = alloc(42); let view = &*data; let next = choose(data, false); *view}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let stale = source.replace("choose(data, false)", "choose(data, true)");
    assert!(verify(&stale)
        .unwrap_err()
        .contains("reference has type never"));
}

#[test]
fn allocation_summaries_keep_alias_checks_and_trusted_dependencies() {
    let aliased = "fn replace(data: unique(usize), view: &usize) -> unique(usize) {drop(data); alloc(*view)} fn main() -> usize {let data: unique(usize) = alloc(42); let view = &*data; let next = replace(data, view); *next}";
    assert!(verify(aliased)
        .unwrap_err()
        .contains("reference has type never"));
    let trusted = "fn replace(data: unique(usize)) -> unique(usize) ensures *result == 42 {drop(data); alloc(43)} proof {trustme} fn needs(n: usize) where n == 42 {} fn main() {let data: unique(usize) = alloc(0); let next = replace(data); needs(*next);}";
    let (program, bundle) = prove(trusted).unwrap();
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        1
    );
    assert_eq!(
        verify_with_certificate(trusted, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
