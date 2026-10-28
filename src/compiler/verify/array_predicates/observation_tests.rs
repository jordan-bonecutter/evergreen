use super::*;

#[test]
fn range_premises_authorize_member_loans_and_real_owner_extraction() {
    let source = include_str!("../../../../examples/range_slots.evg");
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
}

#[test]
fn slot_range_observations_cannot_cover_other_indices_or_survive_extraction() {
    let source = include_str!("../../../../examples/range_slots.evg");
    for bad in [
        source.replacen("&(*data)[0]", "&(*data)[1]", 2),
        source.replace(
            "    move((*data)[0])",
            "    let value = move((*data)[0]); let twice: T = move((*data)[0]); value",
        ),
        source.replace(
            "    let empty:",
            "    proof stale: **view == 42; let empty:",
        ),
        source.replace(
            "    let empty:",
            "    let twice = first::<unique(usize), 8>(&*data); let empty:",
        ),
    ] {
        assert!(verify(&bad).is_err(), "accepted {bad}");
    }
    let invented = "fn bad(data: &[unique(usize) | shape(unique(usize)); 1]) -> &unique(usize) borrows(&(*data)[0]) {proof fake: forall(i: integer) where(0 <= i && i < 1) {typeof((*data)[i]) == unique(usize)} by {trustme}; &(*data)[0]}";
    let error = verify(invented).unwrap_err();
    assert!(error.contains("member"), "{error}");
}

#[test]
fn affine_and_negative_type_ranges_authorize_only_their_real_member() {
    let source = "fn read(data: &[usize | shape(usize); 8]) -> usize where(forall(i: integer) where(i == 1) {typeof((*data)[2 * i]) != shape(usize)}) {(*data)[2]} fn main() -> usize {let data: unique(usize | shape(usize), 8) = alloc(8, shape(usize)); (*data)[2] = 42; let value = read(&*data); let retired: usize = move((*data)[2]); let empty: unique(shape(usize), 8) = data; drop(empty); value}";
    for source in [
        source.to_owned(),
        source.replace("!= shape(usize)", "== usize"),
    ] {
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        crate::compiler::native::emit(&program).unwrap();
    }
    let odd = source.replace("{(*data)[2]}", "{(*data)[3]}");
    assert!(verify(&odd).is_err());
    let ambiguous = source.replace("usize | shape(usize)", "usize | bool | shape(usize)");
    assert!(verify(&ambiguous).is_err());
}

#[test]
fn range_borrowing_keeps_destructors_linear_and_requires_write_authority() {
    let source = include_str!("../../../../examples/range_slots.evg");
    let declarations = source.split("fn main()").next().unwrap();
    let resource = format!("type Resource struct {{tag: usize}} where(tag == 42); impl Drop for Resource {{fn drop(self) {{proof valid: self.tag == 42;}}}} {declarations} fn main() -> usize {{let data: unique(Resource | shape(Resource), 8) = alloc(8, shape(Resource)); (*data)[0] = Resource {{tag: 42}}; let view = first::<Resource, 8>(&*data); proof read: view.tag == 42; let value = take_first::<Resource, 8>(&*data); let empty: unique(shape(Resource), 8) = data; drop(empty); value.tag}}");
    let (program, bundle) = prove(&resource).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    assert_eq!(
        verify_with_certificate(&resource, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let stolen = resource.replace("proof read:", "let stolen: Resource = *view; proof read:");
    assert!(verify(&stolen).is_err());
    let no_write = source.replace("modifies(&(*data)[0])", "");
    let error = verify(&no_write).unwrap_err();
    assert!(
        error.contains("effect contract") || error.contains("modifies"),
        "{error}"
    );
}

#[test]
fn conditional_range_domains_are_checked_at_the_point_of_use() {
    let good = "fn inspect(data: &[unique(usize) | shape(unique(usize)); 1], ready: bool) -> usize where(forall(i: integer) where(0 <= i && i < 1 && ready) {typeof((*data)[i]) == unique(usize)}) {if ready {let view: &unique(usize) = &(*data)[0]; **view} else {42}} fn main() -> usize {42}";
    let (program, bundle) = prove(good).unwrap();
    assert_eq!(
        verify_with_certificate(good, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let bad = good.replace(
        "if ready {let view: &unique(usize) = &(*data)[0]; **view} else {42}",
        "if ready {let view: &unique(usize) = &(*data)[0]; let seen = **view;} let uncovered: &unique(usize) = &(*data)[0]; **uncovered",
    );
    assert!(verify(&bad).is_err());
    let changed_guard = good.replace("if ready {", "if ready {ready = false;");
    assert!(verify(&changed_guard).is_err());
    let promoted = good.replace("if ready {", "if ready {proof promote: (forall(i: integer) where(0 <= i && i < 1 && ready) {typeof((*data)[i]) == unique(usize)}) => ready => (forall(j: integer) where(0 <= j && j < 1) {typeof((*data)[j]) == unique(usize)}) by {intro all; intro enabled; intro j; specialize all(j); omega}; proof live: forall(i: integer) where(0 <= i && i < 1) {typeof((*data)[i]) == unique(usize)} by {apply promote; assumption; omega}; ready = false;");
    let (program, bundle) = prove(&promoted).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&promoted, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn conditional_range_promises_do_not_require_inactive_payloads() {
    let declaration = r#"
        fn inspect(data: &[unique(usize) | shape(unique(usize)); 1], ready: bool) -> usize
        where(forall(i: integer) where(0 <= i && i < 1 && ready) {
            typeof((*data)[i]) == unique(usize)
        }) {
            if ready {let view: &unique(usize) = &(*data)[0]; **view} else {42}
        }
    "#;
    for (initialize, enabled, extract) in [
        ("", "false", ""),
        (
            "(*data)[0] = alloc(42);",
            "true",
            "let payload: unique(usize) = move((*data)[0]);",
        ),
    ] {
        let source = format!(
            r#"
            {declaration}
            fn main() -> usize {{
                let data: unique(unique(usize) | shape(unique(usize)), 1) =
                    alloc(1, shape(unique(usize)));
                {initialize}
                let value = inspect(&*data, {enabled});
                {extract}
                let empty: unique(shape(unique(usize)), 1) = data;
                drop(empty);
                value
            }}
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
        crate::compiler::native::emit(&program).unwrap();
    }
}

#[test]
fn aliased_range_inputs_cannot_extract_the_same_owner_twice() {
    let declarations = include_str!("../../../../examples/range_slots.evg")
        .split("fn main()")
        .next()
        .unwrap();
    let twice = "fn twice(a: &[unique(usize) | shape(unique(usize)); 8], b: &[unique(usize) | shape(unique(usize)); 8]) -> unique(usize) where((forall(i: integer) where(0 <= i && i < 1 && i < integer(8)) {typeof((*a)[i]) == unique(usize)}) && (forall(i: integer) where(0 <= i && i < 1 && i < integer(8)) {typeof((*b)[i]) == unique(usize)})) modifies(&(*a)[0], &(*b)[0]) {let first = take_first::<unique(usize), 8>(a); let second = take_first::<unique(usize), 8>(b); second}";
    let body = "let a: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); let b: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize))); (*a)[0] = alloc(7); (*b)[0] = alloc(42); let value = twice(&*a, &*b); let empty_a: unique(shape(unique(usize)), 8) = a; let empty_b: unique(shape(unique(usize)), 8) = b; drop(empty_a); drop(empty_b); *value";
    let source = format!("{declarations} {twice} fn main() -> usize {{{body}}}");
    assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
    let aliased = source.replace("twice(&*a, &*b)", "twice(&*a, &*a)");
    let error = verify(&aliased).unwrap_err();
    assert!(
        error.contains("body recheck") && error.contains("precondition"),
        "{error}"
    );
}

#[test]
fn demanded_slot_range_proofs_remain_sparse_for_billion_slot_buffers() {
    let small = include_str!("../../../../examples/range_slots.evg");
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
