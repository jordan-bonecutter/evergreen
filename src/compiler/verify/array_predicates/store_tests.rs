use super::*;

#[test]
fn input_store_frames_preserve_initialized_prefixes_and_empty_suffixes() {
    let source = include_str!("../../../../examples/range_store.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let native = crate::compiler::native::emit(&program).unwrap();
    for equivalent in [
        source.replace("== T", "!= shape(T)"),
        source.replace("== shape(T)", "!= T"),
    ] {
        let (program, bundle) = prove(&equivalent).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(&equivalent, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        assert_eq!(crate::compiler::native::emit(&program).unwrap(), native);
    }
}

#[test]
fn stored_ranges_do_not_cover_extracted_slots_or_another_input_plane() {
    let source = include_str!("../../../../examples/range_store.evg");
    let pop = source.find("fn take_last").unwrap();
    let (push, pop_source) = source.split_at(pop);
    for bad in [
        pop_source.replace("integer(length) - 1", "integer(length)"),
        pop_source.replace("move((*data)[length - 1])", "move((*data)[0])"),
        pop_source.replace("if length > 1", "if length > 0"),
    ] {
        let error = verify(&format!("{push}{bad}")).unwrap_err();
        assert!(
            error.contains("prove") || error.contains("member"),
            "{error}"
        );
    }
    let wrong_plane = source.replace(
        "fn take_last<T, const N: usize>(data:",
        "fn take_last<T, const N: usize>(other: &[T | shape(T); N], data:",
    );
    let wrong_plane =
        wrong_plane.replace("typeof(old(*data)[i]) == T", "typeof(old(*other)[i]) == T");
    assert!(verify(&wrong_plane).is_err());
}

#[test]
fn carrying_an_input_range_across_a_store_requires_its_explicit_frame_proof() {
    let source = include_str!("../../../../examples/range_store.evg");
    let start = source.find("    proof prefix:").unwrap();
    let end = source[start..].find("    proof empty_frame:").unwrap() + start;
    let mut missing = source.to_owned();
    missing.replace_range(start..end, "");
    let error = verify(&missing).unwrap_err();
    assert!(error.contains("earlier contents version"), "{error}");
    let changed = source.replace(
        "(*data)[length] = value;",
        "(*data)[length] = value; let removed: T = move((*data)[length]);",
    );
    assert!(
        verify(&changed).is_err(),
        "a second write retained the first store's range"
    );
}

#[test]
fn input_store_range_frames_remain_sparse_for_billion_slot_buffers() {
    let source = include_str!("../../../../examples/range_store.evg");
    let huge = source.replace('8', "1000000000");
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
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 32768);
    assert!(large.run().unwrap_err().contains("before allocation"));
}

#[test]
fn admitted_ranges_do_not_supply_missing_owners_or_unrelated_selector_claims() {
    let source = include_str!("../../../../examples/range_store.evg");
    let take = source.find("fn take_last").unwrap();
    let (push, pop) = source.split_at(take);
    let start = pop.find("where(").unwrap();
    let end = pop.find("modifies(").unwrap();
    let fake = format!(
        "{}where(0 < length && length <= N)\n{}",
        &pop[..start],
        &pop[end..]
    );
    let fake = fake.replace("by {assumption}", "by {trustme}");
    assert!(
        verify(&format!("{push}{fake}")).is_err(),
        "admitted type ranges created a payload"
    );
    let never_member = "fn main() -> usize {let data: unique(usize | shape(usize), 8) = alloc(8, shape(usize)); proof absent: forall(i: integer) where(0 <= i && i < 8) {typeof((*data)[i]) != bool} by {intro i; omega}; let empty: unique(shape(usize), 8) = data; drop(empty); 42}";
    let (program, bundle) = prove(never_member).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(never_member, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn nested_helpers_preserve_range_provenance_through_multiple_input_stores() {
    let source = include_str!("../../../../examples/range_store.evg");
    let roundtrip = r#"
        fn round_trip<T, const N: usize>(data: &[T | shape(T); N], length: usize, value: T) -> T
        where(length < N && (forall(i: integer) where(0 <= i && i < integer(length) && i < integer(N)) {
            typeof((*data)[i]) == T
        }) && (forall(i: integer) where(0 <= i && integer(length) <= i && i < integer(N)) {
            typeof((*data)[i]) == shape(T)
        }))
        modifies(&(*data)[length])
        ensures((forall(i: integer) where(0 <= i && i < integer(length) && i < integer(N)) {
            typeof((*data)[i]) == T
        }) && (forall(i: integer) where(0 <= i && integer(length) <= i && i < integer(N)) {
            typeof((*data)[i]) == shape(T)
        })) {
            push::<T, N>(data, length, value);
            take_last::<T, N>(data, length + 1)
        }
    "#;
    let source = source.replace("fn main()", &format!("{roundtrip} fn main()"));
    let source = source.replace("    let last =", "    let recovered = round_trip::<unique(usize), 8>(&*data, 2, alloc(99)); proof value: *recovered == 99; let last =");
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

#[test]
fn prefix_transitions_preserve_exactly_once_resource_cleanup() {
    let declarations = include_str!("../../../../examples/range_store.evg")
        .split("fn main()")
        .next()
        .unwrap();
    let source = format!(
        r#"
        type Resource struct {{tag: usize}} where(tag > 0);
        impl Drop for Resource {{fn drop(self) {{proof valid: self.tag > 0;}}}}
        {declarations}
        fn main() -> usize {{
            let data: unique(Resource | shape(Resource), 8) = alloc(8, shape(Resource));
            push::<Resource, 8>(&*data, 0, Resource {{tag: 7}});
            push::<Resource, 8>(&*data, 1, Resource {{tag: 42}});
            let last = take_last::<Resource, 8>(&*data, 2);
            let first = take_last::<Resource, 8>(&*data, 1);
            let empty: unique(shape(Resource), 8) = data;
            drop(empty);
            last.tag
        }}
    "#
    );
    let (program, bundle) = prove(&source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Resource"]);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}
