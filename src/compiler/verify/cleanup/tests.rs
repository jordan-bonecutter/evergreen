use super::*;

#[test]
fn decomposed_destructors_extract_slots_and_clean_their_payload_once() {
    let source = include_str!("../../../../examples/range_drop.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events.len(), 2);
    assert_eq!(events.last().map(String::as_str), Some("drop Resource"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let prefix = source.split("fn main()").next().unwrap();
    let copied = format!(
        "{prefix} fn main() -> usize {{let slot = Slot::<usize>::new(42); drop(slot); 42}}"
    );
    let (value, events) = verify(&copied).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events.len(), 1);
}

#[test]
fn destructor_extraction_requires_consumed_self_and_current_slot_authority() {
    let source = include_str!("../../../../examples/range_drop.evg");
    let early = source.replace(
        "let Self {data} = self;\n        let value: T = move((*data)[0]);",
        "let value: T = move((*self.data)[0]); let Self {data} = self;",
    );
    assert!(verify(&early).unwrap_err().contains("decompose self"));
    for invalid in [
        source.replace(
            "let value: T = move((*data)[0]);",
            "let value: T = move((*data)[0]); let again: T = move((*data)[0]);",
        ),
        source.replace("(*data)[0] = value;", ""),
        source.replace("    answer\n", "    *payload\n"),
        source.replace("drop(empty);", "drop(empty); proof stale: (*data)[0] == 0;"),
    ] {
        assert!(verify(&invalid).is_err(), "accepted {invalid}");
    }
}

#[test]
fn extraction_from_borrowed_destructor_fields_needs_a_write_footprint() {
    let source = r#"
        type Borrowed struct {data: &[unique(usize) | shape(unique(usize)); 1]} where (
            forall(i: integer) where(0 <= i && i < 1) {
                typeof((*self.data)[i]) == unique(usize)
            }
        );
        impl Drop for Borrowed {
            fn drop(self) modifies(&(*self.data)[0]) {
                let Self {data} = self;
                let value: unique(usize) = move((*data)[0]);
            }
        }
        fn main() -> usize {
            let data: unique(unique(usize) | shape(unique(usize)), 1) = alloc(1, shape(unique(usize)));
            (*data)[0] = alloc(42);
            let borrowed = Borrowed {data: &*data};
            drop(borrowed);
            let empty: unique(shape(unique(usize)), 1) = data;
            drop(empty);
            42
        }
    "#;
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
    let error = verify(&source.replace("modifies(&(*self.data)[0])", "")).unwrap_err();
    assert!(
        error.contains("modifies") || error.contains("effect contract"),
        "{error}"
    );
}

#[test]
fn destructor_loops_use_normal_invariant_effect_and_termination_checks() {
    let source = include_str!("../../../../examples/drop_loop.evg");
    let (program, bundle) = prove(source).unwrap();
    assert!(!program
        .potentially_diverging_functions()
        .any(|name| name == "main"));
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Counter"]);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let zero = source
        .replace("= 39;", "= 42;")
        .replace("limit: 3", "limit: 0");
    assert_eq!(verify(&zero).unwrap().run().unwrap().to_string(), "42");
    for invalid in [
        source.replace("remaining = remaining - 1", "remaining = remaining"),
        source.replace("modifies(count, &remaining)", "modifies(&remaining)"),
        source.replace("modifies(self.count)", ""),
        source.replace("limit: 3", "limit: usize::MAX"),
    ] {
        assert!(verify(&invalid).is_err(), "accepted {invalid}");
    }
    let unmeasured = source.replace("decreases(remaining)", "");
    let program = verify(&unmeasured).unwrap();
    assert!(program
        .potentially_diverging_functions()
        .any(|name| name == "main"));
    assert_eq!(program.run().unwrap().to_string(), "42");
}

#[test]
fn destructor_loops_cannot_consume_surrounding_owners_without_a_resource_frame() {
    let source = r#"
        type Owner struct {data: unique(usize)}
        impl Drop for Owner {
            fn drop(self) {
                let Self {data} = self;
                let cursor: usize = 0;
                while cursor < 2 invariant(cursor <= 2) modifies(&cursor) decreases(2 - cursor) {
                    drop(data);
                    cursor = cursor + 1;
                }
            }
        }
        fn main() -> usize {42}
    "#;
    let error = verify(source).unwrap_err();
    assert!(
        error.contains("loop write") || error.contains("ownership"),
        "{error}"
    );
    let fake_frame = source.replace("modifies(&cursor)", "modifies(&cursor, &data)");
    let error = verify(&fake_frame).unwrap_err();
    assert!(error.contains("shape invariant"), "{error}");
}
