use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn nominal_range_invariants_authorize_reads_and_complete_consumption() {
    let source = include_str!("../../../../examples/range_type.evg");
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
    for invalid in [
        source.replace_evg("(*data)[0] = value;", ""),
        source.replace_evg("    *payload", "    **view"),
        source.replace_evg(
            "let payload = &**view;",
            "let stolen: unique(usize) = *view; let payload = &**view;",
        ),
    ] {
        assert!(verify(&invalid).is_err(), "accepted {invalid}");
    }
    let steal = source.replace_evg(
        "let view = slot.get();",
        "let stolen: unique(usize) = move((*slot.data)[0]); let view = slot.get();",
    );
    let error = verify(&steal).unwrap_err();
    assert!(error.contains("invariant"), "{error}");
    let invented = source.replace_evg("(*data)[0] = value;", "proof invented: forall(i: integer) where(0 <= i && i < 1) {typeof((*data)[i]) == T} by {trustme};");
    assert!(
        verify(&invented).is_err(),
        "an admitted type fact created an owner"
    );
    let declarations = source.split("fn main()").next().unwrap();
    let resource = format!(
        r#"
        type Resource struct {{tag: usize}} where(tag == 42);
        impl Drop for Resource {{fn drop(self) {{proof valid: self.tag == 42;}}}}
        {declarations}
        fn main() -> usize {{
            let slot = Slot::<Resource>::new(Resource {{tag: 42}});
            let view = slot.get();
            proof tag: view.tag == 42;
            let value = slot.into_inner();
            value.tag
        }}
    "#
    );
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
}

#[test]
fn nominal_scalar_universals_are_checked_at_construction_and_mutation() {
    let source = r#"
        type Bound struct {limit: usize} where (
            forall(i: integer) where(0 <= i && i < 4) {i < integer(self.limit)}
        );
        fn main() -> usize {
            let bound = Bound {limit: 46};
            bound.limit - 4
        }
    "#;
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for invalid in [
        source.replace_evg("Bound {limit: 46}", "Bound {limit: 2}"),
        source.replace_evg("bound.limit - 4", "bound.limit = 0; bound.limit - 4"),
    ] {
        assert!(verify(&invalid).is_err(), "accepted {invalid}");
    }
}

#[test]
fn empty_nominal_range_invariants_do_not_materialize_their_extents() {
    let source = r#"
        type Empty<T, const N: usize> struct {data: unique(T | shape(T), N)} where (
            forall(i: integer) where(0 <= i && i < integer(N)) {
                typeof((*self.data)[i]) == shape(T)
            }
        );
        impl<T, const N: usize> Empty<T, N> {
            fn new() -> Self {
                Self {data: alloc(N, shape(T))}
            }
            method into_data() -> unique(T | shape(T), N) {
                let Self {data} = self;
                data
            }
        }
        fn main() -> usize {
            let empty = Empty::<unique(usize), 8>::new();
            let data = empty.into_data();
            let retired: unique(shape(unique(usize)), 8) = data;
            drop(retired);
            42
        }
    "#;
    let (small, certificate) = prove(source).unwrap();
    assert_eq!(small.run().unwrap().to_string(), "42");
    let huge = source.replace_evg('8', "1000000000");
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
}
