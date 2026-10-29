use super::*;

#[test]
fn source_results_preserve_values_select_variants_and_drop_owned_payloads() {
    let source = include_str!("../../../examples/result.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let owned = "type Resource struct {tag: usize} impl Drop for Resource {fn drop({tag}) {}} fn main() -> usize {let failed = results::Result::<unique(usize), Resource>::err(Resource {tag: 7}); let owner = failed.unwrap_or(alloc(42)); *owner}";
    let (value, events) = verify(owned).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(
        events
            .iter()
            .filter(|event| event.ends_with("Resource"))
            .count(),
        1
    );
    for invalid in [
        "fn main() -> usize {let r = results::Result::<usize, usize>::err(7); r.unwrap()}",
        "fn main() -> usize {let r = results::Result::<usize, usize>::ok(42); let view = r.get(); drop(r); *view}",
    ] { assert!(verify(invalid).is_err(), "accepted {invalid}"); }
}
