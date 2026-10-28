use super::*;

const ADMITTED_DROP: &str = "type Resource struct {value: usize} impl Drop for Resource {fn drop(self) {proof nonmax: self.value < usize::MAX by {trustme}; let next = self.value + 1;}}";

#[test]
fn implicit_read_only_cleanup_imports_safety_dependencies() {
    for body in [
        "fn release(value: Resource) {} fn main() -> usize {release(Resource {value: usize::MAX}); 42}",
        "type Envelope struct {inner: Resource} fn release(value: Envelope) {} fn main() -> usize {release(Envelope {inner: Resource {value: usize::MAX}}); 42}",
        "fn release(ideal n: nat, values: [Resource; n]) {} fn main() -> usize {release([Resource {value: usize::MAX}]); 42}",
    ] {
        let source = format!("{ADMITTED_DROP} {body}");
        let (program, bundle) = prove(&source).unwrap();
        for name in ["release", "main"] {
            assert_eq!(program.function_safety_assumptions(name).unwrap().count(), 1, "{name}: {body}");
        }
        let replay = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(replay.proof_search_count(), 0);
        assert_eq!(replay.function_safety_assumptions("main").unwrap().count(), 1);
    }
}

#[test]
fn empty_arrays_do_not_execute_or_import_element_cleanup() {
    let source =
        format!("{ADMITTED_DROP} fn main() -> usize {{let values: [Resource; 0] = []; 42}}");
    let (program, bundle) = prove(&source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        0
    );
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert!(events.is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn read_only_destructors_check_the_actual_reference_aliases() {
    let source = "fn needs_bound(n: usize) -> usize where n < usize::MAX {n + 1} type Coupled struct {left: &usize, right: &usize} where left == right; impl Drop for Coupled {fn drop(self) {let next = needs_bound(*self.left);}} fn main() -> usize {let value: usize = 41; let coupled = Coupled {left: &value, right: &value}; 42}";
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Coupled"]);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let error = verify(&source.replace("= 41;", "= usize::MAX;")).unwrap_err();
    assert!(error.contains("precondition of needs_bound"), "{error}");
}

#[test]
fn potentially_divergent_cleanup_propagates_through_cached_summaries_and_aggregates() {
    let spin =
        "type Spin struct {} impl Drop for Spin {fn drop(self) {while true invariant(true) {}}}";
    for (declarations, binding) in [
        ("", "let value = Spin {};"),
        (
            "type Envelope struct {value: Spin}",
            "let value = Envelope {value: Spin {}};",
        ),
        (
            "type Envelope struct {value: Spin} impl Drop for Envelope {fn drop(self) {}}",
            "let value = Envelope {value: Spin {}};",
        ),
        ("", "let value: [Spin; 2] = [Spin {}, Spin {}];"),
    ] {
        let source = format!("{spin} {declarations} fn produce() -> usize ensures(result == 42) {{{binding} 42}} fn main() -> usize {{produce()}}");
        let (program, bundle) = prove(&source).unwrap();
        for function in ["produce", "main"] {
            assert!(
                program
                    .potentially_diverging_functions()
                    .any(|name| name == function),
                "{function}: {source}"
            );
        }
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        let invalid = source.replace(
            "fn main() -> usize {produce()}",
            "fn main() -> usize {proof invalid: produce() == 42; 42}",
        );
        assert!(verify(&invalid).unwrap_err().contains("divergent"));
    }
    let source = format!("{spin} fn main() -> usize {{let value = Spin {{}}; 42}}");
    assert!(verify(&source)
        .unwrap()
        .run()
        .unwrap_err()
        .contains("limit reached"));
}

#[test]
fn empty_arrays_and_borrows_do_not_import_divergent_element_cleanup() {
    let source = "type Spin struct {} impl Drop for Spin {fn drop(self) {while true invariant(true) {}}} fn observe(value: &Spin) -> usize {42} fn produce() -> usize ensures(result == 42) {let values: [Spin; 0] = []; 42} fn main() -> usize {proof safe: produce() == 42; produce()}";
    let (program, bundle) = prove(source).unwrap();
    for name in ["observe", "produce", "main"] {
        assert!(
            !program
                .potentially_diverging_functions()
                .any(|function| function == name),
            "{name}"
        );
    }
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert!(events.is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}
