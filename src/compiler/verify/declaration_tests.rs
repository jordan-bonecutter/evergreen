//! Refinement and implicit-cleanup dependencies must use checked declarations,
//! regardless of their order in the source or package.

use super::*;

#[test]
fn source_functions_can_define_record_refinements_without_becoming_axioms() {
    let source = "type Positive struct {data: usize} where positive(data); ideal fn positive(n: usize) -> bool {n > 0} impl Positive {fn new(n: usize) -> Self where positive(n) {Self {data: n}}} fn main() -> usize {let value = Positive::new(42); value.data}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("Positive::new(42)", "Positive::new(0)")).is_err());
    assert!(verify(&source.replace("where positive(n)", "")).is_err());
}

#[test]
fn predicates_check_the_nominal_types_used_only_inside_their_bodies() {
    let source = "type Checked struct {data: usize} where positive(data); type Local struct {value: usize} impl Copy for Local {} ideal fn positive(n: usize) -> bool ensures result == (n > 0) {let local = Local {value: n}; local.value > 0} fn make(n: usize) -> Checked where positive(n) {Checked {data: n}} fn main() -> usize {let value = make(42); value.data}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn refinement_dependencies_cannot_circularly_assume_the_type_being_defined() {
    for source in [
        "type Circular struct {value: usize} where valid(&self); ideal fn valid(value: &Circular) -> bool {value.value > 0}",
        "type Circular struct {value: usize} where valid(value); ideal fn valid(n: usize) -> bool {let value = Circular {value: n}; value.value > 0}",
        "type Circular struct {value: usize} where valid(value); ideal fn valid(n: usize) -> bool {other(n)} ideal fn other(n: usize) -> bool {let value = Circular {value: n}; value.value > 0}",
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains("mutually recursive declarations"), "{error}");
    }
}

#[test]
fn implicit_cleanup_can_depend_on_a_helper_declared_after_its_caller() {
    let source = "type Resource struct {value: usize} fn consume(value: Resource) -> usize {value.value} impl Drop for Resource {fn drop(self) {mark(self.value);}} fn mark(value: usize) {} fn main() -> usize {consume(Resource {value: 42})}";
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Resource"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
