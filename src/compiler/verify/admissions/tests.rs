//! Admission scope, subject identity, and certificate replay regressions.

use super::*;

const NEEDS: &str = "fn needs(parameter: usize) where parameter == 42 {}";

#[test]
fn unused_admissions_do_not_make_unrelated_obligations_vacuous() {
    for body in [
        "proof poison: false by {trustme}; needs(43);",
        "let x: usize = 43; let y: usize = 43; proof poison: x == 42 by {trustme}; needs(y);",
        "proof poison: false by {trustme}; let value = usize::MAX + 1; proof _: value == 0;",
    ] {
        let source = format!("{NEEDS} fn main() -> usize {{{body} 0}}");
        assert!(verify(&source).is_err(), "{source}");
    }
    let source = "fn main() -> usize {proof unused: false by {trustme}; 42}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn matching_admissions_support_renamed_parameters_and_replay_without_search() {
    for proof in [
        "proof admitted: known by {trustme};",
        "proof _: known by {trustme};",
    ] {
        let source = format!("{NEEDS} fn main() -> usize {{let x: usize = 43; fact known = x == 42; proof unused: false by {{trustme}}; {proof} needs(x); 0}}");
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "0");
        assert_eq!(program.trusted_assumptions().len(), 2);
        let replayed = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(replayed.proof_search_count(), 0);
    }
}

#[test]
fn direct_alias_and_helper_writes_prevent_reusing_old_mutable_admissions() {
    let change = "fn change(value: &usize) modifies(value) {*value = 43;}";
    for mutation in [
        "x = x;",
        "x = x + 1;",
        "let alias = &x; *alias = 43;",
        "change(&x);",
    ] {
        let source = format!("{change} {NEEDS} fn main() -> usize {{let x: usize = 43; proof admitted: x == 42 by {{trustme}}; needs(x); {mutation} needs(x); 0}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains("precondition of needs"), "{error}: {source}");
    }
}

#[test]
fn folded_claims_cannot_be_reused_for_other_subjects_by_exact_or_apply() {
    for step in ["exact admitted", "apply admitted"] {
        let source = format!("fn main() -> usize {{let x: usize = 43; let y: usize = 43; proof admitted: x == 42 by {{trustme}}; proof wrong: y == 42 by {{{step}}}; 0}}");
        assert!(verify(&source).is_err(), "{source}");
    }
    let stale = "fn main() -> usize {let x: usize = 43; proof admitted: x == 42 by {trustme}; x = x; proof stale: x == 42 by {exact admitted}; 0}";
    assert!(verify(stale).unwrap_err().contains("earlier state"));
}

#[test]
fn derived_and_compound_evidence_keeps_admissions_local() {
    let source = format!("{NEEDS} fn main() -> usize {{let x: usize = 43; let y: usize = 7; proof a: x == 42 by {{trustme}}; proof b: y == 42 by {{trustme}}; proof both: x == 42 && y == 42 by {{constructor; exact a; exact b}}; proof derived: x == 42 by {{exact a}}; needs(x); 0}}");
    assert!(verify(&source).is_ok());
    let wrong = source.replace("exact b", "exact a");
    assert!(verify(&wrong).is_err());
}

#[test]
fn admitted_preconditions_do_not_publish_false_posts_into_unrelated_paths() {
    let source = "fn needs(parameter: usize) where parameter == 42 ensures(parameter == 42) {} fn other(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 43; let y: usize = 43; proof admitted: x == 42 by {trustme}; needs(x); other(y); 0}";
    assert!(verify(source)
        .unwrap_err()
        .contains("precondition of other"));
    let valid = source.replace("other(y);", "");
    let (_, bundle) = prove(&valid).unwrap();
    assert_eq!(
        verify_with_certificate(&valid, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn admission_dependent_result_invariants_cannot_erase_unrelated_obligations() {
    let source = "type Impossible struct {} where false; fn impossible(parameter: usize) -> Impossible where parameter == 0 && parameter == 1 {Impossible {}} fn needs(value: usize) where value == 42 {} fn main() -> usize {let x: usize = 43; proof admitted: x == 0 && x == 1 by {trustme}; let invalid = impossible(x); needs(43); 0}";
    assert!(verify(source).is_err());
}

#[test]
fn an_explicit_false_admission_can_support_a_false_precondition_without_spreading() {
    let source = "fn impossible() where false {} fn needs(value: usize) where value == 42 {} fn main() -> usize {proof admitted: false by {trustme}; impossible(); 0}";
    let (_, bundle) = prove(source).unwrap();
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let unrelated = source.replace("impossible(); 0", "impossible(); needs(43); 0");
    assert!(verify(&unrelated)
        .unwrap_err()
        .contains("precondition of needs"));
}

#[test]
fn a_consumed_precondition_does_not_resurrect_after_symbolic_mutation() {
    let source = "fn needs(parameter: usize) where parameter == 42 {} fn test(x: usize) where x == 43 {proof admitted: x == 42 by {trustme}; needs(x); x = x + 1; needs(x);} fn main() {}";
    assert!(verify(source)
        .unwrap_err()
        .contains("precondition of needs"));
    let with_post = source.replace(
        "where parameter == 42 {}",
        "where parameter == 42 ensures(parameter == 42) {}",
    );
    assert!(verify(&with_post)
        .unwrap_err()
        .contains("precondition of needs"));
}

#[test]
fn scalar_copy_requires_explicit_admission_transfer_and_then_survives_source_write() {
    let before = "fn needs(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 43; proof source: x == 42 by {trustme}; let saved = x; ";
    let implicit = format!("{before} needs(saved); 0}}");
    assert!(verify(&implicit)
        .unwrap_err()
        .contains("precondition of needs"));
    let symbolic = "fn needs(parameter: usize) where parameter == 42 {} fn test(x: usize) {proof source: x == 42 by {trustme}; let saved = x; needs(saved);} fn main() {}";
    assert!(verify(symbolic)
        .unwrap_err()
        .contains("precondition of needs"));
    let symbolic_carried = symbolic.replace("let saved = x; needs(saved);", "let saved = x; proof carried: saved == 42 by {cases source with lower , upper; omega}; x = x + 1; needs(saved);");
    assert!(verify(&symbolic_carried).is_ok());
    let explicit = format!("{before} proof carried: saved == 42 by {{cases source with lower , upper; omega}}; x = x + 1; needs(saved); 0}}");
    let (program, bundle) = prove(&explicit).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "0");
    assert_eq!(
        verify_with_certificate(&explicit, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn copying_a_pointer_does_not_preserve_proofs_when_the_shared_pointee_changes() {
    let source = "fn needs(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 43; let p = &x; proof original: *p == 42 by {trustme}; let q = p; proof carried: *q == 42 by {exact original}; *p = 43; needs(*q); 0}";
    assert!(verify(source)
        .unwrap_err()
        .contains("precondition of needs"));
    let aggregate = "type Holder struct {pointer: &usize} impl Copy for Holder {} fn needs(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 43; let holder = Holder {pointer: &x}; proof original: *holder.pointer == 42 by {trustme}; let saved = holder; proof carried: *saved.pointer == 42 by {exact original}; *holder.pointer = 43; needs(*saved.pointer); 0}";
    assert!(verify(aggregate)
        .unwrap_err()
        .contains("precondition of needs"));
}

#[test]
fn a_multi_plane_claim_expires_when_either_dependency_changes() {
    let before = "fn needs(parameter: usize) where parameter == 42 {} fn main() -> usize {let x: usize = 43; let y: usize = 43; proof together: x == 42 && y == 42 by {trustme}; ";
    let implicit = format!("{before} x = x + 1; needs(y); 0}}");
    assert!(verify(&implicit)
        .unwrap_err()
        .contains("precondition of needs"));
    let explicit = format!("{before} proof independent: y == 42 by {{cases together with left , right; exact right}}; x = x + 1; needs(y); 0}}");
    let (_, bundle) = prove(&explicit).unwrap();
    assert_eq!(
        verify_with_certificate(&explicit, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
