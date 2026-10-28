use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn anonymous_universal_proofs_are_live_state_indexed_contract_evidence() {
    let source = "type Bounds struct {limit: usize} fn require(b: &Bounds) where(forall(i: integer) where(0 <= i && i < 4) {i < integer(b.limit)}) {} fn main() -> usize {let b = Bounds {limit: 0}; proof _: forall(i: integer) where(0 <= i && i < 4) {i < integer(b.limit)} by {trustme}; require(&b); 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let stale = source.replace_evg("require(&b);", "b.limit = 0; require(&b);");
    assert!(verify(&stale).is_err());
}

#[test]
fn function_universal_contracts_import_specialize_and_replay() {
    let source = "fn require(limit: usize) -> usize where(forall(i: integer) where(0 <= i && i < 4) {i < integer(limit)}) {proof bounds: forall(i: integer) where(0 <= i && i < 4) {i < integer(limit)} by {assumption}; proof selected: 3 < integer(limit) by {specialize bounds(3); omega}; 42} fn establish(limit: usize) -> usize where(limit >= 4) ensures(forall(i: integer) where(0 <= i && i < 4) {i < integer(limit)}) {42} fn main() -> usize {let limit: usize = 8; establish(limit); require(limit)}";
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
    assert!(verify(&source.replace_evg("limit: usize = 8", "limit: usize = 2")).is_err());
    assert!(verify(&source.replace_evg("where(limit >= 4)", "where(limit >= 2)")).is_err());
}

#[test]
fn mixed_loop_invariants_keep_universals_out_of_arithmetic_paths() {
    let source = "fn main() -> usize {let cursor: usize = 0; while cursor < 42 invariant(cursor <= 42 && (forall(i: integer) where(i >= 0) {i + 1 > i})) modifies(&cursor) decreases(42 - cursor) {proof rule: forall(i: integer) where(i >= 0) {i + 1 > i} by {assumption}; cursor = cursor + 1;} cursor}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn universal_postconditions_follow_result_bindings_and_reference_revisions() {
    for source in [
        "fn ceiling() -> usize ensures(forall(i: integer) where(0 <= i && i < 4) {i < integer(result)}) {8} fn main() -> usize {let n = ceiling(); proof bounds: forall(i: integer) where(0 <= i && i < 4) {i < integer(n)} by {assumption}; proof picked: 3 < integer(n) by {specialize bounds(3); omega}; let safe = n - 4; 42}",
        include_str!("../../../../examples/universal_contracts.evg"),
    ] {
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
        if source.contains("establish(&b)") {
            let stale = source.replace_evg("establish(&b);", "establish(&b); b.limit = 0;");
            assert!(verify(&stale).is_err());
            let aliased = source
                .replace_evg("fn establish(b: &Bounds)", "fn establish(b: &Bounds, a: &Bounds) where(b == a)")
                .replace_evg("establish(&b)", "establish(&b, &b)");
            assert_eq!(verify(&aliased).unwrap().run().unwrap().to_string(), "42");
        } else {
            let stale = source.replace_evg("let n = ceiling();", "let n = ceiling(); n = 0;");
            assert!(verify(&stale).is_err());
        }
    }
}

#[test]
fn admitted_universal_contracts_keep_their_subjects_and_runtime_dependencies() {
    let source = "type Bounds struct {limit: usize} fn external_bound(b: &Bounds) ensures(forall(i: integer) where(0 <= i && i < 4) {i < integer(b.limit)}) {} proof {trustme} fn require(b: &Bounds) -> usize where(forall(i: integer) where(0 <= i && i < 4) {i < integer(b.limit)}) {proof bounds: forall(i: integer) where(0 <= i && i < 4) {i < integer(b.limit)} by {assumption}; proof selected: 3 < integer(b.limit) by {specialize bounds(3); omega}; b.limit - 4} fn main() -> usize {let b = Bounds {limit: 0}; external_bound(&b); require(&b)}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        1
    );
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    // The admitted contract is false, but machine underflow itself is defined
    // to produce a type-valid value. It no longer traps in this interpreter.
    program.run().unwrap();
    let stale = source.replace_evg("external_bound(&b);", "external_bound(&b); b.limit = 0;");
    assert!(verify(&stale).is_err());
    let unrelated = source.replace_evg(
        "external_bound(&b); require(&b)",
        "external_bound(&b); let other = Bounds {limit: 0}; require(&other)",
    );
    assert!(verify(&unrelated).is_err());
    let isolated = source.replace_evg("require(&b)", "7 - b.limit");
    let program = verify(&isolated).unwrap();
    assert_eq!(
        program.function_safety_assumptions("main").unwrap().count(),
        0
    );
    assert_eq!(program.run().unwrap().to_string(), "7");
}

#[test]
fn returned_guarantees_do_not_transfer_from_discarded_argument_or_other_branch_results() {
    for (post, claim, steps) in [
        (
            "forall(i: integer) {integer(result) == 42}",
            "forall(i: integer) {integer(n) == 42}",
            "assumption",
        ),
        ("result == 42", "n == 42", "omega"),
    ] {
        let functions = format!("fn poison(p: unique(usize)) -> usize ensures({post}) {{0}} proof {{trustme}} fn clean(p: unique(usize)) -> usize {{0}} fn ignore(p: unique(usize), x: usize) -> usize {{0}}");
        let direct = format!("{functions} fn main() -> usize {{let n = poison(alloc(7)); proof kept: {claim} by {{{steps}}}; n}}");
        assert!(!verify(&direct).unwrap().trusted_assumptions().is_empty());
        for expression in [
            "{poison(alloc(7)); clean(alloc(8))}",
            "ignore(alloc(8), poison(alloc(7)))",
        ] {
            let source = format!("{functions} fn main() -> usize {{let n = {expression}; proof wrong: {claim} by {{{steps}}}; n}}");
            let error = verify(&source).unwrap_err();
            assert!(error.contains("cannot prove"), "{error}");
        }
        let branch = format!("{functions} fn test(flag: bool) -> usize {{let n = if flag {{poison(alloc(7))}} else {{clean(alloc(8))}}; proof wrong: {claim} by {{{steps}}}; n}} fn main() -> usize {{test(false)}}");
        let error = verify(&branch).unwrap_err();
        assert!(error.contains("cannot prove"), "{error}");
    }
}
