use super::*;

#[test]
fn measured_runtime_loops_prove_termination_and_replay() {
    let source = "fn count(limit: usize) -> usize ensures result == limit {let value: usize = 0; while value < limit invariant(value <= limit) modifies(&value) decreases(limit - value) {value = value + 1;} value} fn main() -> usize {count(42)}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.potentially_diverging_functions().count(), 0);
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    let replay = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replay.proof_search_count(), 0);
    assert_eq!(replay.potentially_diverging_functions().count(), 0);
    assert!(verify(&source.replace("count(42)", "count(usize::MAX)")).is_ok());
    let ideal = source.replace(
        "decreases(limit - value)",
        "decreases(integer(limit) - integer(value))",
    );
    assert_eq!(verify(&ideal).unwrap().run().unwrap().to_string(), "42");
    let proof_call = source.replace(
        "fn main() -> usize {count(42)}",
        "fn main() -> usize {proof total_contract: count(42) == 42; 42}",
    );
    verify(&proof_call).unwrap();
}

#[test]
fn loop_measures_require_nonnegative_integer_heads_and_strict_progress() {
    for (measure, label) in [
        ("0", "strictly decreasing loop measure"),
        ("value", "strictly decreasing loop measure"),
        ("-integer(value) - 1", "nonnegative loop measure"),
        ("true", "loop measure must be an integer"),
    ] {
        let source = format!("fn main() {{let value: usize = 0; while value < 42 invariant(value <= 42) modifies(&value) decreases({measure}) {{value = value + 1;}}}}");
        let error = verify(&source).unwrap_err();
        assert!(error.contains(label), "{measure}: {error}");
    }
    let plateau = "fn main() {let value: usize = 0; while value < 42 invariant(value <= 42) modifies(&value) decreases(42 - value) {value = value;}}";
    assert!(verify(plateau)
        .unwrap_err()
        .contains("strictly decreasing loop measure"));
}

#[test]
fn loop_progress_includes_iteration_local_destructors() {
    let source = "type Reset struct {target: &usize} impl Drop for Reset {fn drop(self) modifies(self.target) ensures *self.target == 0 {*self.target = 0;}} fn main() {let value: usize = 0; while value < 2 invariant(value <= 2) modifies(&value) decreases(2 - value) {let reset = Reset {target: &value}; value = value + 1;}}";
    let error = verify(source).unwrap_err();
    assert!(
        error.contains("strictly decreasing loop measure"),
        "{error}"
    );
}

#[test]
fn a_ranking_function_does_not_make_a_divergent_body_total() {
    for body in [
        "spin(); value = value + 1;",
        "while true invariant(true) {} value = value + 1;",
    ] {
        let source = format!("fn spin() {{spin();}} fn main() {{let value: usize = 0; while value < 42 invariant(value <= 42) modifies(&value) decreases(42 - value) {{{body}}}}}");
        let program = verify(&source).unwrap();
        assert!(program
            .potentially_diverging_functions()
            .any(|name| name == "main"));
    }
}

#[test]
fn loop_measures_cannot_write_storage_or_call_partial_functions() {
    for metric in ["change(&value)", "spin()"] {
        let source = format!("fn change(p: &usize) -> usize modifies(p) {{*p = 0; 0}} fn spin() -> usize {{spin()}} fn main() {{let value: usize = 0; while value < 42 invariant(value <= 42) modifies(&value) decreases({metric}) {{value = value + 1;}}}}");
        assert!(verify(&source).is_err(), "accepted {metric}");
    }
}

#[test]
fn ranking_expressions_resolve_source_dependencies_and_entry_snapshots() {
    let source = "module rank {ideal fn remaining(limit: usize, value: usize) -> nat where value <= limit ensures result == nat(limit) - nat(value) {nat(limit) - nat(value)} fn run(limit: usize) -> usize ensures result == limit {let value: usize = 0; while value < limit invariant(value <= limit) modifies(&value) decreases(remaining(old(limit), value)) {value = value + 1;} value}} fn main() -> usize {rank::run(42)}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.potentially_diverging_functions().count(), 0);
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn loop_measures_follow_pointer_revisions_and_method_sugar() {
    for source in [
        "fn count(value: &usize, limit: usize) where *value <= limit modifies(value) ensures *value == limit {while *value < limit invariant(*value <= limit) modifies(value) decreases(integer(limit) - integer(*value)) {*value = *value + 1;}} fn main() -> usize {let value: usize = 0; count(&value, 42); value}",
        "type Limit struct {value: usize} impl Limit {method& bound() -> usize ensures result == self.value {self.value}} fn main() -> usize {let limit = Limit {value: 42}; let value: usize = 0; while value < limit.value invariant(value <= limit.value) modifies(&value) decreases(limit.bound() - value) {value = value + 1;} value}",
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.potentially_diverging_functions().count(), 0);
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn admitted_progress_remains_an_explicit_safety_dependency() {
    let source = "ideal fn rank(value: usize) -> nat ensures result == nat(value) {if value == 0 {0} else {1}} proof {trustme} fn claimed() -> usize {let value: usize = 0; while value < 42 invariant(value <= 42) modifies(&value) decreases(rank(42 - value)) {value = value + 1;} value} fn main() -> usize {claimed()}";
    // A symbolic branch falls back to the admitted contract, so progress
    // depends on that admission. A visibly constant rank cannot decrease:
    // its contradictory postcondition must not prove unrelated arithmetic.
    let constant_rank = source.replace("{if value == 0 {0} else {1}}", "{0}");
    let error = verify(&constant_rank).unwrap_err();
    assert!(
        error.contains("strictly decreasing loop measure"),
        "{error}"
    );
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    for name in ["claimed", "main"] {
        assert_eq!(
            program.function_safety_assumptions(name).unwrap().count(),
            1
        );
    }
    let replay = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replay.proof_search_count(), 0);
    assert_eq!(
        replay.function_safety_assumptions("main").unwrap().count(),
        1
    );
    let unrelated = source.replace(
        "fn main() -> usize {claimed()}",
        "fn needs(value: usize) where value == 42 {} fn main() {claimed(); needs(43);}",
    );
    assert!(verify(&unrelated)
        .unwrap_err()
        .contains("precondition of needs"));
}
