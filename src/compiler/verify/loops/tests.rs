use super::*;

#[test]
fn library_buffer_copy_uses_a_checked_loop_with_explicit_bounds() {
    let source = include_str!("../../../../examples/buffer_copy.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    let function = program
        .functions
        .iter()
        .find(|f| f.name == "vec::copy_prefix")
        .unwrap();
    assert!(!crate::compiler::effects::recursive(function));
    assert!(function
        .body
        .iter()
        .any(|statement| matches!(statement, Statement::While { .. })));
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for invalid in ["5, 1", "3, 4"] {
        let error = verify(&source.replace("3, 1", invalid)).unwrap_err();
        assert!(
            error.contains("precondition of vec::copy_prefix"),
            "{error}"
        );
    }
    for source in [
        "fn main() -> usize {let data: [usize; 1] = [42]; vec::copy_prefix(&data, &data, 1, 0); data[0]}",
        "fn main() -> usize {let source: [usize; 0] = []; let target: [usize; 0] = []; vec::copy_prefix(&source, &target, 0, 0); 42}",
    ] {
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    }
}

#[test]
fn runtime_while_checks_induction_and_replays_without_unrolling() {
    let source = include_str!("../../../../examples/while.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("count_to(42)", "count_to(usize::MAX)")).is_ok());
}

#[test]
fn loop_invariants_require_initialization_and_preservation() {
    for (source, label) in [
        ("fn main() {let x: usize = 0; while x < 42 invariant(x == 42) modifies(&x) {x = x + 1;}}", "loop invariant on entry"),
        ("fn main() {let x: usize = 0; while x < 42 invariant(x <= 41) modifies(&x) {x = x + 1;}}", "loop invariant after iteration"),
        ("fn main() {let x: usize = 0; while x <= usize::MAX invariant(true) modifies(&x) {x = x + 1;}}", "no overflow"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(label), "{error}");
    }
}

#[test]
fn loop_frame_applies_to_aliases_and_callees() {
    let source = "fn set(p: &usize) modifies(p) ensures *p == 42 {*p = 42;} fn main() {let x: usize = 0; let alias = &x; while x < 42 invariant(x <= 42) {*alias = 42;}}";
    assert!(verify(source)
        .unwrap_err()
        .contains("outside its modifies frame"));
    let call = source.replace("*alias = 42;", "set(alias);");
    assert!(verify(&call)
        .unwrap_err()
        .contains("outside its modifies frame"));
    assert!(
        verify(&source.replace("invariant(x <= 42)", "invariant(x <= 42) modifies(alias)")).is_ok()
    );
    assert!(verify(&call.replace("invariant(x <= 42)", "invariant(x <= 42) modifies(&x)")).is_ok());
}

#[test]
fn loop_does_not_export_one_iteration_or_stale_claims() {
    let prefix = "fn needs(x: usize) where x == 42 {}";
    let source = format!("{prefix} fn main() {{let x: usize = 0; while x < 10 invariant(x <= 10) modifies(&x) {{x = x + 1;}} needs(x);}}");
    assert!(verify(&source)
        .unwrap_err()
        .contains("precondition of needs"));
    let source = format!("{prefix} fn main() {{let x: usize = 43; proof admitted: x == 42 by {{trustme}}; while x > 0 invariant(true) modifies(&x) {{x = x - 1;}} needs(x);}}");
    assert!(verify(&source)
        .unwrap_err()
        .contains("precondition of needs"));
}

#[test]
fn runtime_loops_cannot_be_observed_as_total_specification_functions() {
    let source =
        "fn spin() -> bool {while true invariant(true) {} true} ideal fn bad() -> bool {spin()}";
    assert!(verify(source).is_err());
    assert!(verify("ideal fn bad() {while true invariant(true) {}}")
        .unwrap_err()
        .contains("ideal loops"));
    assert!(verify("fn main() {while false invariant(true) {return;}}").is_err());
}

#[test]
fn loops_handle_array_writes_borrowed_storage_and_iteration_locals() {
    let source = "fn fill(data: &[usize; 3]) modifies(data) {let i: usize = 0; while i < 3 invariant(i <= 3) modifies(&i, data) {let value: usize = 42; (*data)[i] = value; i = i + 1;}} fn main() -> usize {let data: [usize; 3] = [0, 0, 0]; fill(&data); data[2]}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let borrowed = "fn advance(p: &usize, limit: usize) where *p <= limit modifies(p) ensures *p == limit {while *p < limit invariant(*p <= limit) modifies(p) {*p = *p + 1;}} fn main() -> usize {let n: usize = 7; advance(&n, 42); n}";
    assert_eq!(verify(borrowed).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn nested_loops_and_cleanup_preserve_the_invariant() {
    let nested = "fn main() -> usize {let i: usize = 0; let sum: usize = 0; while i < 3 invariant(i <= 3 && integer(sum) == 14 * integer(i)) modifies(&i, &sum) {let j: usize = 0; while j < 14 invariant(j <= 14) modifies(&j) {j = j + 1;} sum = sum + j; i = i + 1;} sum}";
    assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
    let cleanup = "type Guard struct {target: &usize} impl Drop for Guard {fn drop(self) modifies(self.target) ensures *self.target == 42 {*self.target = 42;}} fn main() -> usize {let i: usize = 0; let out: usize = 0; while i < 2 invariant(i <= 2 && (i == 0 || out == 42)) modifies(&i, &out) {let guard = Guard {target: &out}; i = i + 1;} out}";
    let program = verify(cleanup).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Guard", "drop Guard"]);
    assert!(
        verify(&cleanup.replace("modifies(&i, &out)", "modifies(&i)"))
            .unwrap_err()
            .contains("outside its modifies frame")
    );
}

#[test]
fn loops_frame_unmodified_assumptions_and_track_admitted_preservation() {
    let source = "fn needs(x: usize) where x == 42 {} fn main() {let x: usize = 43; let i: usize = 0; proof admitted: x == 42 by {trustme}; while i < 2 invariant(i <= 2) modifies(&i) {i = i + 1;} needs(x);}";
    let program = verify(source).unwrap();
    assert_eq!(
        program
            .function_safety_assumptions("main")
            .unwrap()
            .map(|a| a.goal.as_str())
            .collect::<Vec<_>>(),
        ["proof admitted"]
    );
    let admitted = "fn count() -> usize ensures result == 42 {let i: usize = 0; while i < 42 invariant(i <= 42) modifies(&i) {i = 43; proof step: i <= 42 by {trustme};} i} fn main() -> usize {count()}";
    let (program, bundle) = prove(admitted).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "43");
    for name in ["count", "main"] {
        assert_eq!(
            program
                .function_safety_assumptions(name)
                .unwrap()
                .map(|a| a.goal.as_str())
                .collect::<Vec<_>>(),
            ["proof step"]
        );
    }
    assert_eq!(
        verify_with_certificate(admitted, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let stale = "fn needs(x: usize) where x == 42 {} fn main() {let i: usize = 0; while i < 42 invariant(i <= 42) modifies(&i) {i = 43; proof step: i <= 42 by {trustme};} i = i + 1; needs(i);}";
    assert!(verify(stale).unwrap_err().contains("precondition of needs"));
}

#[test]
fn loops_reject_shape_changes_and_execute_with_bounded_interpreter_fuel() {
    let shape = "fn main() {let x: usize = 0; while true invariant(true) modifies(&x) {drop(x);}}";
    assert!(verify(shape).unwrap_err().contains("plane generations"));
    let spin = verify("fn main() {while true invariant(true) {}}").unwrap();
    assert!(spin.run().unwrap_err().contains("execution step limit"));
}

#[test]
fn loop_local_facts_and_witnesses_have_lexical_scope() {
    let source = "fn main() -> usize {let i: usize = 0; fact bound = i <= 2; while i < 2 invariant(bound) modifies(&i) {fact local = i < 2; proof witness: local; i = i + 1;} fact local = i == 2; proof witness: local; 42}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    let escaped = "fn main() {let i: usize = 0; while i < 2 invariant(i <= 2) modifies(&i) {fact local = i < 2; proof witness: local; i = i + 1;} proof leak: true by {exact witness};}";
    assert!(verify(escaped).is_err());
}

#[test]
fn atomic_counter_retries_are_library_loops_without_recursive_calls() {
    let source = include_str!("../../../../examples/atomic_counter.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    assert_eq!(program.run().unwrap().to_string(), "42");
    for name in [
        "atomic_counter::increment_from",
        "atomic_counter::decrement_from",
    ] {
        let function = program.functions.iter().find(|f| f.name == name).unwrap();
        assert!(!crate::compiler::effects::recursive(function));
        assert!(crate::compiler::effects::unmeasured_loops(function));
        assert!(function.partial);
    }
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}
