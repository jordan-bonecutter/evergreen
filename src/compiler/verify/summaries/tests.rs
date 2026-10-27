//! Cross-function trust provenance, independent of proof-cache annotations.

use super::*;

fn safety(program: &VerifiedProgram, name: &str) -> Vec<String> {
    program
        .function_safety_assumptions(name)
        .unwrap()
        .map(|a| a.goal.clone())
        .collect()
}
fn contract(program: &VerifiedProgram, name: &str) -> Vec<String> {
    program
        .function_contract_assumptions(name)
        .unwrap()
        .map(|a| a.goal.clone())
        .collect()
}

#[test]
fn unused_admission_does_not_taint_callee_or_caller_summary() {
    let source = "fn clean() -> usize ensures result == 42 {proof unused: false by {trustme}; 42} fn main() -> usize ensures result == 42 {clean()}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.trusted_assumptions().len(), 1);
    for name in ["clean", "main"] {
        assert!(safety(&program, name).is_empty());
        assert!(contract(&program, name).is_empty());
    }
    let replay = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replay.proof_search_count(), 0);
    assert!(contract(&replay, "main").is_empty());
}

#[test]
fn postcondition_admission_is_distinct_from_runtime_safety() {
    let source = "fn trusted() -> usize ensures result == 42 {43} proof {trustme} fn ignored() -> usize {let unused = trusted(); 0} fn main() -> usize ensures result == 42 {trusted()}";
    let (program, bundle) = prove(source).unwrap();
    for name in ["trusted", "ignored", "main"] {
        assert!(safety(&program, name).is_empty());
    }
    assert_eq!(
        contract(&program, "trusted"),
        vec!["postcondition of trusted"]
    );
    assert!(contract(&program, "ignored").is_empty());
    assert_eq!(contract(&program, "main"), vec!["postcondition of trusted"]);
    let replay = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replay.proof_search_count(), 0);
    assert_eq!(contract(&replay, "main"), contract(&program, "main"));
}

#[test]
fn false_callee_postcondition_does_not_erase_unrelated_obligations() {
    let source = "fn invalid() ensures false {} proof {trustme} fn needs(value: usize) where value == 42 {} fn main() {invalid(); needs(43);}";
    assert!(verify(source)
        .unwrap_err()
        .contains("precondition of needs"));
}

#[test]
fn runtime_safety_dependencies_flow_through_calls() {
    let source = "fn needs(value: usize) where value == 42 {} fn admitted(value: usize) {proof assumed: value == 42 by {trustme}; needs(value);} fn middle() {admitted(43);} fn main() {middle();}";
    let (program, bundle) = prove(source).unwrap();
    for name in ["admitted", "middle", "main"] {
        assert_eq!(safety(&program, name), vec!["proof assumed"]);
        assert_eq!(contract(&program, name), vec!["proof assumed"]);
    }
    let replay = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replay.proof_search_count(), 0);
    assert_eq!(safety(&replay, "main"), safety(&program, "main"));
}

#[test]
fn binding_a_trusted_call_result_does_not_preserve_it_across_a_write() {
    let prefix = "fn trusted() -> usize ensures result == 42 {43} proof {trustme} fn needs(value: usize) where value == 42 {}";
    let good = format!("{prefix} fn main() {{let x = trusted(); needs(x);}}");
    assert_eq!(
        safety(&verify(&good).unwrap(), "main"),
        ["postcondition of trusted"]
    );
    let nested = format!("{prefix} fn main() {{needs(trusted());}}");
    assert_eq!(
        safety(&verify(&nested).unwrap(), "main"),
        ["postcondition of trusted"]
    );
    for write in ["x = x;", "let alias = &x; *alias = *alias;"] {
        let bad = format!("{prefix} fn main() {{let x = trusted(); needs(x); {write} needs(x);}}");
        assert!(verify(&bad).unwrap_err().contains("precondition of needs"));
    }
}

#[test]
fn a_false_post_about_a_parameter_cannot_poison_its_next_revision() {
    let source = "fn needs(value: usize) where value == 42 ensures value == 42 {} fn test(value: usize) where value == 43 {proof admitted: value == 42 by {trustme}; needs(value); value = value + 1; needs(value);} fn main() {}";
    assert!(verify(source)
        .unwrap_err()
        .contains("precondition of needs"));
}

#[test]
fn external_safety_is_inherited_even_when_the_result_is_ignored() {
    let source = "extern syscall(39) fn pid() -> isize ensures result > 0; proof {trustme} fn middle() {pid();} fn main() {middle();}";
    let (program, bundle) = prove(source).unwrap();
    for name in ["pid", "middle", "main"] {
        assert_eq!(safety(&program, name), ["external contract for pid"]);
    }
    assert_eq!(
        safety(&verify_with_certificate(source, &bundle).unwrap(), "main"),
        safety(&program, "main")
    );
}

#[test]
fn a_branch_overwrite_does_not_reuse_the_pre_branch_admission() {
    let prefix = "fn set(p: &usize, value: usize) -> usize modifies(p) ensures *p == value {*p = value; 0} fn needs(value: usize) where value == 42 {}";
    for expression in [
        "if choice {set(&x, 999)} else {set(&x, 999)}",
        "if true {set(&x, 999)} else {0}",
        "if choice {set(&x, 999)} else {0}",
    ] {
        let source = format!("{prefix} fn test(x: usize, choice: bool) where x == 43 {{proof admitted: x == 42 by {{trustme}}; let ignored = {expression}; needs(x);}} fn main() {{}}");
        assert!(verify(&source)
            .unwrap_err()
            .contains("precondition of needs"));
    }
}

#[test]
fn exchange_new_contents_do_not_use_the_old_result_clause() {
    let source = "fn exchange(p: &usize, with: usize) -> usize modifies(p) ensures result == old(*p) && *p == with {let before = *p; *p = with; before} proof {trustme} fn needs(value: usize) where value == 42 {} fn test(x: usize) where x == 43 {proof admitted: x == 42 by {trustme}; let old_value = exchange(&x, 999); needs(x);} fn main() {}";
    assert!(verify(source)
        .unwrap_err()
        .contains("precondition of needs"));
}
