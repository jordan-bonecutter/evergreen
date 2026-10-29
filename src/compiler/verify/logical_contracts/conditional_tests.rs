use super::*;

const SOURCE: &str = r#"
fn inspect(flag: bool, left: &[usize; 4], right: &[usize; 4])
where if flag {
    forall(i: integer) where (0 <= i && i < 4) {(*left)[i] == 42}
} else {
    forall(i: integer) where (0 <= i && i < 4) {(*right)[i] == 7}
}
{
    if flag {
        proof live: forall(i: integer) where (0 <= i && i < 4) {(*left)[i] == 42} by {assumption};
        proof first: (*left)[0] == 42;
    } else {
        proof live: forall(i: integer) where (0 <= i && i < 4) {(*right)[i] == 7} by {assumption};
        proof first: (*right)[0] == 7;
    }
}
fn main() -> usize {
    let left: [usize; 4] = [42, 42, 42, 42];
    let right: [usize; 4] = [7, 7, 7, 7];
    inspect(true, &left, &right);
    inspect(false, &left, &right);
    42
}
"#;

fn replay(source: &str) -> VerifiedProgram {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    program
}

#[test]
fn conditional_ranges_are_selected_on_demand_with_checked_elimination() {
    assert_eq!(replay(SOURCE).run().unwrap().to_string(), "42");
    let nested = SOURCE
        .replace(
            "where if flag {\n    forall",
            "where if flag {\n    true && (forall",
        )
        .replace(
            "{(*left)[i] == 42}\n} else",
            "{(*left)[i] == 42}) && true\n} else",
        );
    assert_eq!(replay(&nested).run().unwrap().to_string(), "42");
}

#[test]
fn conditional_ranges_require_the_correct_guard_and_current_revisions() {
    let declaration = SOURCE.split("fn main()").next().unwrap();
    let wrong_branch = declaration.replacen("    if flag {", "    if !flag {", 1);
    assert!(verify(&wrong_branch).is_err());
    let stale_guard = declaration.replacen("    if flag {", "    flag = !flag; if flag {", 1);
    assert!(verify(&stale_guard).is_err());
    let stale_data = declaration
        .replace("\n{\n    if flag", "\nmodifies(left)\n{\n    if flag")
        .replace("        proof live:", "        (*left)[0] = 0; proof live:");
    assert!(verify(&stale_data).is_err());
    let unguarded = declaration.replace("    if flag {", "    if true {");
    assert!(verify(&unguarded).is_err());
}

#[test]
fn conditional_projection_does_not_use_admitted_guards_or_guarantees() {
    let declaration = SOURCE.split("fn main()").next().unwrap();
    let admitted_guard = declaration.replace(
        "    if flag {",
        "    proof assume_flag: flag by {trustme}; if true {",
    );
    assert!(verify(&admitted_guard).is_err());
    let admitted_source = r#"fn inspect(flag: bool, data: &[usize; 4]) {
        proof assumed: if flag {forall(i: integer) where(0 <= i && i < 4) {(*data)[i] == 42}} else {true} by {trustme};
        if flag {
            proof live: forall(i: integer) where(0 <= i && i < 4) {(*data)[i] == 42} by {assumption};
        }
    }"#;
    assert!(verify(admitted_source).is_err());
}
