//! Small independent concrete oracle for interactions in the symbolic heap.

use crate::syntax::format::test_edit::SourceEdit;

use super::*;

fn expected(first: usize, second: usize, queried: usize, flag: bool) -> usize {
    let mut model = [7usize, 9];
    model[first] = 42;
    if flag {
        model[second] = 13;
    }
    model[queried]
}

pub(crate) fn concrete_cases() -> Vec<(String, usize)> {
    let mut cases = Vec::new();
    for first in 0..2 {
        for second in 0..2 {
            for queried in 0..2 {
                for flag in [false, true] {
                    let expected = expected(first, second, queried, flag);
                    for warmed in [false, true] {
                        for aliased_call in [false, true] {
                            let mirror = if aliased_call {
                                ", mirror: &[usize; 2]"
                            } else {
                                ""
                            };
                            let actual = if aliased_call { ", &data" } else { "" };
                            let borrow = format!("let chosen = &data[{queried}];");
                            let (early, late) = if warmed {
                                (borrow.as_str(), "")
                            } else {
                                ("", borrow.as_str())
                            };
                            let source = format!(
                                r#"
fn put(data: &[usize; 2]{mirror}, index: usize, value: usize)
where(index < 2) modifies(&(*data)[index])
ensures((*data)[index] == value) {{(*data)[index] = value;}}
fn main() -> usize ensures(result == {expected}) {{
    let data: [usize; 2] = [7, 9];
    let flag: bool = {flag};
    {early}
    data[{first}] = 42;
    let guarded = if flag {{data[{queried}]}} else {{0}};
    let effect = if flag {{put(&data{actual}, {second}, 13)}} else {{()}};
    {late}
    *chosen
}}
"#
                            );
                            cases.push((source, expected));
                        }
                    }
                }
            }
        }
    }
    cases
}

pub(crate) fn record_cases() -> Vec<(String, usize)> {
    let mut cases = Vec::new();
    for first in 0..2 {
        for second in 0..2 {
            for queried in 0..2 {
                for flag in [false, true] {
                    let mut model = [(7usize, 9usize), (11, 17)];
                    model[first].0 = 42;
                    if flag {
                        model[second].1 = 13;
                    }
                    let expected = model[queried].0 + model[queried].1;
                    let source = format!(
                        r#"
type Cell struct {{left: usize, right: usize}}
fn put(data: &[Cell; 2], mirror: &[Cell; 2], index: usize)
where(index < 2) modifies(&(*data)[index].right)
ensures((*data)[index].right == 13) {{(*data)[index].right = 13;}}
fn main() -> usize ensures(result == {expected}) {{
    let data: [Cell; 2] = [Cell {{left: 7, right: 9}}, Cell {{left: 11, right: 17}}];
    let selected = &data[{queried}].left;
    data[{first}].left = 42;
    let flag: bool = {flag};
    let first_read = if flag {{data[{queried}].right}} else {{0}};
    let effect = if flag {{put(&data, &data, {second})}} else {{()}};
    *selected + data[{queried}].right
}}
"#
                    );
                    cases.push((source, expected));
                }
            }
        }
    }
    cases
}

fn check_case(source: &str, expected: usize) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        program.run().unwrap().to_string(),
        expected.to_string(),
        "{source}"
    );
    let replayed = verify_with_certificate(source, &bundle).unwrap();
    assert_eq!(replayed.proof_search_count(), 0);
    let wrong = source.replace_evg(
        format!("ensures(result == {expected})"),
        &format!("ensures(result == {})", expected + 1),
    );
    let error = verify(&wrong).unwrap_err();
    assert!(error.contains("postcondition of main"), "{error}\n{wrong}");
}

#[test]
fn small_array_model_agrees_with_proofs_execution_and_replay() {
    for (source, expected) in concrete_cases() {
        check_case(&source, expected);
    }
    // One proof of the symbolic helper; this main observes all sixteen input
    // combinations and returns a failure count without cancellation or wrapping.
    check_case(include_str!("../../../examples/array_model.evg"), 42);
}

#[test]
fn record_fields_agree_with_independent_model_and_wrong_contracts_fail() {
    for (source, expected) in record_cases() {
        check_case(&source, expected);
    }
}

#[test]
#[ignore = "exhaustive symbolic-entry proof audit; run explicitly"]
fn symbolic_array_entries_each_reject_a_wrong_contract() {
    let definitions = include_str!("../../../examples/array_model.evg")
        .split("fn main")
        .next()
        .unwrap();
    for first in 0..2 {
        for second in 0..2 {
            for queried in 0..2 {
                for flag in [false, true] {
                    let expected = expected(first, second, queried, flag);
                    let source = format!("{definitions} fn main() -> usize ensures(result == {expected}) {{scenario({flag}, {first}, {second}, {queried})}}");
                    check_case(&source, expected);
                }
            }
        }
    }
}
