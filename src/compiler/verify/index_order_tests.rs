use super::*;

fn check(source: &str, expected: &str) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert_eq!(program.run().unwrap().to_string(), expected);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn stored_index_reads_observe_index_effects_once_through_locals_and_pointers() {
    let source = include_str!("../../../examples/index_effects.evg");
    check(source, "42");
    let pointer = source.replace(
        "let value = data[replace(&data, &calls)];",
        "let view = &data; let value = (*view)[replace(view, &calls)];",
    );
    check(&pointer, "42");
    let nested = source
        .replace(
            "fn main()",
            "type Matrix struct {rows: [[usize; 1]; 1]} fn main()",
        )
        .replace(
            "let data: [usize; 1] = [usize::MAX];",
            "let data = Matrix {rows: [[usize::MAX]]};",
        )
        .replace(
            "data[replace(&data, &calls)]",
            "data.rows[0][replace(&data.rows[0], &calls)]",
        );
    check(&nested, "42");
}

#[test]
fn an_index_write_cannot_hide_overflow_behind_the_previous_array_contents() {
    let source = include_str!("../../../examples/index_effects.evg")
        .replace("[usize::MAX]", "[0]")
        .replace("== 41", "== usize::MAX")
        .replace("[41]", "[usize::MAX]")
        .replace("proof current: value == usize::MAX;", "");
    for source in [
        source.clone(),
        source.replace(
            "let value = data[replace(&data, &calls)];",
            "let view = &data; let value = (*view)[replace(view, &calls)];",
        ),
    ] {
        let error = verify(&source).unwrap_err();
        assert!(error.contains("no overflow"), "{error}");
    }
}

#[test]
fn explicit_array_copies_and_array_rvalues_keep_their_saved_contents() {
    let source = include_str!("../../../examples/index_effects.evg")
        .replace("[usize::MAX]", "[0]")
        .replace("proof current: value == 41;", "proof snapshot: value == 0;")
        .replace("value + 1", "value + 42");
    let copied = source.replace(
        "let value = data[replace(&data, &calls)];",
        "let saved = data; let value = saved[replace(&data, &calls)];",
    );
    check(&copied, "42");
    let rvalue = source.replace(
        "let value = data[replace(&data, &calls)];",
        "let value = (if true {data} else {data})[replace(&data, &calls)];",
    );
    check(&rvalue, "42");
}

#[test]
fn index_condition_cleanup_runs_before_the_element_read() {
    let source = include_str!("../../../examples/index_cleanup.evg");
    let (program, bundle) = prove(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Reset"]);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    crate::compiler::native::emit(&program).unwrap();
    let bad = source
        .replace("[usize::MAX]", "[0]")
        .replace("== 41", "== usize::MAX")
        .replace("= 41;", "= usize::MAX;")
        .replace("proof current: value == usize::MAX;", "");
    let error = verify(&bad).unwrap_err();
    assert!(error.contains("no overflow"), "{error}");
}
