//! Interpreter execution, ownership, and cleanup regressions.
use super::{copy_value, Value};
#[test]
fn aggregate_copy_work_is_charged_before_cloning() {
    let value = Value::Array(vec![Value::Bool(true); 64]);
    let mut fuel = 64;
    assert!(copy_value(&value, &mut fuel)
        .unwrap_err()
        .contains("value-work"));
    assert_eq!(fuel, 64);
    fuel = 65;
    assert_eq!(copy_value(&value, &mut fuel).unwrap(), value);
    assert_eq!(fuel, 0);
    let values = vec!["1"; 2048].join(",");
    let source = format!("fn repeat(n: usize, data: [usize; 2048]) -> usize where(data[0] == 1) ensures(result == 1) decreases(n) {{if n == 0 {{data[0]}} else {{repeat(n - 1, data)}}}} fn main() -> usize {{let data: [usize; 2048] = [{values}]; repeat(40, data)}}");
    let program = verify(&source).unwrap();
    let error = program.run().unwrap_err();
    assert!(error.contains("value-work"), "{error}");
}

#[test]
fn unused_owned_temporaries_are_dropped_at_the_statement() {
    let declarations = include_str!("../../examples/borrowed_temporaries.evg")
        .split("fn main()")
        .next()
        .unwrap();
    let proof_only = format!("{declarations}\nfn main() -> usize {{fact unused_false = first().tag == 0; proof erased: First {{tag: 1}}.tag == 1; 42}}");
    let (_, events) = verify(&proof_only).unwrap().run_with_events().unwrap();
    assert!(events.is_empty());
    let (value, events) = verify(include_str!("../../examples/borrowed_temporaries.evg"))
        .unwrap()
        .run_with_events()
        .unwrap();
    assert_eq!(value.to_string(), "6");
    assert_eq!(
        events,
        [
            "drop Second",
            "drop First",
            "drop First",
            "drop Second",
            "drop First",
            "drop Third"
        ]
    );
    let (_, events) = verify(include_str!("../../examples/temporary_cleanup.evg"))
        .unwrap()
        .run_with_events()
        .unwrap();
    assert_eq!(events, ["drop Second", "drop First", "drop First"]);
    let declarations = "type Resource struct {} impl Drop for Resource {fn drop(self){}} fn make() -> Resource {Resource {}}";
    for body in [
        "Resource {}; 0",
        "[Resource {}]; 0",
        "make(); 0",
        "let r = Resource {}; move(r); 0",
        "let r = Resource {}; drop(r); 0",
        "let r = Resource {}; if true {move(r)} else {move(r)}; 0",
    ] {
        let (_, events) = verify(&format!("{declarations}\nfn main() -> usize {{{body}}}"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(events, ["drop Resource"], "{body}");
    }
    let declarations = "type First struct {} impl Drop for First {fn drop(self){}} type Second struct {} impl Drop for Second {fn drop(self){}}";
    let (_, events) = verify(&format!(
        "{declarations}\nfn main() -> usize {{let later = Second {{}}; First {{}}; 0}}"
    ))
    .unwrap()
    .run_with_events()
    .unwrap();
    assert_eq!(events, ["drop First", "drop Second"]);
}

use crate::compiler::verify::verify;
#[test]
fn executes_verified_calls_arrays_and_branches() {
    let s = "fn abs(n: isize) -> isize where (n > isize::MIN) ensures (result >= 0) { if n >= 0 { n } else { -n } } fn main() -> isize { let a: [isize; 2] = [-4, 8]; abs(a[0]) }";
    assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "4");
    assert_eq!(
        verify(include_str!("../../examples/contracts.evg"))
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
        "42"
    );
}
#[test]
fn recursive_execution_fails_before_exhausting_the_host_stack() {
    let source = "fn count(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {count(n - 1) + 1}} fn main() -> usize {count(1000)}";
    let error = verify(source).unwrap().run().unwrap_err();
    assert!(
        error.contains("execution expression depth limit")
            || error.contains("execution call depth limit"),
        "{error}"
    );
}
#[test]
fn false_entry_precondition_cannot_execute() {
    assert!(verify("fn main() -> usize where (false) { 1 }")
        .unwrap()
        .run()
        .is_err());
}
#[test]
fn ideal_math_is_never_executed_by_the_runtime() {
    let source = format!(
        "ideal fn double(n: int) -> int {{ n + n }} ideal fn main() -> int {{ double({}) }}",
        i128::MAX
    );
    assert!(verify(&source).unwrap().run().is_err());
}

#[test]
fn updates_do_not_drop_the_parent_or_its_owned_fields() {
    let (value, events) = verify(include_str!("../../examples/drop.evg"))
        .unwrap()
        .run_with_events()
        .unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Pair", "drop Resource"]);
}

#[test]
fn moves_and_reassignment_drop_each_resource_once() {
    let prefix = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self) {proof valid: self.tag == 7;}} ";
    for body in [
        "let a = Resource {tag: 7}; let b = a; a = Resource {tag: 7}; drop(b); 0",
        "let a = Resource {tag: 7}; a = Resource {tag: 7}; 0",
    ] {
        let (_, events) = verify(&format!("{prefix} fn main() -> usize {{ {body} }}"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(events, ["drop Resource", "drop Resource"]);
    }
    let source = format!("{prefix} fn make() -> Resource {{Resource {{tag: 7}}}} fn consume(r: Resource) -> usize {{r.tag}} fn main() -> usize {{let r = make(); consume(r)}}");
    let (value, events) = verify(&source).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "7");
    assert_eq!(events, ["drop Resource"]);
}

#[test]
fn scope_cleanup_runs_in_reverse_binding_order() {
    let source = "type First struct {} impl Drop for First {fn drop(self){}} type Second struct {} impl Drop for Second {fn drop(self){}} fn main() -> usize {let a = First {}; let b = Second {}; 0}";
    let (_, events) = verify(source).unwrap().run_with_events().unwrap();
    assert_eq!(events, ["drop Second", "drop First"]);
}

#[test]
fn destructured_owned_fields_are_cleaned_up_once() {
    let source = "type First struct {} impl Drop for First {fn drop(self){}} type Second struct {} impl Drop for Second {fn drop(self){}} type Pair struct {left: First, right: Second} fn main() -> usize {let p = Pair {left: First {}, right: Second {}}; let Pair {left, right} = p; 0}";
    let (_, events) = verify(source).unwrap().run_with_events().unwrap();
    assert_eq!(events, ["drop Second", "drop First"]);
    let source = source.replace(
        "let Pair {left, right} = p;",
        "let Pair {left, right} = p; drop(left);",
    );
    let (_, events) = verify(&source).unwrap().run_with_events().unwrap();
    assert_eq!(events, ["drop First", "drop Second"]);
}
