//! Lean emission acceptance and rejection regressions.

use super::*;

#[test]
fn emits_contract_and_facts() {
    let s = emit(
        "ideal fn inc(n: nat) -> nat ensures (result > n) { proof h: n + 1 > n by { omega }; n + 1 }",
        false,
    )
    .unwrap();
    assert!(s.contains("{ result : Nat // (result > n) }"));
    assert!(s.contains("have h : ((n + 1) > n) := by omega"));
}

#[test]
fn emits_bounds_obligation() {
    let s = emit(
        "ideal fn at(n: nat, a: [int; n], i: nat) -> int where (i < n) { a[i] }",
        false,
    )
    .unwrap();
    assert!(s.contains("Vector (Int) (n)"));
    assert!(s.contains("[i]'(by omega)"));
}

#[test]
fn rejects_escape_hatches() {
    for tactic in ["sorry", "admit", "native_decide", "axiom", "exact missing"] {
        assert!(emit(
            &format!("ideal fn f() -> nat ensures (result == 1) {{ 0 }} proof {{ {tactic} }}"),
            false
        )
        .is_err());
    }
}

#[test]
fn rejects_bad_programs() {
    for s in [
        "",
        "ideal fn f() -> nat { missing }",
        "ideal fn f() -> nat { 1 / 0 }",
        "ideal fn f() -> nat { 1 } ideal fn f() -> nat { 2 }",
        "ideal fn f() -> nat { let x = 1; let x = 2; x }",
        "type Vec<T> struct {}",
    ] {
        assert!(emit(s, false).is_err(), "{s}");
    }
}

#[test]
fn run_requires_entrypoint() {
    assert!(emit("ideal fn f() -> nat { 1 }", true).is_err());
}

#[test]
fn comments_and_precedence() {
    let s = emit("// comment\nideal fn main() -> int { 1 + 2 * 3 }", true).unwrap();
    assert!(s.contains("(1 + (2 * 3))"));
    assert!(s.contains("#eval main"));
}
