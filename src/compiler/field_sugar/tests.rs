use crate::compiler::verify::{prove, verify, verify_with_certificate};

#[test]
fn scalar_refinements_reuse_checked_invariants_and_machine_layouts() {
    for source in [
        include_str!("../../../examples/refined_scalar.evg"),
        "type Byte u8 where self != 0; impl Copy for Byte {} fn id(value: Byte) -> Byte {value} fn main() -> u8 {let x: Byte = 42; let y = id(x); proof _: typeof(y) == Byte; y}",
        "type NonZero usize where self != 0; fn use_it(x: NonZero) -> usize {x} fn main() -> usize {use_it(42)}",
        "type NonZero usize where self != 0; type Pair struct {a: NonZero, b: NonZero} fn main() -> usize {let p = Pair{a: 20, b: 22}; p.a + p.b}",
        "type NonZero usize where self != 0; fn main() -> usize {let x: [NonZero; 2] = [20, 22]; x[0] + x[1]}",
        "type Truth bool where self; fn yes(x: Truth) -> bool {x} fn main() -> usize {if yes(true) {42} else {0}}",
        "type NonZero usize where self != 0; impl NonZero {method& value() -> usize {*self}} fn main() -> usize {let x: NonZero = 42; x.value()}",
    ] {
        let (program, certificate) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42", "{source}");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &certificate).unwrap().proof_search_count(), 0);
        crate::compiler::native::emit(&program).unwrap();
        // Wasm's aggregate subset is checked separately from scalar semantics.
    }
}

#[test]
fn scalar_refinements_reject_invalid_construction_assignment_and_borrowed_writes() {
    for source in [
        "type NonZero usize where self != 0; fn main() {let x: NonZero = 0;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = usize::MAX + 1;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = 1; x = 0;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = 1; x = x - 1;}",
        "type NonZero usize where self != 0; fn need(x: NonZero) {} fn main() {need(0);}",
        "type NonZero usize where self != 0; fn bad() -> NonZero {0}",
        "type NonZero usize where self != 0; fn zero(x: &usize) modifies(x) ensures *x == 0 {*x = 0;} fn main() {let x: NonZero = 1; zero(&x);}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = 1; let alias: &usize = &x; *alias = 0;}",
        "type NonZero usize where self != 0; fn bad(x: &NonZero) modifies(x) {*x = 0;}",
        "type NonZero usize where self != 0; fn main() {let x: usize = 1; let claimed: &NonZero = &x;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = 1; let moved = x; let again = x;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = 1; let y: u8 = x;}",
        "type Truth bool where self; fn main() {let x: Truth = false;}",
        "type Pointer &usize where true; fn main() {}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}
