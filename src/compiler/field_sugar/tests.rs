use crate::compiler::verify::{prove, verify, verify_with_certificate};

#[test]
fn scalar_refinements_reuse_checked_invariants_and_machine_layouts() {
    for source in [
        include_str!("../../../examples/refined_scalar.evg"),
        "type Pointer &usize where *self != 0; fn make(n: &usize) -> Pointer where *n != 0 borrows(n) {Pointer(n)} fn main() -> usize {let n: usize = 42; let p = make(&n); *p}",
        "type Byte u8 where self != 0; impl Copy for Byte {} fn id(value: Byte) -> Byte {value} fn main() -> u8 {let x: Byte = Byte(42); let y = id(x); proof _: typeof(y) == Byte; y}",
        "type NonZero usize where self != 0; fn use_it(x: NonZero) -> usize {x} fn main() -> usize {use_it(NonZero(42))}",
        "type NonZero usize where self != 0; type Pair struct {a: NonZero, b: NonZero} fn main() -> usize {let p = Pair{a: NonZero(20), b: NonZero(22)}; p.a + p.b}",
        "type NonZero usize where self != 0; fn main() -> usize {let x: [NonZero; 2] = [NonZero(20), NonZero(22)]; x[0] + x[1]}",
        "type Truth bool where self; fn yes(x: Truth) -> bool {x} fn main() -> usize {if yes(Truth(true)) {42} else {0}}",
        "type NonZero usize where self != 0; impl NonZero {method& value() -> usize {*self}} fn main() -> usize {let x: NonZero = NonZero(42); x.value()}",
    ] {
        let program = verify(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42", "{source}");
        assert!(program.trusted_assumptions().is_empty());
    }
    // Replay one representative example; backend execution has its own tests.
    let source = include_str!("../../../examples/refined_scalar.evg");
    let (_, certificate) = prove(source).unwrap();
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn scalar_refinements_reject_invalid_construction_assignment_and_borrowed_writes() {
    for source in [
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(0);}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(usize::MAX + 1);}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(1); x = 0;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(1); x = x - 1;}",
        "type NonZero usize where self != 0; fn need(x: NonZero) {} fn main() {need(0);}",
        "type NonZero usize where self != 0; fn bad() -> NonZero {0}",
        "type NonZero usize where self != 0; fn zero(x: &usize) modifies(x) ensures *x == 0 {*x = 0;} fn main() {let x: NonZero = NonZero(1); zero(&x);}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(1); let alias: &usize = &x; *alias = 0;}",
        "type NonZero usize where self != 0; fn bad(x: &NonZero) modifies(x) {*x = 0;}",
        "type NonZero usize where self != 0; fn main() {let x: usize = 1; let claimed: &NonZero = &x;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(1); let moved = x; let again = x;}",
        "type NonZero usize where self != 0; fn main() {let x: NonZero = NonZero(1); let y: u8 = x;}",
        "type Truth bool where self; fn main() {let x: Truth = Truth(false);}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn refinements_generalize_construction_without_implicit_wrapping() {
    let source = "type Ordered<T> [T; 2] where self[0] < self[1]; fn main() -> usize {let p = Ordered::<usize>([20, 22]); p[0] + p[1]}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("[20, 22]", "[22, 20]")).is_err());
    let error =
        verify("type NonZero usize where self != 0; fn make(x: usize) -> NonZero {x}").unwrap_err();
    assert!(error.contains("expected NonZero, got usize"), "{error}");
}

#[test]
fn option_tag_equivalence_checks_union_state() {
    let source = "type Option<T> struct {data: T | shape(T), ok: bool} where self.ok <=> typeof(self.data) == T; fn main() -> usize {let x = Option::<usize>{data: 42, ok: true}; let Option::<usize>{data, ok} = x; let value: usize = data; value}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("ok: true", "ok: false")).is_err());
}
