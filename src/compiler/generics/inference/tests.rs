use crate::compiler::verify::{prove, verify, verify_with_certificate};

#[test]
fn typed_inputs_infer_free_function_and_record_arguments() {
    for source in [
        include_str!("../../../../examples/inferred_generics.evg"),
        "fn identity<T>(value: T) -> T {value} fn main() -> u8 {let value: u8 = 42; identity(value)}",
        "fn identity<T = usize>(value: T) -> T {value} fn main() -> i8 {let value: i8 = 42; identity(value)}",
        "fn identity<T>(value: T) -> T {value} fn byte() -> u8 {42} fn main() -> u8 {identity(identity(byte()))}",
        "fn view<T>(value: &T) -> &T borrows(value) {value} fn main() -> usize {let value: usize = 42; *view(&value)}",
        "type Box<T> struct {value: T} fn get<T>(value: Box<T>) -> T {value.value} fn main() -> u8 {let value: u8 = 42; let boxed = Box {value: value}; get(boxed)}",
        "type Box<T> struct {value: T} fn identity<T>(value: T) -> T {value} fn main() -> u8 {let box = Box::<u8> {value: 42}; identity(box.value)}",
        "fn first<T, const N: usize>(values: &[T; N]) -> T where N > 0 {(*values)[0]} fn main() -> u8 {let values: [u8; 2] = [42, 7]; first(&values)}",
        "type Box<T, const N: usize> struct {values: [T; N]} fn first<T, const N: usize>(value: Box<T, N>) -> T where N > 0 {value.values[0]} fn main() -> u8 {let value = Box::<u8, 2> {values: [42, 7]}; first(value)}",
        "fn identity<T>(value: T) -> T {value} fn main() -> u8 {identity({let value: u8 = 42; value})}",
        "fn identity<T = usize>(value: T) -> T {value} fn main() -> usize {identity(42)}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
        crate::compiler::native::emit(&program).unwrap();
    }
}

#[test]
fn ideal_numeric_views_infer_their_input_types() {
    verify("fn main() {let value: i8 = -7; proof _: integer::from(value) == -7; let positive: u16 = 42; proof _: nat::from(positive) == 42;}").unwrap();
}

#[test]
fn inferred_instances_keep_contracts_and_ownership_checks() {
    for source in [
        "fn duplicate<T>(value: T) -> T {let other = value; value} fn main() {let pointer: unique(usize) = alloc(42); duplicate(pointer);}",
        "fn view<T>(value: &T) -> &T borrows(value) {value} fn escape() -> &usize {let local: usize = 42; view(&local)} fn main() {}",
        "fn nonzero<T>(value: T) -> T where value != 0 {value} fn main() {let value: u8 = 0; nonzero(value);}",
        "fn wrong<T>(value: T) -> T {proof _: false; value} fn main() {let value: u8 = 42; wrong(value);}",
        "type Nonzero<T> struct {value: T} where value != 0; fn main() {let zero: usize = 0; let value = Nonzero {value: zero};}",
        "fn identity<T>(value: T) -> T {value} fn main() {let pointer: unique(usize) = alloc(42); let moved = identity(pointer); identity(pointer);}",
        "fn main() {let negative: i8 = -7; proof _: nat::from(negative) == 0;}",
        "fn main() {let flag: bool = true; proof _: integer::from(flag) == 1;}",
        "fn main() -> integer {let byte: u8 = 42; integer::from(byte)}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
    let program = verify("fn identity<T>(value: T) -> T {value} fn main() -> usize {let pointer: unique(usize) = alloc(42); let moved = identity(pointer); *moved}").unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
}

#[test]
fn inference_rejects_conflicts_and_runtime_const_extents() {
    for (source, expected) in [
        ("fn same<T>(a: T, b: T) {} fn main() {let a: u8 = 1; let b: u16 = 1; same(a, b);}", "conflicting inferred arguments for T"),
        ("fn same<const N: usize>(a: &[u8; N], b: &[u8; N]) {} fn main() {let a: [u8; 2] = [1, 2]; let b: [u8; 3] = [1, 2, 3]; same(&a, &b);}", "conflicting inferred arguments for N"),
        ("fn first<const N: usize>(data: &[u8; N]) {} fn dynamic(n: usize, data: linear_plane(u8, n)) {first(data);} fn main() {}", "closed compile-time"),
        ("fn identity<T>(value: T) -> T {value} fn main() {identity(42);}", "cannot infer generic argument T"),
    ] {
        let error = verify(source).unwrap_err();
        assert!(error.contains(expected), "{error}\n{source}");
    }
    // An explicit type remains authoritative even when an argument's type disagrees.
    assert!(verify("fn identity<T>(value: T) -> T {value} fn main() {let value: u8 = 42; identity::<u16>(value);}").is_err());
}

#[test]
fn inferred_shapes_cross_methods_destructures_and_nested_scopes() {
    for source in [
        "type Box<T> struct {value: T} impl<T> Box<T> {method& get() -> T {self.value}} fn identity<T>(value: T) -> T {value} fn main() -> u8 {let boxed = Box::<u8> {value: 42}; identity(boxed.get())}",
        "type Box<T> struct {value: T} fn identity<T>(value: T) -> T {value} fn main() -> u8 {let boxed = Box::<u8> {value: 42}; let Box {value} = boxed; identity(value)}",
        "fn identity<T>(value: T) -> T {value} fn main() -> u8 {let value: u8 = 42; if true {{let local: u16 = 7; identity(local);}; identity(value)} else {0}}",
        "fn identity<T>(value: T) -> T {value} fn forward<T>(value: T) -> T {identity(value)} fn main() -> u8 {let value: u8 = 42; forward(value)}",
        "type Pair<A, B> struct {a: A, b: B} fn main() -> u8 {let a: u8 = 42; let b: bool = true; let pair = Pair {b: b, a: a}; pair.a}",
    ] {
        let program = verify(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
    }
    assert!(verify("fn identity<T>(value: T) -> T {value} fn main() {{let hidden: u8 = 42;}; identity(hidden);}").is_err());
}

#[test]
fn inferred_extents_are_sparse_and_canonical_instances_are_reused() {
    let program = verify("fn inspect<T, const N: usize>(data: &[T; N]) {} fn huge(data: &[u8; 1000000000]) {inspect(data);} fn main() {}").unwrap();
    assert_eq!(program.functions.len(), 3);
    let source = "fn inspect<T, const N: usize>(data: &[T; N]) {} fn first(data: &[u8; 2]) {inspect(data);} fn second(data: &[u8; 1 + 1]) {inspect(data); inspect::<u8, 2>(data);} fn main() {}";
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.functions.len(), 4);
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn inference_preserves_unspecified_machine_arithmetic() {
    let source = "fn identity<T>(value: T) -> T {value} fn main() {let unknown = identity(usize::MAX + 1); proof _: typeof(unknown) == usize; proof _: integer::from(unknown) >= 0;}";
    verify(source).unwrap();
    assert!(verify("fn identity<T>(value: T) -> T ensures result == value {value} fn main() {let unknown = identity(usize::MAX + 1); proof _: unknown == 0;}").is_err());
}
