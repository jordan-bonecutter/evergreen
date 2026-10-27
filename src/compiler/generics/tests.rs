use crate::compiler::verify::{prove, verify, verify_with_certificate};

#[test]
fn concrete_generic_records_functions_and_const_extents_are_verified() {
    for source in [
        include_str!("../../../examples/generics.evg"),
        "fn identity<T>(value: T) -> T {ideal let actual = T; proof same: typeof(value) == actual; value} fn main() -> usize {identity::<usize>(42)}",
        "fn inspect<T>(value: &T) {ideal let actual = T; proof same: typeof(*value) == actual;} fn caller(value: &[u8; 1000000000]) {inspect::<[u8; 1000000000]>(value);} fn main() -> usize {42}",
        "fn identity<T>(value: T) -> T ensures (typeof(result) == T) {value} fn main() -> usize {identity::<usize>(42)}",
        "module values {type Wrapper<T> struct {value: T} where typeof(value) == T; fn wrap<T>(value: T) -> Wrapper<T> {Wrapper::<T> {value: value}}} fn main() -> usize {let value = values::wrap::<usize>(42); value.value}",
        "fn read<T>(value: &T) -> &T borrows(value) {value} fn main() -> usize {let value: usize = 42; *read::<usize>(&value)}",
        "fn identity<T>(value: T) -> T {value} fn main() -> usize {identity::<usize>(42)}",
        "type Pair<T> struct {a: T, b: T} fn main() -> usize {let pair: Pair<usize> = Pair::<usize> {a: 7, b: 42}; pair.b}",
        "type Buffer<T, const N: usize> struct {data: array(T, N)} fn first<T, const N: usize>(data: &Buffer<T, N>) -> T where N > 0 {data.data[0]} fn main() -> usize {let data = Buffer::<usize, 2> {data: [42, 7]}; first::<usize, 2>(&data)}",
        "fn identity<T>(value: T) -> T {value} fn main() -> usize {let value: unique(usize) = alloc(42); let final = identity::<unique(usize)>(value); *final}",
        "type Pair<T = usize> struct {a: T, b: T} fn identity<T = usize>(value: T) -> T {value} fn main() -> usize {let pair: Pair = Pair {a: 7, b: 42}; identity(pair.b)}",
    ] {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn generic_instances_reject_bad_bodies_constants_and_kinds() {
    for source in [
        "fn alloc<T>(value: T) -> T {value} fn main() -> usize {alloc::<usize>(42)}",
        "fn wrong<const N: usize>() -> usize {let N: usize = 7; N} fn main() -> usize {wrong::<42>()}",
        "module values {opaque type Wrapper<T> struct {value: T} fn wrap<T>(value: T) -> Wrapper<T> {Wrapper::<T> {value: value}}} fn main() -> usize {let value = values::wrap::<usize>(42); value.value}",
        "fn duplicate<T>(value: T) -> T {let first = value; value} fn main() {let value: unique(usize) = alloc(42); let bad = duplicate::<unique(usize)>(value);}",
        "fn bad<T>(value: T) -> T {proof false_claim: false; value} fn main() -> usize {bad::<usize>(42)}",
        "fn length<const N: u8>() -> usize {42} fn main() -> usize {length::<256>()}",
        "fn length<const N: u8>() -> usize {42} fn main() -> usize {length::<{255 + 1 - 1}>()}",
        "fn answer<T>() -> usize {42} fn main() -> usize {answer::<Unknown>()}",
        "fn answer<T>() -> usize {42} fn main() -> usize {answer::<7>()}",
        "fn length<const N: usize>() -> usize {42} fn main() -> usize {length::<usize>()}",
        "fn identity<T>(value: T) -> T {value} fn main() -> usize {identity(42)}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn specialization_reuses_closed_type_and_const_argument_identities() {
    let alias = "type Octet = make_type(size: 1, align: 1, represents: repr::Integral {signed: false, bits: 8, encoding: repr::Binary, endian: repr::Little});";
    let source = format!("{alias} type Box<T> struct {{value: T}} fn take(value: Box<u8>) -> u8 {{value.value}} fn main() -> u8 {{let value: Box<Octet> = Box::<u8> {{value: 42}}; take(value)}}");
    let program = verify(&source).unwrap();
    assert_eq!(program.structs.len(), 1);
    assert_eq!(program.run().unwrap().to_string(), "42");
    let source = "type Box<T> struct {value: T} fn take(value: Box<[usize; 2]>) -> usize {value.value[0]} fn main() -> usize {let value: Box<[usize; 1 + 1]> = Box::<[usize; 2]> {value: [42, 7]}; take(value)}";
    let program = verify(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(program.structs.len(), 1);
    let source = "fn answer<const N: usize>() -> usize {42} fn main() -> usize {answer::<2>(); answer::<{1 + 1}>()}";
    let program = verify(source).unwrap();
    assert_eq!(program.functions.len(), 2);
    assert_eq!(program.run().unwrap().to_string(), "42");
}

#[test]
fn unused_templates_are_not_certified_and_expanding_instantiations_are_bounded() {
    let source =
        "fn bad<T>(value: T) -> T {proof impossible: false; value} fn main() -> usize {42}";
    let program = verify(source).unwrap();
    assert_eq!(program.functions.len(), 1);
    assert_eq!(program.run().unwrap().to_string(), "42");
    let source = "type Expanding<T> struct {next: unique(Expanding<[T; 2]>)} fn use(value: &Expanding<usize>) {} fn main() -> usize {42}";
    let error = verify(source).unwrap_err();
    assert!(error.contains("limit"), "{error}");
}
