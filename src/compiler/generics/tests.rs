use crate::compiler::verify::{prove, verify, verify_with_certificate};
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn source_vectors_specialize_vacant_storage_and_move_operations() {
    for (index, source) in [
        include_str!("../../../examples/vec.evg"),
        include_str!("../../../examples/vec_generic.evg"),
        "fn main() -> i16 {let values = vec::Vec::<i16>::new(2); values.push(-7); values.push(42); values = values.reallocate(4); values.pop()}",
        "fn main() -> usize {let values = vec::Vec::<bool>::new(2); values.push(true); values = values.reallocate(4); if values.pop() {42} else {1}}",
        "type Item struct {tag: u8, count: u16} impl Copy for Item {} fn main() -> u16 {let values = vec::Vec::<Item>::new(2); values.push(Item {tag: 7, count: 42}); values.push(Item {tag: 7, count: 42}); let data = values.into_storage(); let item: &Item = &(*data)[1]; let answer = item.count; arrays::drain_prefix::<Item>(2, data, 2); answer}",
        "fn prepare() -> vec::Vec<u8> {vec::Vec::<u8>::new(1000000000)} fn main() -> usize {42}",
    ].into_iter().enumerate() {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        // Replay one representative specialization, not the whole runtime matrix.
        if index == 0 {
            assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
        }
    }
}

#[test]
fn source_vectors_reject_implicit_copies_stale_borrows_and_byte_overflow() {
    for source in [
        "fn main() {let values = vec::Vec::<unique(usize)>::new(2); let item = alloc(7); values.push(item); values.push(item);}",
        "type Item struct {tag: usize} fn main() {let values = vec::Vec::<Item>::new(2); let item = Item {tag: 7}; values.push(item); values.push(item);}",
        "fn main() {let values = vec::Vec::<u8>::new(usize::MAX);}",
        "fn main() {let values = vec::Vec::<u16>::new(9223372036854775807);}",
        "fn main() -> u8 {let values = vec::Vec::<u8>::new(2); values.push(42); let view = values.get(0); values = values.reallocate(4); *view}",
        "fn main() -> u8 {let values = vec::Vec::<u8>::new(2); values.push(42); values.pop(); *values.get(0)}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
    let library = include_str!("../../../stdlib/vec/vec.evg").replace_evg(
        "integer::from(capacity) * integer::from(size_of(T)) <= integer::from(isize::MAX)",
        "true",
    );
    let exercised = format!("{library}\nfn exercise() -> u16 {{let values = Vec::<u16>::new(2); values.push(42); values.pop()}}");
    assert!(verify(&exercised).is_err());
}

#[test]
fn generic_methods_and_drop_are_concrete_checked_source_functions() {
    for (index, source) in [
        "type Buffer<T, const N: usize> struct {data: array(T, N)} impl<U, const M: usize> Buffer<U, M> {method& get(index: usize) -> &U where index < M borrows(&self.data[index]) {&self.data[index]}} fn main() -> usize {let value = Buffer::<usize, 2> {data: [7, 42]}; *value.get(1)}",
        "type Inner<T> struct {value: T} type Outer<T> struct {value: T} impl<T> Outer<T> {method wrap() -> Inner<T> {let Self {value} = self; Inner::<T> {value: value}}} impl<T> Inner<T> {method& read() -> &T borrows(&self.value) {&self.value}} fn main() -> usize {let value = Outer::<usize> {value: 42}; *value.wrap().read()}",
        "type Box<T> struct {value: T} impl<T> Box<T> {fn new(value: T) -> Self {Self {value: value}} method& get() -> &T borrows(&self.value) {&self.value}} fn main() -> usize {let value = Box::<usize>::new(42); *value.get()}",
        "type Box<T> struct {value: T} impl<T> Drop for Box<T> {fn drop(self) {let Self {value} = self; drop(value);}} fn main() -> usize {let value = Box::<usize> {value: 42}; value.value}",
        "type Box<T> struct {value: T} impl<T> Copy for Box<T> {} fn main() -> usize {let first = Box::<usize> {value: 42}; let second = first; first.value + second.value - 42}",
        "type Box<T> struct {value: T} fn unpack<T>(input: Box<T>) -> T {let Box::<T> {value: payload} = input; payload} fn main() -> usize {unpack::<usize>(Box::<usize> {value: 42})}",
    ].into_iter().enumerate() {
        let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        // Replay one representative specialization, not the whole runtime matrix.
        if index == 0 {
            assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
        }
    }
}

#[test]
fn generic_impls_cannot_skip_bodies_ownership_or_module_permissions() {
    for source in [
        "type Box<T> struct {value: T} impl<T> Box<T> {fn new(value: T) -> Self {proof wrong: false; Self {value: value}}} fn main() {let value = Box::<usize>::new(42);}",
        "type Box<T> struct {value: T} impl<T> Box<T> {method& take() -> T {self.value}} fn main() {let value = Box::<unique(usize)> {value: alloc(42)}; let wrong = value.take();}",
        "type Box<T> struct {value: T} impl<T> Drop for Box<T> {fn drop(self) {proof wrong: false;}} fn main() {let value = Box::<usize> {value: 42};}",
        "type Box<T> struct {value: T} impl<T> Copy for Box<T> {} fn main() {let value = Box::<unique(usize)> {value: alloc(42)};}",
        "module data {type Box<T> struct {value: T}} impl<T> data::Box<T> {fn new(value: T) -> Self {Self {value: value}}} fn main() {}",
        "type Box<T> struct {value: T} impl<T> Box<T> {method& read() -> &T borrows(&self.value) {&self.value}} fn main() -> &usize {let value = Box::<usize> {value: 42}; value.read()}",
        "type Pair<T, U> struct {a: T, b: U} impl<T> Pair<T, T> {} fn main() {}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn generic_method_bodies_are_instantiated_only_when_used() {
    let source = "type Box<T> struct {value: T} impl<T> Box<T> {method& get() -> &T borrows(&self.value) {&self.value} fn invalid() -> usize {proof bad: false; 0} fn growing() -> Box<[T; 2]> {proof bad: false; growing()}} fn main() -> usize {let value = Box::<usize> {value: 42}; *value.get()}";
    let program = verify(source).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(program.functions.len(), 2);
    assert_eq!(program.run().unwrap().to_string(), "42");
    let called = source.replace_evg("*value.get()", "Box::<usize>::invalid()");
    assert!(verify(&called).is_err());
}

#[test]
fn consuming_generic_methods_run_normal_receiver_cleanup() {
    let source = "type Resource<T> struct {value: T} impl<T> Drop for Resource<T> {fn drop(self) {}} impl<T> Resource<T> {method inspect() -> usize {42}} fn main() -> usize {let value = Resource::<usize> {value: 7}; value.inspect()}";
    let program = verify(source).unwrap();
    let (value, events) = program.run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events.len(), 1);
}

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

#[test]
fn reference_type_observations_accept_angle_arguments_without_turbofish() {
    let declaration =
        "type Pair<T> struct {value: T} fn read(view: &Pair<usize>) -> usize {view.value}";
    for observation in ["&Pair<usize>", "&Pair::<usize>"] {
        let source = format!("{declaration} fn main() -> usize {{let pair = Pair::<usize> {{value: 42}}; let view = &pair; proof _: typeof(view) == {observation}; read(view)}}");
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        crate::compiler::native::emit(&program).unwrap();
    }
    let source = "module pairs {type Pair<T> struct {value: T}} fn main() {let pair = pairs::Pair::<[usize; 2]> {value: [7, 42]}; let view = &pair; let indirect = &view; proof _: typeof(view) == &pairs::Pair<[usize; 2]>; proof _: typeof(indirect) == &&pairs::Pair<[usize; 2]>;}";
    verify(source).unwrap();
    // Reference comparisons still borrow values, and scalar comparisons retain
    // the ordinary precedence around a borrow argument.
    verify("fn less(view: &usize, limit: usize) -> bool {*view < limit} fn main() {let a: usize = 1; let b: usize = 2; proof _: &a == &a; proof _: &a != &b; less(&a, b);}").unwrap();
}

#[test]
fn reference_type_proofs_do_not_resurrect_planes_or_reinterpret_references() {
    let declarations =
        "type Pair<T> struct {value: T} fn read(view: &Pair<usize>) -> usize {view.value}";
    let dangling = format!("{declarations} fn main() -> usize {{let pair = Pair::<usize> {{value: 42}}; let view = &pair; drop(pair); proof lie: typeof(view) == &Pair<usize> by {{trustme}}; read(view)}}");
    let error = verify(&dangling).unwrap_err();
    assert!(
        error.contains("plane") || error.contains("dangling") || error.contains("live"),
        "{error}"
    );
    let wrong_type = format!("{declarations} fn main() -> usize {{let pair = Pair::<bool> {{value: true}}; let view = &pair; proof lie: typeof(view) == &Pair<usize> by {{trustme}}; read(view)}}");
    assert!(verify(&wrong_type).unwrap_err().contains("type mismatch"));
}

#[test]
fn source_option_moves_owned_payloads_and_requires_presence() {
    let source = include_str!("../../../examples/option.evg");
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    assert!(verify(
        "fn main() -> usize {let empty = option::Option::<usize>::none(); empty.unwrap()}"
    )
    .is_err());
}
