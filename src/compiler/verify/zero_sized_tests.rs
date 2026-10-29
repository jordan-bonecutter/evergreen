use super::*;
use crate::compiler::TargetKind;

#[test]
fn zero_sized_layouts_preserve_types_and_storage_without_dense_facts() {
    for target in [TargetKind::X86_64, TargetKind::Wasm32] {
        let source = include_str!("../../../examples/zero_sized.evg");
        let (program, bundle) = prove_for_target(source, target).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate_for_target(source, &bundle, target)
                .unwrap()
                .proof_search_count(),
            0
        );
        let large = "fn main() -> usize {let data: unique(unit, usize::MAX) = alloc(usize::MAX, ()); (*data)[usize::MAX - 1] = (); drop(data); 42}";
        let (program, bundle) = prove_for_target(large, target).unwrap();
        assert!(program.obligations < 100);
        assert_eq!(
            verify_with_certificate_for_target(large, &bundle, target)
                .unwrap()
                .proof_search_count(),
            0
        );
    }
}

#[test]
fn empty_address_equality_is_stable_without_assuming_distinct_addresses() {
    let source = "fn same(a: &unit, b: &unit) -> bool ensures result == (a == b) {a == b} fn main() -> usize {let data: [unit; 2] = [(), ()]; let same = &data[0] == &data[1]; proof _: same == (&data[0] == &data[1]); proof _: same == (&data[1] == &data[0]); proof _: &data[0] == &data[0]; proof _: same(&data[0], &data[0]); 42}";
    let (_, bundle) = prove(source).unwrap();
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for source in [
        "fn main() {let data: [unit; 2] = [(), ()]; proof _: &data[0] != &data[1];}",
        "fn main() {let data: [unit; 2] = [(), ()]; proof _: &data[0] == &data[1];}",
        "type Empty struct {} fn main() {let a = Empty {}; let b = Empty {}; proof _: &a != &b;}",
        "fn main() {let data = alloc(()); let stale = &*data; drop(data); proof _: stale == stale;}",
        "fn main() {let data = alloc(()); let stale = &*data; drop(data); let fresh = alloc(()); *stale = ();}",
        "fn change(a: &unit, b: &unit) where a == b modifies(a) {*b = ();} fn main() {}",
        "fn wrong(a: &unit, b: &unit) -> &unit where a == b borrows(a) {b} fn main() {}",
    ] {
        assert!(verify(source).is_err(), "accepted {source}");
    }
}

#[test]
fn zero_sized_resource_cleanup_remains_linear() {
    let source = "type Empty struct {} impl Drop for Empty {fn drop(self) {}} fn main() -> usize {let data = [Empty {}, Empty {}]; drop(data); 42}";
    let (value, events) = verify(source).unwrap().run_with_events().unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Empty", "drop Empty"]);
    assert!(verify(&source.replace("drop(data);", "drop(data); drop(data);")).is_err());
}
