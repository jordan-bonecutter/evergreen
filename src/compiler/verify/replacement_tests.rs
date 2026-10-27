use super::*;

pub(crate) const OLD_SLOT_DURING_DROP: &str = "type Resource struct {data: plane(usize), slot: &plane(usize), seen: &usize} impl Drop for Resource {fn drop(self) modifies(self.seen) ensures *self.seen == old(**self.slot) {*self.seen = **self.slot;}} fn main() -> usize {let seen: usize = 0; let original: plane(usize) = alloc(7); let replacement: plane(usize) = alloc(42); let resource = Resource {data: alloc(7), slot: &original, seen: &seen}; resource.slot = &resource.data; let header = &resource.data; resource = Resource {data: alloc(42), slot: &replacement, seen: &seen}; if seen == 7 && **header == 42 {42} else {1}}";

#[test]
fn replacing_an_owned_record_destroys_its_old_payload_before_installing_the_new_one() {
    for source in [
        "type Resource struct {data: plane(usize)} impl Drop for Resource {fn drop(self) {}} fn main() -> usize {let value = Resource {data: alloc(7)}; value = Resource {data: alloc(42)}; *value.data}",
        OLD_SLOT_DURING_DROP,
    ] {
        let (program, bundle) = prove(source).unwrap();
        let (value, events) = program.run_with_events().unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events, ["drop Resource", "drop Resource"]);
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
}

#[test]
fn replacement_still_rejects_dangling_new_fields_and_broken_external_invariants() {
    for source in [
        "type Resource struct {data: plane(usize), view: &usize} impl Drop for Resource {fn drop(self) {}} fn main() {let external: usize = 7; let value = Resource {data: alloc(7), view: &external}; let old = &*value.data; value = Resource {data: alloc(42), view: old};}",
        "type Positive struct {value: &usize} where *value > 0; type Guard struct {value: &usize, data: plane(usize)} impl Drop for Guard {fn drop(self) modifies(self.value) {*self.value = 0;}} fn main() {let count: usize = 1; let retained = Positive {value: &count}; let guard = Guard {value: &count, data: alloc(42)}; guard = Guard {value: &count, data: alloc(7)};}",
    ] {assert!(verify(source).is_err(), "accepted {source}");}
}

#[test]
fn zero_capacity_vectors_use_one_zero_word_and_preserve_header_borrows_on_growth() {
    for source in [
        "fn main() -> usize {let values = vec::Vec::new(0); proof empty: values.length() == 0 && values.capacity() == 0; 42}",
        "fn main() -> usize {let values = vec::Vec::new(0); let header = &values; values = values.reallocate(4); proof grown: header.capacity() == 4; values.push(42); values = values.reallocate(8); proof grown_again: header.capacity() == 8; values.pop()}",
        "fn main() -> usize {let values = vec::Vec::new(1); values.push(42); let removed = values.pop(); values = values.reallocate(0); values = values.reallocate(0); proof empty: values.capacity() == 0; removed}",
    ] {
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(crate::compiler::layout::of(&Type::Named("vec::Zero".into()), &program.structs).unwrap().size, 8);
        assert_eq!(crate::compiler::layout::of(&Type::Named("vec::Vec".into()), &program.structs).unwrap().size, 24);
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
    }
    assert!(
        verify("fn main() {let values = vec::Vec::new(0); let data = values.into_data();}")
            .is_err()
    );
}
