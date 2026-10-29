use super::*;
use crate::syntax::format::test_edit::SourceEdit;

const SOURCE: &str = include_str!("../../../../examples/conditional_buffer.evg");
const UPDATES: &str = include_str!("../../../../examples/buffer_updates.evg");

fn replay(source: &str) -> (VerifiedProgram, usize) {
    let (program, bundle) = prove(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    (program, bundle.certificate_count())
}

#[test]
fn buffer_updates_move_payloads_and_keep_range_proofs_sparse() {
    let (program, certificates) = replay(UPDATES);
    assert_eq!(program.run().unwrap().to_string(), "42");
    let huge = UPDATES.replace_evg("::new(8)", "::new(1000000000)");
    let (large, large_certificates) = replay(&huge);
    assert_eq!(program.obligations, large.obligations);
    assert_eq!(certificates, large_certificates);
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 32768);
}

#[test]
fn buffer_updates_require_valid_ranges_and_reject_stale_slot_views() {
    for bad in [
        UPDATES.replace_evg("self.len = self.len + 1;", ""),
        UPDATES.replace_evg("self.len = self.len - 1;", ""),
        UPDATES.replace_evg("(*self.data)[self.len] = item;", "(*self.data)[0] = item;"),
        UPDATES.replace_evg("::new(8)", "::new(1)"),
        UPDATES.replace_evg(
            "let item = values.pop();",
            "let view = values.get(1); let item = values.pop(); let invalid = **view;",
        ),
        UPDATES.replace_evg(
            "let item = values.pop();",
            "let item = values.pop(); let invalid = values.get(1);",
        ),
        UPDATES.replace_evg(
            "let item = values.pop();",
            "let item = values.pop(); let second = values.pop(); let third = values.pop();",
        ),
    ] {
        assert!(verify(&bad).is_err(), "accepted {bad}");
    }
}

#[test]
fn conditional_buffers_keep_empty_and_initialized_ranges_sparse() {
    let (program, certificates) = replay(SOURCE);
    assert_eq!(program.run().unwrap().to_string(), "42");
    let huge = SOURCE.replace_evg('8', "1000000000");
    let (large, large_certificates) = replay(&huge);
    assert_eq!(program.obligations, large.obligations);
    assert_eq!(certificates, large_certificates);
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 32768);
    assert!(large.run().unwrap_err().contains("before allocation"));
}

#[test]
fn conditional_buffers_drop_only_their_live_payloads() {
    let source = format!(
        "type Resource struct {{owner: unique(usize)}}
         impl Drop for Resource {{fn drop(self) {{}}}}
         {}",
        SOURCE
            .replace_evg("unique(usize)", "Resource")
            .replace_evg("alloc(7)", "Resource {owner: alloc(7)}")
            .replace_evg("alloc(42)", "Resource {owner: alloc(42)}")
            .replace_evg("**view", "*view.owner")
    );
    let (program, _) = replay(&source);
    let (result, events) = program.run_with_events().unwrap();
    assert_eq!(result.to_string(), "42");
    assert_eq!(
        events
            .iter()
            .filter(|event| event.as_str() == "drop Resource")
            .count(),
        2
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| event.contains("Buffer"))
            .count(),
        3
    );
}

#[test]
fn conditional_buffers_reject_incorrect_members_stale_views_and_missing_ranges() {
    for bad in [
        SOURCE.replace_evg("(*data)[1] = alloc(42);", ""),
        SOURCE.replace_evg("len: 2", "len: 1"),
        SOURCE.replace_evg("len: 2", "len: 3"),
        SOURCE.replace_evg("values.get(1)", "values.get(2)"),
        SOURCE.replace_evg(
            "let answer = **view;",
            "let answer = **view; drop(values); proof _: **view == answer;",
        ),
        SOURCE.replace_evg(
            "length_fits && storage_matches_capacity && initialized_prefix && vacant_suffix",
            "length_fits && storage_matches_capacity",
        ),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn destructured_cleanup_calls_retain_effect_permissions_and_liveness() {
    let source = "fn clean(data: unique(usize), count: &usize)
        where *count < usize::MAX modifies(count) ensures *count == old(*count) + 1 {
            let temporary: unique(usize) = alloc(7);
            *count = *count + 1;
        }
        type Resource struct {data: unique(usize), count: &usize} where *self.count < usize::MAX;
        impl Drop for Resource {
            fn drop({data, count}) modifies(self.count) {
                clean(data, count);
            }
        }
        fn main() -> usize {
            let count: usize = 41;
            let value = Resource {data: alloc(42), count: &count};
            drop(value); count
        }";
    assert_eq!(replay(source).0.run().unwrap().to_string(), "42");
    assert!(verify(&source.replace("modifies(self.count)", ""))
        .unwrap_err()
        .contains("modifies"));
    assert!(verify(&source.replace(
        "*count = *count + 1;",
        "drop(data); let invalid = *data; *count = *count + 1;"
    ))
    .is_err());
    let intact = "fn allocate_temporary() {let temporary: unique(usize) = alloc(7);}
        type Resource struct {data: unique(usize)}
        impl Drop for Resource {fn drop(self) {allocate_temporary();}}
        fn main() {let value = Resource {data: alloc(42)};}";
    assert!(verify(intact)
        .unwrap_err()
        .contains("destructor calls require"));
}
