use super::*;
use crate::syntax::format::test_edit::SourceEdit;

const EXAMPLE: &str = include_str!("../../../../examples/range_reallocate.evg");
const LIBRARY: &str = include_str!("../../../../stdlib/arrays/prefix.evg");
const RELEASE: &str = include_str!("../../../../stdlib/arrays/release.evg");

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
fn source_prefix_relocation_moves_unique_payloads_and_scales_sparsely() {
    let (small, certificates) = replay(EXAMPLE);
    assert_eq!(small.run().unwrap().to_string(), "42");
    let huge = EXAMPLE
        .replace_evg('8', "1000000000")
        .replace_evg("16", "2000000000");
    let (large, large_certificates) = replay(&huge);
    assert_eq!(small.obligations, large.obligations);
    assert_eq!(certificates, large_certificates);
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 32768);
    assert!(large.run().unwrap_err().contains("before allocation"));
}

#[test]
fn source_prefix_relocation_runs_each_payload_destructor_once() {
    let source = format!(
        "type Resource struct {{owner: unique(usize)}}
         impl Drop for Resource {{fn drop(self) {{}}}}
         {}",
        EXAMPLE
            .replace_evg("unique(usize)", "Resource")
            .replace_evg("alloc(7)", "Resource {owner: alloc(7)}")
            .replace_evg("alloc(42)", "Resource {owner: alloc(42)}")
            .replace_evg("*last", "*last.owner")
    );
    let (program, _) = replay(&source);
    let (result, events) = program.run_with_events().unwrap();
    assert_eq!(result.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Resource"]);
}

#[test]
fn source_prefix_relocation_supports_shrinking_and_empty_prefixes() {
    let shrink = EXAMPLE.replace_evg("16", "2");
    assert_eq!(replay(&shrink).0.run().unwrap().to_string(), "42");
    let empty = "fn main() -> usize {
        let data: unique(unique(usize) | shape(unique(usize)), 8) = alloc(8, shape(unique(usize)));
        let grown = arrays::relocate_prefix::<unique(usize)>(8, data, 0, 16);
        arrays::release_empty::<unique(usize)>(16, grown);
        42
    }";
    assert_eq!(replay(empty).0.run().unwrap().to_string(), "42");
}

#[test]
fn source_prefix_relocation_rejects_incorrect_members_bounds_and_stale_views() {
    for bad in [
        EXAMPLE.replace_evg("(*data)[1] = alloc(42);", ""),
        EXAMPLE.replace_evg("8, data, 2, 16", "8, data, 1, 16"),
        EXAMPLE.replace_evg("8, data, 2, 16", "8, data, 3, 16"),
        EXAMPLE.replace_evg("8, data, 2, 16", "8, data, 2, 1"),
        EXAMPLE.replace_evg("8, data, 2, 16", "8, data, 2, 0"),
        EXAMPLE.replace_evg("8, data, 2, 16", "8, data, 2, usize::MAX"),
        EXAMPLE
            .replace_evg("let grown =", "let slot = &(*data)[0]; let grown =")
            .replace_evg(
                "finish(16, grown)",
                "let invalid: &unique(usize) = slot; finish(16, grown)",
            ),
        EXAMPLE
            .replace_evg("let grown =", "let payload = &*(*data)[0]; let grown =")
            .replace_evg(
                "finish(16, grown)",
                "proof _: *payload == 7; finish(16, grown)",
            ),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn source_prefix_relocation_rejects_skips_wrong_slots_and_missing_frames() {
    for bad in [
        LIBRARY.replace_evg("remaining = remaining - 1", "remaining = remaining - 2"),
        LIBRARY.replace_evg("(*data)[start - 1] = value", "(*data)[start] = value"),
        LIBRARY.replace_evg("move((*data)[length - 1])", "move((*data)[length])"),
        LIBRARY.replace_evg(
            "modifies(&*data, &*target, &remaining)",
            "modifies(&*data, &remaining)",
        ),
        LIBRARY.replace_evg(
            "prepend::<T>(new_capacity, &*target, remaining, length, value);",
            "drop(value);",
        ),
        LIBRARY.replace_evg(
            "remaining = remaining - 1;",
            "arrays::release_empty::<T>(data); remaining = remaining - 1;",
        ),
    ] {
        let error = verify(&format!("{RELEASE}\u{1e}{bad}\u{1e}{EXAMPLE}")).unwrap_err();
        assert!(!error.contains("unknown function"), "{error}");
        assert!(!error.contains("work limit"), "{error}");
    }
}
