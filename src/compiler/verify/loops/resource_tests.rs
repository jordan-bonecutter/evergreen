use super::*;
use crate::syntax::format::test_edit::SourceEdit;

const SOURCE: &str = include_str!("../../../../examples/range_drain.evg");

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
fn resource_drain_checks_one_iteration_and_remains_sparse() {
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
fn resource_drain_runs_nominal_destructors_exactly_once() {
    let source = format!(
        "type Resource struct {{owner: unique(usize)}}
        impl Drop for Resource {{fn drop(self) {{}}}}
        {}",
        SOURCE
            .replace_evg("unique(usize)", "Resource")
            .replace_evg("alloc(7)", "Resource {owner: alloc(7)}")
            .replace_evg("alloc(42)", "Resource {owner: alloc(42)}")
    );
    let (program, _) = replay(&source);
    let (result, events) = program.run_with_events().unwrap();
    assert_eq!(result.to_string(), "42");
    assert_eq!(events, ["drop Resource", "drop Resource"]);
}

#[test]
fn resource_drain_rejects_stale_payload_views_and_unframed_ownership() {
    let borrowed = SOURCE.replace_evg(
        "drain::<unique(usize), 8>(data, 2);",
        "let payload = &*(*data)[0]; drain::<unique(usize), 8>(data, 2); proof _: *payload == 7;",
    );
    assert!(verify(&borrowed).is_err());
    for bad in [
        SOURCE.replace_evg(
            "drop(value);",
            "drop(value); let again: T = take_last::<T, N>(&*data, remaining);",
        ),
        SOURCE.replace_evg("remaining = remaining - 1;", "remaining = remaining - 2;"),
        SOURCE.replace_evg("drop(value);", "drop(value); drop(data);"),
        SOURCE
            .replace_evg(
                "let remaining = length;",
                "let remaining = length; let outside = alloc(99);",
            )
            .replace_evg("drop(value);", "drop(value); drop(outside);"),
        SOURCE.replace_evg("modifies(&*data, &remaining)", "modifies(&remaining)"),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn resource_frames_preserve_unrelated_payloads_and_require_actual_members() {
    let outside = SOURCE
        .replace_evg(
            "let remaining = length;",
            "let remaining = length; let outside = alloc(99);",
        )
        .replace_evg(
            "arrays::release_empty::<T>(data);",
            "arrays::release_empty::<T>(data); proof _: *outside == 99;",
        );
    replay(&outside);
    let empty = SOURCE
        .replace_evg("(*data)[0] = alloc(7);", "")
        .replace_evg("(*data)[1] = alloc(42);", "")
        .replace_evg(
            "drain::<unique(usize), 8>(data, 2)",
            "drain::<unique(usize), 8>(data, 0)",
        );
    assert_eq!(replay(&empty).0.run().unwrap().to_string(), "42");
    for bad in [
        SOURCE.replace_evg("(*data)[1] = alloc(42);", ""),
        SOURCE.replace_evg(
            "drain::<unique(usize), 8>(data, 2)",
            "drain::<unique(usize), 8>(data, 1)",
        ),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn resource_frames_support_runtime_capacities_and_reject_borrowed_payloads() {
    let source = SOURCE
        .replace_evg(
            "fn take_last<T, const N: usize>(",
            "fn take_last<T>(N: usize,",
        )
        .replace_evg("fn drain<T, const N: usize>(", "fn drain<T>(N: usize,")
        .replace_evg("take_last::<T, N>(", "take_last::<T>(N,")
        .replace_evg("drain::<unique(usize), 8>(", "drain::<unique(usize)>(8,");
    assert_eq!(replay(&source).0.run().unwrap().to_string(), "42");
    let borrowed = format!(
        "type Resource struct {{value: &usize}} {}",
        SOURCE
            .replace_evg("unique(usize)", "Resource")
            .replace_evg("let data:", "let outside: usize = 42; let data:")
            .replace_evg("alloc(7)", "Resource {value: &outside}")
            .replace_evg("alloc(42)", "Resource {value: &outside}")
    );
    assert!(verify(&borrowed).is_err());
}

#[test]
fn deferred_input_payloads_are_not_mistaken_for_iteration_local_allocations() {
    let source = "fn change(data: unique(unique(usize), 1)) {
        let i: usize = 0;
        while i < 1 invariant i <= 1 modifies(&i) {
            *(*data)[0] = 42;
            i = i + 1;
        }
    }";
    let error = verify(source).unwrap_err();
    assert!(error.contains("outside its modifies frame"), "{error}");
    let allowed = source.replace("modifies(&i)", "modifies(&i, &*(*data)[0])");
    replay(&allowed);
    let nested = "fn change(data: unique(unique(usize), 1)) {
        let i: usize = 0;
        while i < 1 invariant i <= 1 modifies(&i) {
            let j: usize = 0;
            while j < 1 invariant j <= 1 modifies(&j, &*(*data)[0]) {
                *(*data)[0] = 42;
                j = j + 1;
            }
            i = i + 1;
        }
    }";
    assert!(verify(nested)
        .unwrap_err()
        .contains("outside its modifies frame"));
}
