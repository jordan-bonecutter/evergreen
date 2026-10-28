use super::*;

const EMPTY: &str = "fn clear(data: unique(unique(usize) | shape(unique(usize)), 8))
    where (forall(i: integer) where (0 <= i && i < 8) {typeof((*data)[i]) == shape(unique(usize))})
{
    let empty: unique(shape(unique(usize)), 8) = data;
    drop(empty);
}
fn main() -> usize {42}";

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
fn full_shape_ranges_release_unobserved_buffers_without_enumeration() {
    let (small, small_certificates) = replay(EMPTY);
    let huge = EMPTY
        .replace(", 8)", ", 1000000000)")
        .replace("i < 8", "i < 1000000000");
    let (large, large_certificates) = replay(&huge);
    assert_eq!(small.obligations, large.obligations);
    assert_eq!(small_certificates, large_certificates);
    assert!(crate::compiler::native::emit(&large).unwrap().len() < 16384);
    let source = include_str!("../../../../examples/range_empty.evg");
    let (program, _) = replay(source);
    assert_eq!(program.run().unwrap().to_string(), "42");
    crate::compiler::native::emit(&program).unwrap();
}

#[test]
fn shape_range_release_rechecks_materialized_slots_and_invalidates_borrows() {
    let observed = EMPTY.replace("    let empty:", "    let slot = &(*data)[3]; let empty:");
    let observed = observed.replace(
        "    drop(empty);",
        "    proof _: typeof(*slot) == shape(unique(usize)); drop(empty);",
    );
    replay(&observed);
    let stale = observed
        .replace("    proof _:", "    drop(empty); proof _:")
        .replace("; drop(empty);", ";");
    assert!(verify(&stale).is_err());
    for bad in [
        EMPTY.replace("i < 8", "i < 7"),
        EMPTY.replace("i < 8", "i < 8 && i != 3"),
        EMPTY.replace("    let empty:", "    (*data)[3] = alloc(42); let empty:"),
        EMPTY.replace(
            "{typeof((*data)[i]) == shape(unique(usize))}",
            "{typeof((*data)[i]) == unique(usize)}",
        ),
    ] {
        assert!(verify(&bad).is_err(), "{bad}");
    }
}

#[test]
fn range_release_requires_the_correct_plane_and_admission_free_evidence() {
    let other = EMPTY
        .replace(
            "fn clear(data:",
            "fn clear(other: unique(unique(usize) | shape(unique(usize)), 8), data:",
        )
        .replace("typeof((*data)[i])", "typeof((*other)[i])");
    assert!(verify(&other).is_err());
    let unproved = EMPTY.replace("    where (forall(i: integer) where (0 <= i && i < 8) {typeof((*data)[i]) == shape(unique(usize))})", "");
    assert!(verify(&unproved).is_err());
    let admitted = unproved.replace("    let empty:", "    proof assumed: forall(i: integer) where (0 <= i && i < 8) {typeof((*data)[i]) == shape(unique(usize))} by {trustme}; let empty:");
    assert!(verify(&admitted).is_err());
    let source = include_str!("../../../../examples/range_empty.evg");
    let lost = source.replace(
        "    let value: unique(usize) = move((*buffer)[3]);",
        "    let value: unique(usize) = alloc(7);",
    );
    assert!(verify(&lost).is_err());
    let lie = lost.replace("    arrays::release_empty", "    proof lie: forall(i: integer) where (0 <= i && i < 8) {typeof((*buffer)[i]) == shape(unique(usize))} by {trustme}; arrays::release_empty");
    assert!(verify(&lie).is_err());
}
