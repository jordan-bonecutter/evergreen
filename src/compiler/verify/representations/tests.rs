use super::*;
use crate::syntax::format::test_edit::SourceEdit;

#[test]
fn representation_transfer_moves_array_ownership_and_replays() {
    let source = include_str!("../../../../examples/representation_transfer.evg");
    let (program, bundle) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    for bad in [
        source.replace_evg("transfer_type(&source, &target);", ""),
        source.replace_evg(
            "transfer_type(&source, &target);",
            "transfer_type(&source, &target); transfer_type(&source, &target);",
        ),
        source.replace_evg(
            "transfer_type(&source, &target);",
            "transfer_type(&source, &source);",
        ),
    ] {
        assert!(verify(&bad).is_err());
    }
}

#[test]
fn copied_representation_does_not_own_or_survive_source_writes_as_equal() {
    let source = "fn main() -> usize {let value: usize = 42; let bytes = copy_representation(&value); proof copied: same_representation(&value, &bytes) by {omega}; value}";
    assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    let stale = source.replace_evg("proof copied:", "value = 7; proof copied:");
    assert!(verify(&stale).unwrap_err().contains("cannot prove"));
    let stale_proof = source.replace_evg(
        "value}",
        "value = 7; proof stale: same_representation(&value, &bytes) by {exact copied}; value}",
    );
    assert!(verify(&stale_proof).is_err());
    let unreadable = source.replace_evg("value}", "let forged: usize = bytes; forged}");
    assert!(verify(&unreadable).is_err());
    let drop = "type Item struct {value: usize} impl Drop for Item {fn drop(self) {}} fn main() -> usize {let source: Item | shape(Item) = Item {value: 42}; let target: Item | shape(Item) = copy_representation(&source); transfer_type(&source, &target); let retired: shape(Item) = source; let live: Item = target; live.value}";
    let (value, events) = crate::interpreter::run_with_events(&verify(drop).unwrap()).unwrap();
    assert_eq!(value.to_string(), "42");
    assert_eq!(events, ["drop Item"]);
    let shared = "fn main() -> usize {let allocation: unique(usize) = alloc(42); let owner: shared(usize) = move(allocation); let source: shared(usize) | shape(shared(usize)) = move(owner); let target: shared(usize) | shape(shared(usize)) = copy_representation(&source); transfer_type(&source, &target); let retired: shape(shared(usize)) = source; let live: shared(usize) = move(target); proof one: owner_count(live) == 1; let final: unique(usize) = move(live); *final}";
    assert_eq!(verify(shared).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn source_relocation_transfers_sparse_slots_without_capacity_expansion() {
    let source = include_str!("../../../../examples/representation_array_slot.evg");
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    let huge = source.replace_evg('3', "1000000000");
    assert_eq!(verify(&huge).unwrap().obligations, program.obligations);
    let repeated = source.replace_evg(
        "let value:",
        "arrays::relocate::<unique(usize)>(&(*source)[1], &(*target)[2]); let value:",
    );
    assert!(verify(&repeated).is_err());
}
