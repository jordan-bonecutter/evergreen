use super::*;
use crate::syntax::format::test_edit::SourceEdit;

const SOURCE: &str = include_str!("../../../../examples/update_owner_slots.evg");

#[test]
fn update_owner_slots_transfer_once_and_replay() {
    let (program, bundle) = prove(SOURCE).unwrap();
    let (answer, events) = program.run_with_events().unwrap();
    assert_eq!(answer.to_string(), "42");
    assert_eq!(events, ["drop Slot"]);
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(SOURCE, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
    // The allocation remains live when its owner moves through the two slots.
    let borrowed = SOURCE.replace_evg(
        "let item = slot.pop(); let answer = *item;",
        "let view = &*slot.data; let item = slot.pop(); let answer = *view;",
    );
    assert_eq!(verify(&borrowed).unwrap().run().unwrap().to_string(), "42");
}

#[test]
fn update_owner_slots_require_vacancy_restoration_and_complete_transfers() {
    for source in [
        SOURCE.replace_evg("self.full = true;", ""),
        SOURCE.replace_evg("self.full = false;", ""),
        SOURCE.replace_evg("output = value;", ""),
        SOURCE.replace_evg("where !self.full", "where true"),
        SOURCE.replace_evg(
            "let item = slot.pop();",
            "slot.push(alloc(7)); let item = slot.pop();",
        ),
        SOURCE.replace_evg(
            "self.data = item;",
            "self.data = item; let duplicate = item;",
        ),
        SOURCE.replace_evg("output = value;", "output = value; let duplicate = value;"),
        SOURCE.replace_evg("self.data = item;", "item;"),
        SOURCE.replace_evg("self.data = item;", "drop(item);"),
        SOURCE.replace_evg("self.data = item;", "leak(item);"),
        SOURCE.replace_evg(
            "let item = slot.pop();",
            "let view: &unique(usize) = &slot.data; let item = slot.pop(); let bad = **view;",
        ),
    ] {
        assert!(verify(&source).is_err(), "accepted {source}");
    }
    let escaped = "type Pair struct {a: usize, b: usize} where (fact same = self.a == self.b; same); fn main() {let pair = Pair {a: 1, b: 1}; update(pair) lifts same {let moved = move(pair);}}";
    assert!(verify(escaped)
        .unwrap_err()
        .contains("cannot consume an opened update plane"));
}

#[test]
fn ideal_update_locals_keep_their_erased_scope() {
    let source = "ideal type Witness struct {value: nat} type Pair struct {a: usize, b: usize} where (fact same = self.a == self.b; same); fn main() -> usize {let pair = Pair {a: 1, b: 1}; update(pair) lifts same {ideal let witness = Witness {value: 42}; pair.a = 42; pair.b = 42;} pair.a}";
    let program = verify(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
}
