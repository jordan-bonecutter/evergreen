use super::*;

fn with_context(check: impl FnOnce(&mut Context<'_>)) {
    let functions = BTreeMap::new();
    let structs = BTreeMap::new();
    let names = BTreeSet::new();
    let summaries = BTreeMap::new();
    let declarations = Declarations {
        target: crate::compiler::TargetKind::X86_64,
        functions: &functions,
        summaries: &summaries,
        structs: &structs,
        drops: &names,
        destructors: &functions,
        helpers: &names,
        cleanup_helpers: &names,
    };
    check(&mut Context::new(declarations, &mut Session::search()));
}

fn array(identity: &str, length: i128) -> Symbol {
    Symbol::Array {
        element: Box::new(byte_type()),
        len: Linear::number(length),
        items: None,
        cells: BTreeMap::new(),
        identity: identity.into(),
    }
}

fn byte(value: i128) -> Symbol {
    Symbol::Number(byte_type(), Linear::number(value))
}

#[test]
fn importing_and_reading_a_fill_has_constant_cost_at_any_capacity() {
    with_context(|context| {
        context
            .arrays
            .history
            .insert("filled".into(), ArrayHistory::Fill(byte(42)));
        let mut costs = Vec::new();
        for length in [8, 1_000_000_000] {
            let source = array("filled", length);
            let mut budget = Budget::new(32);
            let imported = Importer::new(context, &mut budget)
                .value(&source, 0)
                .unwrap()
                .unwrap();
            assert_eq!(budget.spent, 1);
            let Value::Array(view) = imported else {
                panic!("expected an array view")
            };
            let selected = select(context, &mut budget, view, length as usize - 1)
                .unwrap()
                .unwrap();
            assert_eq!(selected.number().unwrap(), 42);
            costs.push(budget.spent);
        }
        assert_eq!(costs[0], costs[1]);
        assert!(context.arrays.reads.is_empty());
    });
}

#[test]
fn selection_follows_only_exact_stores_and_closed_choices() {
    with_context(|context| {
        context
            .arrays
            .history
            .insert("base".into(), ArrayHistory::Fill(byte(7)));
        context.arrays.history.insert(
            "stored".into(),
            ArrayHistory::Store {
                base: "base".into(),
                index: Linear::number(3),
                value: byte(42),
            },
        );
        let stored = array("stored", 1_000_000_000);
        let mut budget = Budget::new(128);
        assert_eq!(
            select(context, &mut budget, Array::Stored(&stored), 3)
                .unwrap()
                .unwrap()
                .number()
                .unwrap(),
            42
        );
        assert_eq!(
            select(context, &mut budget, Array::Stored(&stored), 999_999_999)
                .unwrap()
                .unwrap()
                .number()
                .unwrap(),
            7
        );
        context.arrays.history.insert(
            "alias".into(),
            ArrayHistory::Store {
                base: "base".into(),
                index: Linear::variable("i"),
                value: byte(42),
            },
        );
        // A branch-local read cache is not a timeless explanation of a store.
        context
            .arrays
            .reads
            .insert(("alias".into(), Linear::number(0)), byte(42));
        let aliased = array("alias", 8);
        assert!(select(context, &mut budget, Array::Stored(&aliased), 0)
            .unwrap()
            .is_none());
        context.arrays.history.insert(
            "choice".into(),
            ArrayHistory::Choice {
                condition: Formula::Ge(Linear::variable("guard")),
                left: "stored".into(),
                right: "base".into(),
            },
        );
        let choice = array("choice", 8);
        assert!(select(context, &mut budget, Array::Stored(&choice), 3)
            .unwrap()
            .is_none());
        context.arrays.history.insert(
            "choice".into(),
            ArrayHistory::Choice {
                condition: Formula::True,
                left: "stored".into(),
                right: "base".into(),
            },
        );
        assert_eq!(
            select(context, &mut budget, Array::Stored(&choice), 3)
                .unwrap()
                .unwrap()
                .number()
                .unwrap(),
            42
        );
    });
}

#[test]
fn missing_empty_and_out_of_bounds_slots_do_not_acquire_data() {
    with_context(|context| {
        context.arrays.history.insert(
            "empty".into(),
            ArrayHistory::Uninitialized(Symbol::Shape(Box::new(byte_type()))),
        );
        for identity in ["unknown", "empty"] {
            let source = array(identity, 8);
            assert!(
                select(context, &mut Budget::new(32), Array::Stored(&source), 0)
                    .unwrap()
                    .is_none()
            );
            assert!(select(context, &mut Budget::new(32), Array::Stored(&source), 8).is_err());
        }
        let mut symbolic = array("unknown", 8);
        let Symbol::Array { len, .. } = &mut symbolic else {
            unreachable!()
        };
        *len = Linear::variable("length");
        assert!(
            select(context, &mut Budget::new(32), Array::Stored(&symbolic), 0)
                .unwrap()
                .is_none()
        );
        assert!(select(context, &mut Budget::new(32), Array::Bytes(b""), 0).is_err());
    });
}

#[test]
fn source_ideal_reads_are_sparse_across_large_capacity_and_store_history() {
    let source = "ideal fn last(ideal n: nat, data: &[u8; n]) -> u8 where n > 0 {(*data)[n - 1]} fn main() -> usize {let data: unique(u8, 8) = alloc(8, 42); proof first: last(&*data) == 42; (*data)[0] = 7; proof untouched: last(&*data) == 42; (*data)[7] = 9; proof changed: last(&*data) == 9; 42}";
    let (small, small_certificate) = prove(source).unwrap();
    assert_eq!(small.run().unwrap().to_string(), "42");
    let large = source
        .replace("unique(u8, 8)", "unique(u8, 1000000000)")
        .replace("alloc(8, 42)", "alloc(1000000000, 42)")
        .replace("[7] = 9", "[999999999] = 9");
    let (large_program, large_certificate) = prove(&large).unwrap();
    // Only verify/build the large allocation: do not allocate it on the host.
    assert_eq!(small.obligations, large_program.obligations);
    assert_eq!(
        small_certificate.certificate_count(),
        large_certificate.certificate_count()
    );
    assert_eq!(
        verify_with_certificate(&large, &large_certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(crate::compiler::native::emit(&large_program).unwrap().len() < 16384);
    assert!(verify(&source.replace(
        "proof changed: last(&*data) == 9",
        "proof changed: last(&*data) == 42"
    ))
    .is_err());
}

#[test]
fn an_observed_field_does_not_require_importing_unrelated_payloads() {
    let source = "type Packet struct {tag: usize, payload: usize | shape(usize)} ideal fn tag(packet: &Packet) -> usize {packet.tag} fn main() -> usize {let packet = Packet {tag: 42, payload: shape(usize)}; proof _: tag(&packet) == 42; let Packet {tag, payload} = packet; let empty: shape(usize) = move(payload); 42}";
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    assert!(verify(&source.replace("tag(&packet) == 42", "tag(&packet) == 7")).is_err());
}

#[test]
fn symbolic_extents_can_pass_through_ideal_helpers_without_reading_slots() {
    let source = "ideal fn length(ideal n: nat, data: &[u8; n]) -> nat {n} ideal fn relay(ideal n: nat, data: &[u8; n]) -> nat {length(data)} fn check(n: usize, data: linear_plane(u8, n)) {proof _: relay(data) == nat(n);} fn main() -> usize {let data: [u8; 2] = [7, 42]; check(&data); 42}";
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn lazy_observation_example_keeps_the_large_allocation_out_of_execution() {
    let source = include_str!("../../../../../examples/lazy_ideal_reads.evg");
    let (program, certificate) = prove(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(source, &certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
}

#[test]
fn utf8_rejection_can_stop_before_importing_an_unknown_tail() {
    let source = "fn reject(data: &[u8; 8]) modifies(&(*data)[0]) {(*data)[0] = 255; proof _: !utf8::valid(data);} fn main() -> usize {42}";
    let (small, small_certificate) = prove(source).unwrap();
    let large = source.replace("[u8; 8]", "[u8; 1000000000]");
    let (large_program, large_certificate) = prove(&large).unwrap();
    assert_eq!(small.obligations, large_program.obligations);
    assert_eq!(
        small_certificate.certificate_count(),
        large_certificate.certificate_count()
    );
    assert_eq!(
        verify_with_certificate(&large, &large_certificate)
            .unwrap()
            .proof_search_count(),
        0
    );
    // One ASCII byte says nothing about the remaining bytes' encoding.
    assert!(verify(
        &source
            .replace("= 255;", "= 65;")
            .replace("!utf8::valid(data)", "utf8::valid(data)")
    )
    .is_err());
    assert!(verify(&source.replace("= 255;", "= 65;")).is_err());
}
