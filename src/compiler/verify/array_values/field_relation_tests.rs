use super::*;

const TYPES: &str = "type Pair struct {left: u8, right: u8} type Sample struct {pair: Pair, flag: bool} impl Copy for Pair {} impl Copy for Sample {}";

fn replay(body: &str) {
    let source = format!("{TYPES} {body}");
    let (program, bundle) = prove(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    assert!(program.trusted_assumptions().is_empty());
    assert_eq!(
        verify_with_certificate(&source, &bundle)
            .unwrap()
            .proof_search_count(),
        0
    );
}

fn reject(body: &str) {
    let source = format!("{TYPES} {body}");
    let error = verify(&source).unwrap_err();
    assert!(error.contains("cannot prove"), "{error}\n{source}");
}

#[test]
fn record_observations_preserve_cross_field_alternatives() {
    let source = "fn read(data: &[Sample; 8], at: usize) -> bool
        where at < 8 && (forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.left == 7 || (*data)[i].pair.right == 9})
        ensures result
    {let left = (*data)[at].pair.left; let right = (*data)[at].pair.right; left == 7 || right == 9}";
    replay(source);
    for bad in [
        source.replace("left == 7 || right == 9}", "left == 7}"),
        source.replace("left == 7 || right == 9}", "right == 9}"),
        source.replace("(*data)[at].pair.right", "(*data)[7 - at].pair.right"),
    ] {
        reject(&bad);
    }
    let mixed = source
        .replace(
            "(*data)[i].pair.left == 7 ||",
            "((*data)[i].pair.left == 7 && (*data)[i].flag == true) ||",
        )
        .replace(
            "left == 7 || right == 9}",
            "(left == 7 && (*data)[at].flag) || right == 9}",
        );
    replay(&mixed);
    reject(&mixed.replace(
        "(left == 7 && (*data)[at].flag) || right == 9}",
        "(*data)[at].flag}",
    ));
}

#[test]
fn record_observations_preserve_implication_and_negation() {
    let source = "fn read(data: &[Sample; 8], at: usize) -> bool
        where at < 8 && (forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.left == 7 => (*data)[i].flag == true})
        ensures result
    {(*data)[at].pair.left != 7 || (*data)[at].flag}";
    replay(source);
    reject(&source.replace("(*data)[at].pair.left != 7 || ", ""));
    let negated = source
        .replace(
            "(*data)[i].pair.left == 7 => (*data)[i].flag == true",
            "!((*data)[i].pair.left == 7 && (*data)[i].flag == true)",
        )
        .replace(
            "{(*data)[at].pair.left != 7 || (*data)[at].flag}",
            "{!((*data)[at].pair.left == 7 && (*data)[at].flag)}",
        );
    replay(&negated);
    reject(&negated.replace(
        "{!((*data)[at].pair.left == 7 && (*data)[at].flag)}",
        "{!(*data)[at].flag}",
    ));
}

#[test]
fn field_relations_require_current_unadmitted_contents() {
    let source = "fn read(data: &[Sample; 8], other: &[Sample; 8]) -> bool
        where forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.left == 7 || (*data)[i].pair.right == 9}
        ensures result
    {(*data)[0].pair.left == 7 || (*data)[0].pair.right == 9}";
    replay(source);
    reject(&source.replace("(*data)[0]", "(*other)[0]"));
    reject(
        &source
            .replace("ensures result", "modifies(data) ensures result")
            .replace(
                "{(*data)[0].pair.left == 7",
                "{(*data)[0].pair.left = 0; (*data)[0].pair.right = 0; (*data)[0].pair.left == 7",
            ),
    );
    reject("fn read(data: &[Sample; 8]) -> bool ensures result {
        proof external: forall(i: integer) where (0 <= i && i < 8) {(*data)[i].pair.left == 7 || (*data)[i].pair.right == 9} by {trustme};
        (*data)[0].pair.left == 7 || (*data)[0].pair.right == 9
    }");
}

#[test]
fn cross_field_contracts_replay_and_remain_sparse() {
    let example = include_str!("../../../../examples/record_field_relations.evg");
    let (program, bundle) = prove(example).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(program.trusted_assumptions().is_empty());
    verify_with_certificate(example, &bundle).unwrap();
    let source = format!("{TYPES} fn read(data: &[Sample; 8], at: usize) -> bool
        where at < 8 && (forall(i: integer) where (0 <= i && i < 8) {{(*data)[i].pair.left == 7 || (*data)[i].pair.right == 9}})
        ensures result
    {{(*data)[at].pair.left == 7 || (*data)[at].pair.right == 9}}");
    let huge = source
        .replace("; 8]", "; 1000000000]")
        .replace("< 8", "< 1000000000");
    let (a, ca) = prove(&source).unwrap();
    let (b, cb) = prove(&huge).unwrap();
    assert_eq!(a.obligations, b.obligations);
    assert_eq!(ca.certificate_count(), cb.certificate_count());
    verify_with_certificate(&huge, &cb).unwrap();
}

#[test]
fn observation_work_depends_on_mentioned_fields_not_record_width() {
    fn work(extra_fields: usize) -> usize {
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
        let mut session = Session::search();
        let mut ctx = Context::new(declarations, &mut session);
        let projection = Contents {
            identity: "input".into(),
            fields: vec!["chosen".into()],
        };
        let body = ctx
            .value_equality(
                &(Some(projection), None),
                &Linear::variable("i"),
                &Linear::number(7),
                0,
            )
            .unwrap();
        let theorem = ctx
            .proof
            .evidence
            .contract(
                Formula::Forall {
                    variable: "i".into(),
                    domain: Box::new(equal(&Linear::variable("i"), &Linear::number(0)).unwrap()),
                    body: Box::new(body),
                },
                Vec::new(),
            )
            .unwrap();
        ctx.proof.claims.insert(theorem);
        let mut fields = (0..extra_fields)
            .map(|i| {
                (
                    format!("unused_{i}"),
                    Symbol::Number(Ty::Int, Linear::variable(format!("unused_{i}"))),
                )
            })
            .collect::<BTreeMap<_, _>>();
        fields.insert(
            "chosen".into(),
            Symbol::Number(Ty::Int, Linear::variable("value")),
        );
        let observed = Symbol::Record("Record".into(), fields);
        let before = ctx.work.value_work;
        ctx.observe_array_values("input", &Linear::number(0), &observed)
            .unwrap();
        let spent = ctx.work.value_work - before;
        assert!(ctx
            .checked_entails(&equal(&Linear::variable("value"), &Linear::number(7)).unwrap())
            .unwrap());
        spent
    }
    assert_eq!(work(1), work(1000));
}
