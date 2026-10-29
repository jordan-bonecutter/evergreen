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

fn number(n: i128) -> Symbol {
    Symbol::Number(Ty::Int, Linear::number(n))
}

fn contents(identity: &str, fields: &[&str]) -> Contents {
    Contents {
        whole: false,
        identity: identity.into(),
        fields: fields.iter().map(|field| (*field).into()).collect(),
    }
}

#[test]
fn known_stores_need_exact_indices_or_identical_definitions() {
    with_context(|ctx| {
        let at = Linear::variable("at");
        ctx.arrays
            .history
            .insert("fill".into(), ArrayHistory::Fill(number(7)));
        ctx.arrays.history.insert(
            "store".into(),
            ArrayHistory::Store {
                base: "fill".into(),
                index: at.clone(),
                value: number(42),
            },
        );
        assert_eq!(
            ctx.defined_array_read("store", &at).unwrap(),
            Some(number(42))
        );
        assert_eq!(
            ctx.defined_array_read("store", &at.add(&Linear::number(1)).unwrap())
                .unwrap(),
            Some(number(7))
        );
        assert!(ctx
            .defined_array_read("store", &Linear::number(3))
            .unwrap()
            .is_none());
        assert!(ctx
            .defined_array_value(&contents("store", &[]), None, 0)
            .unwrap()
            .is_none());
        // Neither a cached observation nor a current proof path is a definition.
        ctx.arrays
            .reads
            .insert(("store".into(), Linear::number(3)), number(42));
        ctx.assume(&equal(&at, &Linear::number(3)).unwrap())
            .unwrap();
        assert!(ctx
            .defined_array_read("store", &Linear::number(3))
            .unwrap()
            .is_none());
        ctx.arrays.history.insert(
            "same".into(),
            ArrayHistory::Store {
                base: "fill".into(),
                index: at,
                value: number(7),
            },
        );
        assert_eq!(
            ctx.defined_array_value(&contents("same", &[]), None, 0)
                .unwrap(),
            Some(number(7))
        );
    });
}

#[test]
fn branch_reduction_retains_distinct_values_and_projects_unchanged_fields() {
    with_context(|ctx| {
        let record = |n| {
            Symbol::Record(
                "Pair".into(),
                BTreeMap::from([("left".into(), number(n)), ("right".into(), number(9))]),
            )
        };
        ctx.arrays
            .history
            .insert("fill".into(), ArrayHistory::Fill(record(7)));
        ctx.arrays.history.insert(
            "store".into(),
            ArrayHistory::Store {
                base: "fill".into(),
                index: Linear::number(3),
                value: record(42),
            },
        );
        ctx.arrays.history.insert(
            "choice".into(),
            ArrayHistory::Choice {
                condition: Formula::Ge(Linear::variable("guard")),
                left: "fill".into(),
                right: "store".into(),
            },
        );
        assert_eq!(
            ctx.defined_array_value(&contents("choice", &["right"]), None, 0)
                .unwrap(),
            Some(number(9))
        );
        assert!(ctx
            .defined_array_value(&contents("choice", &["left"]), None, 0)
            .unwrap()
            .is_none());
        assert!(ctx
            .defined_array_read("choice", &Linear::number(3))
            .unwrap()
            .is_none());
        assert_eq!(
            ctx.defined_array_read("choice", &Linear::number(4))
                .unwrap(),
            Some(record(7))
        );
    });
}

#[test]
fn literal_reduction_does_not_default_missing_or_uninitialized_storage() {
    with_context(|ctx| {
        ctx.arrays
            .value_literals
            .insert("literal".into(), vec![number(7), number(42)]);
        assert_eq!(
            ctx.defined_array_read("literal", &Linear::number(1))
                .unwrap(),
            Some(number(42))
        );
        assert!(ctx
            .defined_array_read("literal", &Linear::number(2))
            .unwrap()
            .is_none());
        assert!(ctx
            .defined_array_read("literal", &Linear::variable("i"))
            .unwrap()
            .is_none());
        ctx.arrays.value_literals.insert("empty".into(), vec![]);
        ctx.arrays
            .value_literals
            .insert("uniform".into(), vec![number(7), number(7)]);
        assert!(ctx
            .defined_array_read("uniform", &Linear::number(-1))
            .unwrap()
            .is_none());
        ctx.arrays.history.insert(
            "uninitialized".into(),
            ArrayHistory::Uninitialized(Symbol::Shape(Box::new(Ty::Int))),
        );
        for name in ["unknown", "empty", "uninitialized"] {
            ctx.arrays
                .reads
                .insert((name.into(), Linear::number(0)), number(7));
            assert!(ctx
                .defined_array_read(name, &Linear::number(0))
                .unwrap()
                .is_none());
            assert!(ctx
                .defined_array_value(&contents(name, &[]), None, 0)
                .unwrap()
                .is_none());
        }
    });
}
