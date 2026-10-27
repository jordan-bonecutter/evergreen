//! Order ordinary calls and implicit cleanup dependencies together. Traversal
//! uses explicit stacks so a long declaration chain cannot exhaust Rust's stack.

use super::*;

const MAX_DEPENDENCY_WORK: usize = 262_144;

enum Source<'a> {
    Type(&'a Type),
    Record(&'a str),
    Expression(&'a Expr),
    Statement(&'a Statement),
}

struct Dependencies<'a> {
    program: &'a VerifiedProgram,
    functions: BTreeMap<&'a str, &'a Function>,
    methods: BTreeMap<&'a str, &'a Function>,
    work: usize,
}

impl<'a> Dependencies<'a> {
    fn of(&mut self, function: &'a Function) -> Result<BTreeSet<&'a str>> {
        let mut dependencies = BTreeSet::new();
        let mut records = BTreeSet::new();
        let mut pending = vec![
            Source::Type(&function.ret),
            Source::Expression(&function.result),
        ];
        pending.extend(
            function
                .params
                .iter()
                .filter(|(name, _)| !function.ideal_params.contains(name))
                .map(|(_, ty)| Source::Type(ty)),
        );
        pending.extend(function.body.iter().map(Source::Statement));
        while let Some(source) = pending.pop() {
            self.work = self
                .work
                .checked_add(1)
                .ok_or("native dependency work overflow")?;
            if self.work > MAX_DEPENDENCY_WORK {
                return Err("native dependency work limit reached".into());
            }
            match source {
                Source::Type(Type::Named(name)) => pending.push(Source::Record(name)),
                Source::Record(name) => {
                    if !records.insert(name) {
                        continue;
                    }
                    let definition = self
                        .program
                        .structs
                        .get(name)
                        .ok_or("unknown native cleanup dependency")?;
                    if definition.ideal {
                        continue;
                    }
                    pending.extend(definition.runtime_fields().map(|(_, ty)| Source::Type(ty)));
                    if let Some(method) = self.methods.get(name) {
                        dependencies.insert(method.name.as_str());
                    }
                }
                Source::Type(Type::Plane(inner) | Type::Array(inner, _)) => {
                    pending.push(Source::Type(inner));
                }
                Source::Type(Type::Union(members)) => {
                    pending.extend(members.iter().map(Source::Type));
                }
                Source::Type(_) => {} // References and shapes have no child cleanup.
                Source::Expression(expression) => match &expression.kind {
                    Kind::Call(name, args) => {
                        if self.functions.get(name.as_str()).is_some_and(|f| !f.ideal) {
                            dependencies.insert(name.as_str());
                        }
                        // Ideal actuals are erased, including calls inside them.
                        if let Some(callee) = self.functions.get(name.as_str()) {
                            let supplied = callee.supplied_parameters(args.len())?;
                            pending.extend(
                                supplied
                                    .into_iter()
                                    .zip(args)
                                    .filter(|((name, _), _)| !callee.ideal_params.contains(name))
                                    .map(|(_, arg)| Source::Expression(arg)),
                            );
                        } else {
                            pending.extend(args.iter().map(Source::Expression));
                        }
                    }
                    Kind::Record(name, fields) => {
                        pending.push(Source::Record(name));
                        let definition = self
                            .program
                            .structs
                            .get(name)
                            .ok_or("unknown native record dependency")?;
                        pending.extend(
                            fields
                                .iter()
                                .filter(|(name, _)| !definition.ideal_fields.contains(name))
                                .map(|(_, value)| Source::Expression(value)),
                        );
                    }
                    Kind::Unary(_, value) | Kind::Field(value, _) | Kind::FactAt(value, _) => {
                        pending.push(Source::Expression(value));
                    }
                    Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                        pending.extend([Source::Expression(a), Source::Expression(b)]);
                    }
                    Kind::If(c, a, b) => {
                        pending.extend([
                            Source::Expression(c),
                            Source::Expression(a),
                            Source::Expression(b),
                        ]);
                    }
                    Kind::Array(items) => pending.extend(items.iter().map(Source::Expression)),
                    _ => {}
                },
                Source::Statement(statement) => match statement {
                    Statement::Let { ty, value, .. } => {
                        pending.extend(ty.iter().map(Source::Type));
                        pending.push(Source::Expression(value));
                    }
                    Statement::Destructure { record, value, .. } => {
                        pending.extend([Source::Record(record), Source::Expression(value)]);
                    }
                    Statement::Assign { target, value } => {
                        pending.extend([Source::Expression(target), Source::Expression(value)]);
                    }
                    Statement::Effect(value) => pending.push(Source::Expression(value)),
                    Statement::Update { body, .. } => {
                        pending.extend(body.iter().map(Source::Statement))
                    }
                    Statement::While {
                        condition, body, ..
                    } => {
                        pending.push(Source::Expression(condition));
                        pending.extend(body.iter().map(Source::Statement));
                    }
                    Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => {}
                },
            }
        }
        // Direct recursion uses the current function's entry label. Cleanup of
        // a Drop receiver runs its fields, rather than calling its own Drop.
        dependencies.remove(function.name.as_str());
        Ok(dependencies)
    }
}

pub(super) fn compilation_order(program: &VerifiedProgram) -> Result<Vec<&Function>> {
    let mut scanner = Dependencies {
        program,
        functions: program
            .functions
            .iter()
            .map(|f| (f.name.as_str(), f))
            .collect(),
        methods: program
            .functions
            .iter()
            .filter_map(|f| f.drop_target.as_deref().map(|name| (name, f)))
            .collect(),
        work: 0,
    };
    let mut graph = BTreeMap::new();
    for function in program.functions.iter().filter(|f| !f.ideal) {
        graph.insert(function.name.as_str(), scanner.of(function)?);
    }
    let mut started = BTreeSet::new();
    let mut finished = BTreeSet::new();
    let mut ordered = Vec::new();
    for root in program.functions.iter().filter(|f| !f.ideal) {
        let mut pending = vec![(root, false)];
        while let Some((function, exiting)) = pending.pop() {
            let name = function.name.as_str();
            if finished.contains(name) {
                continue;
            }
            if exiting {
                finished.insert(name);
                ordered.push(function);
                continue;
            }
            if !started.insert(name) {
                return Err(format!(
                    "native cleanup/call dependency cycle involving {name}"
                ));
            }
            pending.push((function, true));
            for dependency in graph[name].iter().rev() {
                pending.push((scanner.functions[dependency], false));
            }
        }
    }
    Ok(ordered)
}
