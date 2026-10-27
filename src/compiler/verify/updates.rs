//! Explicit invariant suspension, checked update statements, and restoration.

use super::*;

#[derive(Default)]
struct UpdateScope {
    bindings: Vec<String>,
    facts: Vec<String>,
    proofs: Vec<String>,
}

fn scalar_value(ty: &Ty) -> bool {
    matches!(ty, Ty::Machine(_) | Ty::Int | Ty::Nat | Ty::Bool)
}

fn lifted_requirements(
    definition: &Struct,
    selectors: &[String],
    matched: &mut BTreeSet<String>,
) -> BTreeSet<String> {
    let mut requirements = Vec::new();
    if let Some(invariant) = &definition.invariant {
        clauses(invariant, &mut requirements);
    }
    let names: BTreeSet<_> = requirements
        .iter()
        .filter_map(|requirement| {
            if let Kind::Name(name) = &requirement.kind {
                Some(name.as_str())
            } else {
                None
            }
        })
        .collect();
    let mut selected = BTreeSet::new();
    for selector in selectors {
        let (qualifier, fact) = selector
            .rsplit_once("::")
            .map(|(qualifier, name)| (Some(qualifier), name))
            .unwrap_or((None, selector.as_str()));
        if qualifier.is_some_and(|qualifier| qualifier != definition.name) {
            continue;
        }
        if names.contains(fact) && definition.facts.iter().any(|(name, _)| name == fact) {
            selected.insert(fact.to_owned());
            matched.insert(selector.clone());
        }
    }
    selected
}

impl Context<'_> {
    pub(super) fn update(
        &mut self,
        places: &[Expr],
        lifts: &[String],
        body: &[Statement],
        line: usize,
    ) -> Result<()> {
        let targets = self.open_update(places, lifts, line)?;
        let mut scope = UpdateScope::default();
        for statement in body {
            self.update_statement(statement, &mut scope, line)?;
        }
        self.close_update(targets, scope, line)
    }

    fn open_update(
        &mut self,
        places: &[Expr],
        lifts: &[String],
        line: usize,
    ) -> Result<Vec<Reference>> {
        if !self.opened_planes.is_empty() {
            return Err("nested invariant updates are not supported yet".into());
        }
        if lifts.iter().collect::<BTreeSet<_>>().len() != lifts.len() {
            return Err(format!("line {line}: duplicate lifted requirement"));
        }
        let mut opened = BTreeMap::new();
        let mut matched = BTreeSet::new();
        let mut targets = Vec::new();
        for place in places {
            if !borrow_expression(place) {
                return Err(format!(
                    "line {line}: update places require structural storage observations"
                ));
            }
            let (reference, path) = self.location(place)?;
            if !path.is_empty() {
                return Err(format!("line {line}: updates currently open whole plane roots; nested record projections need subplane invariant tracking"));
            }
            let plane = self.memory.plane(reference)?;
            if opened.contains_key(&plane) {
                return Err(format!(
                    "line {line}: duplicate update place; aliases name the same plane"
                ));
            }
            let value = self.memory.read(reference)?.clone();
            self.record_valid(&value, line)?;
            let Symbol::Record(type_name, _) = value else {
                return Err(format!("line {line}: update requires a live struct plane"));
            };
            let definition = self.structs.get(&type_name).ok_or("unknown update type")?;
            opened.insert(plane, lifted_requirements(definition, lifts, &mut matched));
            targets.push(reference);
        }
        if matched.len() != lifts.len() {
            return Err(format!("line {line}: lifts must name declared facts used as independent where requirements of an opened place"));
        }
        self.opened_planes = opened;
        Ok(targets)
    }

    fn update_statement(
        &mut self,
        statement: &Statement,
        scope: &mut UpdateScope,
        line: usize,
    ) -> Result<()> {
        match statement {
            Statement::Assign {target, value}
                if self.update_expression(target) && self.update_expression(value) => {
                // Inspect the type without evaluating the target twice:
                // computing an address may itself call a checked helper.
                if !self.hint(target).as_ref().is_some_and(scalar_value) {
                    return Err(format!("line {}: updates currently allow only scalar writes; replacing owned fields requires destructor/effect proofs", target.line));
                }
                self.assign(target, value)?;
            }
            Statement::Let {name, value, ..} if self.update_expression(value) => {
                self.statement(statement)?;
                let ty = self.env.get(name).ok_or("unknown update local")?.ty();
                let allowed = scalar_value(&ty) || matches!(ty, Ty::Unit)
                    || matches!(&ty, Ty::Ref(inner) if scalar_value(inner));
                if !allowed {
                    return Err(format!("line {}: update locals require scalar values or scalar borrows, without an open object invariant", value.line));
                }
                scope.bindings.push(name.clone());
            }
            Statement::Fact {name, value} if self.update_expression(value) => {
                self.statement(statement)?;
                scope.facts.push(name.clone());
            }
            Statement::Proof {name, proposition, ..} if self.update_expression(proposition) => {
                self.statement(statement)?;
                scope.proofs.push(name.clone());
            }
            Statement::Effect(value) if self.update_expression(value) => self.statement(statement)?,
            Statement::Ideal(binding) => {
                self.statement(statement)?;
                scope.bindings.extend(binding.bindings().into_iter().map(str::to_owned));
            }
            _ => return Err(format!("line {line}: this operation needs invariant-independent effects; moves, drops, exits, and unknown effects are forbidden while invariants are open")),
        }
        Ok(())
    }

    fn close_update(
        &mut self,
        targets: Vec<Reference>,
        scope: UpdateScope,
        line: usize,
    ) -> Result<()> {
        for reference in targets {
            let value = self.memory.read(reference)?.clone();
            self.record_valid(&value, line)?;
        }
        self.opened_planes.clear();
        for name in scope.bindings.into_iter().rev() {
            let value = if let Some(id) = self.roots.remove(&name) {
                if self.memory.get(id).is_ok() {
                    Some(self.memory.take(id)?)
                } else {
                    None
                }
            } else {
                self.env.remove(&name)
            };
            if let Some(value) = value {
                if self.symbol_is_affine(&value) {
                    self.validate_argument(&value, line)?;
                }
            }
            self.env.remove(&name);
            self.ideal_bindings.remove(&name);
        }
        for name in scope.facts {
            self.facts.remove(&name);
        }
        for name in scope.proofs {
            self.proofs.remove(&name);
        }
        self.validate_live(line)
    }

    fn update_expression(&self, e: &Expr) -> bool {
        match &e.kind {
            Kind::Call(name, args) => {
                if matches!(name.as_str(), "integer" | "nat") {
                    return args.len() == 1 && self.update_expression(&args[0]);
                }
                self.functions.get(name).is_some_and(|f| {
                    (f.ideal || self.cleanup_helpers.contains(name))
                        && f.params.len() == args.len()
                        && f.params.iter().zip(args).all(|((parameter, _), e)| {
                            f.ideal_params.contains(parameter) || self.update_expression(e)
                        })
                })
            }
            Kind::Record(..) | Kind::Array(..) => false,
            Kind::Unary(op, x) if op == "*" => {
                matches!(self.hint(x), Some(Ty::Ref(_) | Ty::Plane(_))) && self.update_expression(x)
            }
            Kind::Unary(_, x) | Kind::Field(x, _) | Kind::FactAt(x, _) => self.update_expression(x),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                self.update_expression(a) && self.update_expression(b)
            }
            Kind::If(c, a, b) => {
                self.update_expression(c) && self.update_expression(a) && self.update_expression(b)
            }
            _ => true,
        }
    }
}
