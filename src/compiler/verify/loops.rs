//! Finite verification of runtime iteration: initialization, an arbitrary
//! invariant-bearing head, one preservation step, and the false exit guard.
//! The frontend checks the state substitution; contract imports remain part of
//! the documented trusted boundary, as they are for function bodies.

use super::*;

mod head;
use head::Head;

#[cfg(test)]
mod termination_tests;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(super) struct Loop<'a> {
    pub(super) condition: &'a Expr,
    pub(super) invariant: &'a Expr,
    pub(super) modifies: &'a [Expr],
    pub(super) decreases: Option<&'a Expr>,
    pub(super) body: &'a [Statement],
    pub(super) line: usize,
}

pub(super) struct Frame {
    protected: BTreeSet<PlaneId>,
    writes: Vec<(PlaneId, Vec<Projection<Linear>>)>,
    line: usize,
}

fn pure_condition(expression: &Expr) -> bool {
    match &expression.kind {
        Kind::Name(_) | Kind::Number(_) | Kind::Constant(..) | Kind::Bool(_) => true,
        Kind::Unary(op, value) if matches!(op.as_str(), "!" | "-" | "*") => pure_condition(value),
        Kind::Field(base, _) => pure_condition(base),
        Kind::Index(base, index) | Kind::Binary(_, base, index) => {
            pure_condition(base) && pure_condition(index)
        }
        _ => false,
    }
}

impl Context<'_> {
    pub(super) fn check_loop_write(
        &mut self,
        plane: PlaneId,
        path: &[Projection<Linear>],
    ) -> Result<()> {
        // Specification evaluation only materializes observations. In an
        // old(...) store those slot numbers may overlap the live store's slots.
        if self.execution.phase == Phase::Specification {
            return Ok(());
        }
        let cost = self
            .storage
            .loops
            .iter()
            .map(|frame| {
                1usize.saturating_add(
                    frame
                        .writes
                        .iter()
                        .map(|(_, prefix)| prefix.len().min(path.len()) + 1)
                        .sum::<usize>(),
                )
            })
            .sum();
        self.charge_value_work(cost)?;
        for frame in &self.storage.loops {
            if frame.protected.contains(&plane)
                && !frame
                    .writes
                    .iter()
                    .any(|(target, prefix)| *target == plane && path.starts_with(prefix))
            {
                return Err(format!(
                    "line {}: loop write is outside its modifies frame",
                    frame.line
                ));
            }
        }
        Ok(())
    }

    pub(super) fn check_while(&mut self, source: Loop<'_>) -> Result<()> {
        let Loop {
            condition,
            invariant,
            modifies,
            decreases,
            line,
            ..
        } = source;
        if self.execution.phase != Phase::Runtime {
            return Err(format!("line {line}: while currently supports runtime iteration; ideal loops need erased execution support; use a total recursive ideal function"));
        }
        if !self.storage.opened_planes.is_empty() {
            return Err(format!(
                "line {line}: close invariant updates before entering a loop"
            ));
        }
        if !pure_condition(condition) {
            return Err(format!("line {line}: loop conditions currently require scalar expressions without calls or ownership effects"));
        }
        self.execution.partial_execution |= decreases.is_none();

        // Materialize surrounding bindings before protecting their storage.
        // Iteration-local planes may be created and cleaned up independently.
        for (name, value) in self.clone_env()? {
            if !self.locals.places.contains_key(&name) {
                let plane = self.allocate_symbol(value)?;
                self.locals.places.insert(name, plane);
            }
        }
        let targets = self.loop_targets(modifies, line)?;
        let subjects = self.claim_subjects(invariant)?;
        let initial = self.proposition(invariant)?;
        let entry =
            self.prove_subjects(&initial, Some(&subjects), "loop invariant on entry", line)?;

        // Havoc exactly the declared contents, preserving plane identities,
        // live reference provenance, and fixed layouts.
        for target in &targets {
            let plane = self.storage.memory.plane(target.reference)?;
            let old = project(self.storage.memory.read(target.reference)?, &target.path)?.clone();
            let mut new = self.arbitrary(&target.ty)?;
            self.preserve_views(&old, &mut new)?;
            if !self.same_layout(&old, &new)? {
                return Err(format!(
                    "line {line}: loop frames must preserve storage layouts"
                ));
            }
            let mut root = self.storage.memory.read(target.reference)?.clone();
            self.replace_projection(&mut root, &target.path, new)?;
            self.note_state_write(plane, &target.path)?;
            self.storage.memory.write(plane, root, false)?;
        }
        self.refresh_loop_bindings()?;
        let saved = Head::capture(self)?;
        let head_subjects = self.claim_subjects(invariant)?;
        let head = self.proposition(invariant)?;
        self.loop_assumption(&head, head_subjects.clone(), vec![entry])?;
        let mut parents = vec![entry];
        parents.extend(self.loop_step(source, &targets, &saved)?);
        saved.restore(self);
        self.loop_assumption(&head, head_subjects, parents)?;
        // Recheck guard well-formedness in the restored head; the source has
        // no effects, so it denotes the same tested value.
        let exit = self
            .scoped_eval(condition, Some(&Ty::Bool))?
            .proposition()?;
        self.assume_from(&exit.not(), paths::Origin::Unresolved)?;
        self.validate_live(line)
    }

    fn loop_step(
        &mut self,
        source: Loop<'_>,
        targets: &[WritePlace],
        saved: &Head,
    ) -> Result<Vec<evidence::NodeId>> {
        let Loop {
            condition,
            invariant,
            decreases,
            body,
            line,
            ..
        } = source;
        let first_use = self.proof.uses.len();
        let guard = self
            .scoped_eval(condition, Some(&Ty::Bool))?
            .proposition()?;
        self.assume_from(&guard, paths::Origin::Unresolved)?;
        self.proof.control = Some(saved.control.clone().unwrap_or(Formula::True).and(guard));
        // The ranking expression is evaluated in the arbitrary active head,
        // not the concrete entry or one previously executed iteration.
        let before = if let Some(expression) = decreases {
            let value = self.loop_measure(expression)?;
            self.prove(
                &Formula::Ge(value.clone()),
                "nonnegative loop measure",
                expression.line,
            )?;
            Some(value)
        } else {
            None
        };
        let protected = saved
            .memory
            .states()
            .into_iter()
            .filter_map(|(plane, _, value)| value.is_some().then_some(plane))
            .collect();
        let writes = targets
            .iter()
            .map(|target| {
                Ok((
                    self.storage.memory.plane(target.reference)?,
                    target.path.clone(),
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        self.storage.loops.push(Frame {
            protected,
            writes,
            line,
        });
        let checked = (|| {
            for statement in body {
                self.statement(statement)?;
            }
            // Scope cleanup is part of every iteration, before preservation.
            let names = body
                .iter()
                .flat_map(|s| s.bindings())
                .map(str::to_owned)
                .collect::<Vec<_>>();
            self.finish_bindings(names.clone(), false, line)?;
            for name in names {
                self.locals.values.remove(&name);
                self.locals.places.remove(&name);
                self.locals.ideal_bindings.remove(&name);
            }
            // Bindings cannot shadow existing names. Remove only this lexical
            // scope's declarations instead of cloning every surrounding fact.
            for statement in body {
                match statement {
                    Statement::Fact { name, .. } => {
                        self.proof.facts.remove(name);
                    }
                    Statement::Proof { name, .. } if name != "_" => {
                        self.proof.witnesses.remove(name);
                    }
                    _ => {}
                }
            }
            self.charge_value_work(store_weight(&self.storage.memory)?)?;
            saved.check_generations(&self.storage.memory, line)?;
            let subjects = self.claim_subjects(invariant)?;
            let step = self.proposition(invariant)?;
            self.prove_subjects(
                &step,
                Some(&subjects),
                "loop invariant after iteration",
                line,
            )?;
            if let (Some(expression), Some(before)) = (decreases, before) {
                let after = self.loop_measure(expression)?;
                self.prove(
                    &Formula::Ge(before.sub(&after)?.add(&Linear::number(-1))?),
                    "strictly decreasing loop measure",
                    expression.line,
                )?;
            }
            Ok(self.proof.uses[first_use..].to_vec())
        })();
        self.storage.loops.pop();
        checked
    }

    fn loop_measure(&mut self, expression: &Expr) -> Result<Linear> {
        let ty = self.hint(expression).unwrap_or(Ty::Nat);
        if !matches!(ty, Ty::Int | Ty::Nat | Ty::Machine(_)) {
            return Err(format!(
                "line {}: loop measure must be an integer",
                expression.line
            ));
        }
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let value = self
            .scoped_eval(expression, Some(&ty))
            .and_then(|value| value.number());
        self.execution.phase = phase;
        value
    }

    fn loop_assumption(
        &mut self,
        proposition: &Formula,
        subjects: subjects::Snapshot,
        parents: Vec<evidence::NodeId>,
    ) -> Result<()> {
        let node = self.proof.evidence.contract(proposition.clone(), parents)?;
        if self.evidence_dependencies(node)?.admissions.is_empty() {
            self.assume_from(proposition, paths::Origin::Evidence(node))
        } else {
            self.publish_evidence(node, subjects)?;
            self.proof.claims.insert(node);
            Ok(())
        }
    }

    fn refresh_loop_bindings(&mut self) -> Result<()> {
        let weight = self
            .locals
            .places
            .values()
            .try_fold(0usize, |cost, plane| {
                Ok::<_, String>(
                    cost.saturating_add(
                        self.storage
                            .memory
                            .get(*plane)
                            .ok()
                            .map(symbol_weight)
                            .transpose()?
                            .unwrap_or(1),
                    ),
                )
            })?;
        self.charge_value_work(weight)?;
        for (name, plane) in &self.locals.places {
            if let Ok(value) = self.storage.memory.get(*plane) {
                self.locals.values.insert(name.clone(), value.clone());
            }
        }
        Ok(())
    }

    fn loop_targets(&mut self, modifies: &[Expr], line: usize) -> Result<Vec<WritePlace>> {
        let mut targets: Vec<WritePlace> = Vec::new();
        for expression in modifies {
            if !borrow_expression(expression) {
                return Err(format!(
                    "line {line}: loop modifies requires structural references"
                ));
            }
            let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
            let value = self.eval(expression, None);
            self.execution.phase = phase;
            let Symbol::Ref(ty, reference, path) = value? else {
                return Err(format!(
                    "line {line}: loop modifies requires borrowed storage"
                ));
            };
            let allowed = match ty.as_ref() {
                Ty::Array(element, _) => self.history_element(element),
                ty => self.scalar_field_value(ty) && !self.has_runtime_cleanup(ty),
            };
            if !allowed {
                return Err(format!("line {line}: loop frames currently support scalar contents, scalar records, and arrays of scalar records; reference or ownership replacement needs a shape invariant"));
            }
            let plane = self.storage.memory.plane(reference)?;
            for target in &targets {
                if self.storage.memory.plane(target.reference)? == plane
                    && subjects::overlap(&target.path, &path)
                {
                    return Err(format!("line {line}: overlapping loop modifies entries"));
                }
            }
            let owned = self.owns_plane(plane)?;
            if !self.write_permitted(reference, &path, owned)? {
                return Err(format!(
                    "line {line}: loop modifies exceeds the function's write permissions"
                ));
            }
            targets.push(WritePlace {
                origin: "loop frame".into(),
                guard: Formula::True,
                reference,
                path,
                ty,
            });
        }
        Ok(targets)
    }
}
