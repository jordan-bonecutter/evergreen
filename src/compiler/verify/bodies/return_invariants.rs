//! Export checked nominal result guarantees from an actual body recheck.
//! The callee's other local facts stay local; every exported clause is proved
//! again against the final result and carries its own state dependencies.

use super::*;
use crate::syntax::visit::{self, Visitor};

struct Qualify<'a> {
    receiver: &'a Expr,
    fields: BTreeSet<String>,
    bound: BTreeSet<String>,
    work: &'a mut usize,
}

impl Visitor for Qualify<'_> {
    fn expr(&mut self, expression: &mut Expr) -> Result<()> {
        *self.work = self.work.saturating_add(1);
        if *self.work > MAX_VALUE_WORK {
            return Err("return invariant elaboration work limit reached".into());
        }
        match &mut expression.kind {
            Kind::Name(name) if !self.bound.contains(name) => {
                if name == "self" {
                    *expression = self.receiver.clone();
                    return Ok(());
                }
                if self.fields.contains(name) {
                    expression.kind = Kind::Field(Box::new(self.receiver.clone()), name.clone());
                    return Ok(());
                }
            }
            Kind::Forall {
                variable,
                domain,
                body,
            } => {
                let inserted = self.bound.insert(variable.clone());
                let checked = self.expr(domain).and_then(|()| self.expr(body));
                if inserted {
                    self.bound.remove(variable);
                }
                return checked;
            }
            Kind::Block(statements, tail) => {
                let saved = self.bound.clone();
                let checked = (|| {
                    for statement in statements {
                        self.statement(statement)?;
                        self.bound
                            .extend(statement.bindings().into_iter().map(str::to_owned));
                        if let Statement::Fact { name, .. } | Statement::Proof { name, .. } =
                            statement
                        {
                            self.bound.insert(name.clone());
                        }
                    }
                    self.expr(tail)
                })();
                self.bound = saved;
                return checked;
            }
            _ => {}
        }
        visit::walk_expr(self, expression)
    }
}

impl Context<'_> {
    pub(super) fn publish_checked_result_invariants(
        &mut self,
        value: &Symbol,
        line: usize,
    ) -> Result<Vec<evidence::NodeId>> {
        let Symbol::Record(name, _) = value else {
            return Ok(Vec::new());
        };
        let definition = self
            .declarations
            .structs
            .get(name)
            .ok_or("unknown result type")?
            .clone();
        let Some(mut invariant) = definition.invariant else {
            return Ok(Vec::new());
        };

        // An internal receiver cannot be captured by a source quantifier or
        // local binding. Its plane stores an immutable proof snapshot.
        let receiver_name = self.fresh_name();
        let receiver = Expr {
            kind: Kind::Name(receiver_name.clone()),
            line,
        };
        let env = std::mem::take(&mut self.locals.values);
        let roots = std::mem::take(&mut self.locals.places);
        self.charge_value_work(symbol_weight(value)?)?;
        let plane = self.allocate_symbol(value.clone())?;
        self.locals
            .values
            .insert(receiver_name.clone(), value.clone());
        self.locals.places.insert(receiver_name.clone(), plane);
        let mut facts = definition.facts;
        let mut qualifier = Qualify {
            receiver: &receiver,
            fields: definition
                .fields
                .iter()
                .map(|(name, _)| name.clone())
                .collect(),
            bound: BTreeSet::new(),
            work: &mut self.work.value_work,
        };
        qualifier.expr(&mut invariant)?;
        for (_, expression) in &mut facts {
            qualifier.expr(expression)?;
        }
        let facts = std::mem::replace(&mut self.proof.facts, facts.into_iter().collect());
        let module = std::mem::replace(&mut self.locals.module, definition.module);
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let checked = (|| {
            let mut requirements = Vec::new();
            clauses(&invariant, &mut requirements);
            let mut exported = Vec::new();
            for requirement in requirements {
                let proposition = self.proposition(requirement)?;
                // Arithmetic facts already follow the actual SSA values
                // through a body recheck. Only lexical logical candidates
                // need an explicit export when the callee scope is restored.
                if proposition.is_arithmetic() {
                    continue;
                }
                let subjects = self.claim_subjects(requirement)?;
                let node = self.prove_subjects(
                    &proposition,
                    Some(&subjects),
                    "returned type invariant",
                    line,
                )?;
                // The receiver is an immutable proof snapshot of the returned
                // value. Moving its runtime binding does not change these
                // scalar fields; reads through its pointers still name the
                // actual pointee revisions and must remain current.
                self.publish_evidence(node, subjects)?;
                exported.push(node);
            }
            Ok(exported)
        })();
        self.proof.facts = facts;
        self.locals.module = module;
        self.execution.phase = phase;
        self.locals.values = env;
        self.locals.places = roots;
        checked
    }
}
