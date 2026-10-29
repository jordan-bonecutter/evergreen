//! Transport an advertised call result into its binding. The mathematical value
//! is identical; its state dependency becomes the receiver's initial revision.
//! Ordinary assignments do not inherit this transport automatically.

use super::*;

pub(super) struct CallResult {
    pub(super) value: Symbol,
    pub(super) proof: evidence::NodeId,
    pub(super) origin: subjects::Snapshot,
    pub(super) control: Formula,
}

impl Context<'_> {
    // Collect each source conjunct independently. An unsupported observation in
    // one clause must not erase the footprints of its proven sibling clauses.
    pub(super) fn publish_body_postcondition(
        &mut self,
        root: evidence::NodeId,
        expression: &Expr,
        value: &Symbol,
    ) -> Result<Vec<evidence::NodeId>> {
        let mut pending = vec![(root, expression)];
        let mut published = Vec::new();
        while let Some((node, expression)) = pending.pop() {
            self.charge_value_work(1)?;
            if let Kind::Binary(op, left, right) = &expression.kind {
                if op == "&&" {
                    let Formula::And(a, b) = self.proof.evidence.claim(node)?.clone() else {
                        return Err("source contract conjunction lost its proof structure".into());
                    };
                    let a = self
                        .proof
                        .evidence
                        .derive(*a, evidence::Rule::AndLeft(node))?;
                    let b = self
                        .proof
                        .evidence
                        .derive(*b, evidence::Rule::AndRight(node))?;
                    pending.push((b, right));
                    pending.push((a, left));
                    continue;
                }
            }
            let snapshot = self.claim_subjects(expression)?;
            published.extend(self.publish_call_contract(node, snapshot, value, expression.line)?);
        }
        Ok(published)
    }

    pub(super) fn publish_call_contract(
        &mut self,
        node: evidence::NodeId,
        subjects: subjects::Snapshot,
        value: &Symbol,
        line: usize,
    ) -> Result<Vec<evidence::NodeId>> {
        let clauses = self.contract_clauses(node, subjects)?;
        let origin = self.claim_subjects(&Expr {
            kind: Kind::Name("result".into()),
            line,
        })?;
        let control = self.proof.control.clone().unwrap_or(Formula::True);
        let cost = symbol_weight(value)?
            .saturating_add(origin.storage_weight()?)
            .saturating_add(control.storage_weight()?);
        for &proof in &clauses {
            self.proof.claims.insert(proof);
            self.charge_value_work(cost)?;
            self.proof.results.push(CallResult {
                value: value.clone(),
                proof,
                origin: origin.clone(),
                control: control.clone(),
            });
        }
        Ok(clauses)
    }

    pub(super) fn bind_call_evidence(
        &mut self,
        name: &str,
        value: &Symbol,
        start: usize,
        line: usize,
    ) -> Result<()> {
        let pending = self.proof.results.split_off(start);
        for result in pending.into_iter().filter(|result| result.value == *value) {
            // A branch's returned guarantee cannot become unconditional just
            // because both branches happened to produce equal scalar values.
            if !self.checked_entails(&result.control)? {
                continue;
            }
            let Some(mut snapshot) = self.proof.evidence.subjects(result.proof).cloned() else {
                continue;
            };
            let target = self.claim_subjects(&Expr {
                kind: Kind::Name(name.into()),
                line,
            })?;
            let key = snapshot.key.clone();
            snapshot.replace_read(&result.origin, &target);
            if snapshot.key == key {
                continue;
            }
            let claim = self.proof.evidence.claim(result.proof)?.clone();
            let node = self
                .proof
                .evidence
                .derive(claim, evidence::Rule::Reuse(result.proof))?;
            self.publish_evidence(node, snapshot)?;
            self.proof.claims.remove(&result.proof);
            self.proof.claims.insert(node);
        }
        Ok(())
    }
}
