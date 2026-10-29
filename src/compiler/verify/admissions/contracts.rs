//! Publish independent conjuncts of a contract as separate proof candidates.
//! For example, an exchange's new contents do not depend on its old-result fact.

use super::*;

impl Context<'_> {
    pub(in crate::compiler::verify) fn contract_clauses(
        &mut self,
        root: evidence::NodeId,
        snapshot: subjects::Snapshot,
    ) -> Result<Vec<evidence::NodeId>> {
        let mut pending = vec![(root, snapshot)];
        let mut clauses = Vec::new();
        while let Some((proof, snapshot)) = pending.pop() {
            self.charge_value_work(1)?;
            match self.proof.evidence.claim(proof)?.clone() {
                Formula::And(a, b) => {
                    // Equality also elaborates into two inequalities. Both
                    // keep the equality's footprint; source && splits it.
                    let left_snapshot = snapshot
                        .branch("&&", false)
                        .unwrap_or_else(|| snapshot.clone());
                    let right_snapshot = snapshot.branch("&&", true).unwrap_or(snapshot);
                    let left = self
                        .proof
                        .evidence
                        .derive(*a, evidence::Rule::AndLeft(proof))?;
                    let right = self
                        .proof
                        .evidence
                        .derive(*b, evidence::Rule::AndRight(proof))?;
                    pending.push((right, right_snapshot));
                    pending.push((left, left_snapshot));
                }
                Formula::True => {}
                Formula::Or(a, b) => {
                    if let Some(selected) = self.select_contract_alternative(proof, &a, &b)? {
                        pending.push((selected, snapshot));
                    } else {
                        if self.proof.evidence.subjects(proof).is_none() {
                            self.publish_evidence(proof, snapshot)?;
                        }
                        clauses.push(proof);
                    }
                }
                _ => {
                    if self.proof.evidence.subjects(proof).is_none() {
                        self.publish_evidence(proof, snapshot)?;
                    }
                    clauses.push(proof);
                }
            }
        }
        Ok(clauses)
    }

    // A conditional guarantee may expose its live arm only after the other
    // arm has been ruled out. Keep that checked condition in the proof DAG.
    pub(in crate::compiler::verify) fn select_contract_alternative(
        &mut self,
        source: evidence::NodeId,
        left: &Formula,
        right: &Formula,
    ) -> Result<Option<evidence::NodeId>> {
        for (rejected, selected, reject_left) in [(left, right, true), (right, left, false)] {
            let Some((path, negative)) = self.refuted_contract_conjunct(rejected)? else {
                continue;
            };
            let (left_hypothesis, left_case) = self.proof.evidence.hypothesis(left.clone())?;
            let (right_hypothesis, right_case) = self.proof.evidence.hypothesis(right.clone())?;
            let mut contradicted = if reject_left { left_case } else { right_case };
            for right in path {
                let Formula::And(a, b) = self.proof.evidence.claim(contradicted)?.clone() else {
                    return Err("conditional contract lost its conjunct".into());
                };
                contradicted = self.proof.evidence.derive(
                    if right { *b } else { *a },
                    if right {
                        evidence::Rule::AndRight(contradicted)
                    } else {
                        evidence::Rule::AndLeft(contradicted)
                    },
                )?;
            }
            let impossible = self.selector_contradiction(negative, contradicted)?;
            let impossible = self
                .proof
                .evidence
                .derive(selected.clone(), evidence::Rule::FalseElim(impossible))?;
            return self
                .proof
                .evidence
                .derive(
                    selected.clone(),
                    evidence::Rule::OrElim {
                        source,
                        left_hypothesis,
                        right_hypothesis,
                        left: if reject_left { impossible } else { left_case },
                        right: if reject_left { right_case } else { impossible },
                    },
                )
                .map(Some);
        }
        Ok(None)
    }

    // Refuting any conjunct refutes its containing alternative. Do not feed
    // quantified or predicate-bearing clauses into the arithmetic solver.
    fn refuted_contract_conjunct(
        &mut self,
        claim: &Formula,
    ) -> Result<Option<(Vec<bool>, evidence::NodeId)>> {
        let mut pending = vec![(claim, Vec::new())];
        while let Some((claim, path)) = pending.pop() {
            self.charge_value_work(1 + path.len())?;
            if claim.is_arithmetic() {
                let negative = claim.clone().not();
                let Some(support) = self.probe_guard(&self.proof.paths.clone(), &negative)? else {
                    continue;
                };
                if support.parents.iter().any(|&node| {
                    self.proof.evidence.has_admissions(node)
                        || self.proof.evidence.has_pending_summaries(node)
                }) {
                    continue;
                }
                self.work.obligations += 1;
                let proof = self.proof.evidence.arithmetic(negative, support)?;
                return Ok(Some((path, proof)));
            }
            if let Formula::And(a, b) = claim {
                let mut right = path.clone();
                right.push(true);
                pending.push((b, right));
                let mut left = path;
                left.push(false);
                pending.push((a, left));
            }
        }
        Ok(None)
    }
}
