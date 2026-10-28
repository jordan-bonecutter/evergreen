//! Link an observed input cell to a proved selector instance. This is a
//! frontend storage interpretation, separate from the kernel's ForallElim rule.

use super::*;

fn atom(formula: &Formula) -> Option<(&str, &[Linear], bool)> {
    match formula {
        Formula::Predicate { symbol, arguments } => Some((symbol, arguments, false)),
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Predicate { symbol, arguments } => Some((symbol, arguments, true)),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn specialization_term(
    pattern: &Formula,
    goal: &Formula,
    variable: &str,
) -> Result<Option<Linear>> {
    let (Some((a, aa, an)), Some((b, ba, bn))) = (atom(pattern), atom(goal)) else {
        return Ok(None);
    };
    if a != b || an != bn || aa.len() != ba.len() {
        return Ok(None);
    }
    let mut term = None;
    for (pattern, wanted) in aa.iter().zip(ba) {
        let coefficient = pattern.terms.get(variable).copied().unwrap_or(0);
        if coefficient == 0 {
            if pattern != wanted {
                return Ok(None);
            }
            continue;
        }
        let Some(candidate) = specialization_index(pattern, wanted, variable)? else {
            return Ok(None);
        };
        if term.as_ref().is_some_and(|term| term != &candidate) {
            return Ok(None);
        }
        term = Some(candidate);
    }
    Ok(Some(term.unwrap_or_else(|| Linear::number(0))))
}

pub(in crate::compiler::verify) fn specialization_index(
    pattern: &Linear,
    wanted: &Linear,
    variable: &str,
) -> Result<Option<Linear>> {
    let coefficient = pattern.terms.get(variable).copied().unwrap_or(0);
    if coefficient == 0 {
        return Ok((pattern == wanted).then(|| Linear::number(0)));
    }
    let mut remainder = pattern.clone();
    remainder.terms.remove(variable);
    let mut candidate = wanted.sub(&remainder)?;
    for value in std::iter::once(&mut candidate.constant).chain(candidate.terms.values_mut()) {
        if value
            .checked_rem(coefficient)
            .ok_or("proof arithmetic overflow")?
            != 0
        {
            return Ok(None);
        }
        *value = value
            .checked_div(coefficient)
            .ok_or("proof arithmetic overflow")?;
    }
    Ok(Some(candidate))
}

impl Context<'_> {
    fn unadmitted_evidence(&mut self, node: evidence::NodeId) -> Result<bool> {
        self.charge_value_work(1)?;
        Ok(!self.proof.evidence.has_admissions(node)
            && !self.proof.evidence.has_pending_summaries(node))
    }

    fn input_selector_instance(&mut self, goal: &Formula) -> Result<Option<evidence::NodeId>> {
        if let Some(node) = self.logical_assumption(goal, None)? {
            if self.unadmitted_evidence(node)? && self.proof.evidence.check_closed(node).is_ok() {
                return Ok(Some(node));
            }
        }
        let candidates = self
            .proof
            .claims
            .iter()
            .copied()
            .chain(self.proof.witnesses.values().copied())
            .collect::<BTreeSet<_>>();
        self.charge_value_work(candidates.len())?;
        for node in candidates {
            self.charge_value_work(self.proof.evidence.claim(node)?.storage_weight()?)?;
            let Formula::Forall { variable, body, .. } = self.proof.evidence.claim(node)?.clone()
            else {
                continue;
            };
            let Some(term) = specialization_term(&body, goal, &variable)? else {
                continue;
            };
            if let Some(instance) = self.checked_array_specialization(node, &term, goal)? {
                return Ok(Some(instance));
            }
        }
        Ok(None)
    }

    pub(in crate::compiler::verify) fn checked_array_specialization(
        &mut self,
        node: evidence::NodeId,
        term: &Linear,
        goal: &Formula,
    ) -> Result<Option<evidence::NodeId>> {
        let Formula::Forall {
            variable, domain, ..
        } = self.proof.evidence.claim(node)?.clone()
        else {
            return Ok(None);
        };
        if !self.unadmitted_evidence(node)? || self.proof.evidence.check_closed(node).is_err() {
            return Ok(None);
        }
        if let Some(snapshot) = self.proof.evidence.subjects(node).cloned() {
            let scope = self
                .proof
                .subjects
                .availability(&snapshot, &self.storage.memory, None)?;
            if !self.checked_entails(&scope)? {
                return Ok(None);
            }
        }
        let domain = domain.substitute(&variable, term)?;
        let paths = self.proof.paths.clone();
        let Some(support) = self.probe_guard(&paths, &domain)? else {
            return Ok(None);
        };
        let mut permitted = true;
        for &parent in &support.parents {
            permitted &= self.unadmitted_evidence(parent)?;
        }
        if !permitted {
            return Ok(None);
        }
        self.work.obligations += 1;
        let domain = self.proof.evidence.arithmetic(domain, support)?;
        let instance = self.proof.evidence.derive(
            goal.clone(),
            evidence::Rule::ForallElim {
                theorem: node,
                domain,
                term: term.clone(),
            },
        )?;
        self.proof.evidence.check_closed(instance)?;
        Ok(Some(instance))
    }

    pub(in crate::compiler::verify) fn observe_input_slot_types(
        &mut self,
        identity: &str,
        index: &Linear,
        value: &Symbol,
    ) -> Result<()> {
        let Symbol::Union { members, .. } = value else {
            return Ok(());
        };
        self.charge_value_work(symbol_weight(value)?)?;
        for target in members {
            let Some(selector) = self
                .arrays
                .type_predicates
                .get(&(identity.to_owned(), target.clone()))
            else {
                continue;
            };
            self.work.value_work = self.work.value_work.saturating_add(
                index.terms.len() + selector.captures.len() + selector.symbol.len(),
            );
            if self.work.value_work > MAX_VALUE_WORK {
                return Err("input selector observation work limit reached".into());
            }
            let application = Formula::Predicate {
                symbol: selector.symbol.clone(),
                arguments: std::iter::once(index.clone())
                    .chain(selector.captures.iter().map(Linear::variable))
                    .collect(),
            };
            for negative in [false, true] {
                let (claim, interpretation) = if negative {
                    (application.clone().not(), member(value, target)?.not())
                } else {
                    (application.clone(), member(value, target)?)
                };
                self.charge_value_work(
                    claim
                        .storage_weight()?
                        .saturating_add(interpretation.storage_weight()?),
                )?;
                if self.checked_entails(&interpretation)? {
                    continue;
                }
                let Some(premise) = self.input_selector_instance(&claim)? else {
                    continue;
                };
                // The frontend identifies this array version, cell, and tag.
                // This relation grants neither a predicate nor a live owner.
                let relation = self.proof.evidence.contract(
                    Formula::Implies(Box::new(claim), Box::new(interpretation.clone())),
                    Vec::new(),
                )?;
                let fact = self.proof.evidence.derive(
                    interpretation.clone(),
                    evidence::Rule::ImpElim {
                        theorem: relation,
                        argument: premise,
                    },
                )?;
                self.assume_from(&interpretation, paths::Origin::Evidence(fact))?;
            }
        }
        Ok(())
    }
}
