//! Apply a checked function's advertised guarantee to the actual call state.

use super::*;

impl Context<'_> {
    pub(super) fn apply_postcondition(
        &mut self,
        post: &Expr,
        origins: &BTreeMap<String, ArgumentOrigin>,
        dependencies: &[evidence::NodeId],
        value: &Symbol,
        line: usize,
    ) -> Result<()> {
        let admitted = dependencies.iter().any(|&node| {
            self.proof.evidence.has_admissions(node)
                || self.proof.evidence.has_pending_summaries(node)
        });
        let (proposition, subjects) = if !admitted {
            // Evaluating pure accessors can establish relations for fresh
            // result symbols. Checked inputs must retain those observations;
            // only tainted contracts need the isolated path below.
            let proposition = self.proposition(post)?;
            if proposition.is_arithmetic() && dependencies.is_empty() {
                return self.assume(&proposition);
            }
            let subjects = self.call_subjects(post, origins, line, true)?;
            (proposition, subjects)
        } else {
            let paths = self.proof.paths.clone();
            let subjects = self.call_subjects(post, origins, line, true)?;
            let proposition = self.proposition(post)?;
            self.proof.paths = paths;
            (proposition, subjects)
        };
        let arithmetic = proposition.is_arithmetic();
        let node = self.proof.evidence.applied_contract(
            proposition.clone(),
            dependencies.to_vec(),
            self.proof.control.as_ref().unwrap_or(&Formula::True),
        )?;
        if arithmetic && self.evidence_dependencies(node)?.admissions.is_empty() {
            if let Some(subjects) = subjects {
                self.record_recursive_context(node, subjects)?;
            }
            self.assume_from(&proposition, paths::Origin::Evidence(node))
        } else {
            self.publish_call_contract(node, subjects.unwrap_or_default(), value, line)?;
            Ok(())
        }
    }
}
