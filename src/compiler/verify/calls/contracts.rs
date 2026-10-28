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
        let (proposition, subjects) = if dependencies.is_empty() {
            let proposition = self.proposition(post)?;
            if proposition.is_arithmetic() {
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
        let node = self
            .proof
            .evidence
            .contract(proposition.clone(), dependencies.to_vec())?;
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
