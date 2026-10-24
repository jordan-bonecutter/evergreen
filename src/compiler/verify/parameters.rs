//! Parameter scopes: scalar indices are available throughout a signature.

use super::*;

fn scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Machine(_) | Type::Int | Type::Nat | Type::Bool | Type::Unit
    )
}

impl Context<'_> {
    pub(super) fn declare_parameters(&mut self, function: &Function) -> Result<()> {
        let mut names = BTreeSet::new();
        for (name, _) in &function.params {
            if !names.insert(name) {
                return Err(format!(
                    "line {}: duplicate parameter {name}",
                    function.line
                ));
            }
        }
        let execution = self.phase;
        // This permits `bytes: &[u8; count], count: usize`, preserving the
        // source argument order required by an external ABI.
        for scalars in [true, false] {
            for (name, ty) in &function.params {
                if scalar(ty) != scalars {
                    continue;
                }
                self.phase = if function.ideal_params.contains(name) {
                    Phase::Specification
                } else {
                    execution
                };
                let ty = self.resolve(ty)?;
                let value = self.arbitrary(&ty)?;
                self.env.insert(name.clone(), value);
            }
        }
        self.phase = execution;
        Ok(())
    }

    pub(super) fn bind_arguments(
        &mut self,
        function: &Function,
        values: Vec<Symbol>,
        line: usize,
    ) -> Result<()> {
        // Actual expressions have already been evaluated in source order and
        // checked for liveness. Resolve dependent types in the full callee scope.
        for ((name, _), value) in function.params.iter().zip(values) {
            self.env.insert(name.clone(), value);
        }
        let execution = self.phase;
        for (name, ty) in &function.params {
            self.phase = if function.ideal_params.contains(name) {
                Phase::Specification
            } else {
                execution
            };
            let expected = self.resolve(ty)?;
            let actual = self.env.get(name).ok_or("missing call argument")?.ty();
            self.compatible(&actual, &expected, line)?;
        }
        self.phase = execution;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIRST: &str =
        "fn first(bytes: &[u8; length], length: usize) -> u8 where(length > 0) {(*bytes)[0]}";

    #[test]
    fn later_scalar_indices_check_declarations_calls_and_replay() {
        let source =
            format!("{FIRST} fn main() -> u8 {{let bytes: [u8; 2] = [42, 7]; first(&bytes, 2)}}");
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        for body in [
            "let bytes: [u8; 2] = [42, 7]; first(&bytes, 1)",
            "let bytes: [u8; 2] = [42, 7]; first(&bytes, 3)",
            "let bytes: [u8; 0] = []; first(&bytes, 0)",
        ] {
            assert!(
                verify(&format!("{FIRST} fn main() -> u8 {{{body}}}")).is_err(),
                "accepted {body}"
            );
        }
        assert!(verify(
            "fn bad(bytes: &[u8; length], length: usize, length: usize) {} fn main() {}"
        )
        .is_err());
        assert!(verify("fn bad(bytes: &[u8; unknown], length: usize) {} fn main() {}").is_err());
    }

    #[test]
    fn argument_expressions_still_run_in_source_order() {
        let source = format!("{FIRST} fn change(length: &usize) -> usize modifies(length) ensures(result == 2 && *length == 2) {{*length = 2; 2}} fn main() -> u8 {{let length: usize = 1; let bytes: [u8; 2] = [42, 7]; let byte = first(&bytes, change(&length)); if byte == 42 && length == 2 {{42}} else {{1}}}}");
        assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
        // A scalar actual is checked even if a later type expression uses it.
        assert!(verify(&format!(
            "{FIRST} fn main() -> u8 {{let bytes: [u8; 2] = [42, 7]; first(&bytes, true)}}"
        ))
        .is_err());
    }
}
