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
        let execution = self.execution.phase;
        // This permits `bytes: &[u8; count], count: usize`, preserving the
        // source argument order required by an external ABI.
        for scalars in [true, false] {
            for (name, ty) in &function.params {
                if scalar(ty) != scalars {
                    continue;
                }
                self.execution.phase = if function.ideal_params.contains(name) {
                    Phase::Specification
                } else {
                    execution
                };
                let ty = self.resolve(ty)?;
                let value = self.arbitrary(&ty)?;
                self.locals.values.insert(name.clone(), value);
            }
        }
        self.execution.phase = execution;
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
            self.locals.values.insert(name.clone(), value);
        }
        let execution = self.execution.phase;
        for (name, ty) in &function.params {
            self.execution.phase = if function.ideal_params.contains(name) {
                Phase::Specification
            } else {
                execution
            };
            let expected = self.resolve(ty)?;
            let actual = self
                .locals
                .values
                .get(name)
                .ok_or("missing call argument")?
                .ty();
            self.compatible(&actual, &expected, line)?;
        }
        self.execution.phase = execution;
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

impl Context<'_> {
    pub(super) fn complete_arguments(
        &mut self,
        function: &Function,
        mut provided: BTreeMap<String, Symbol>,
        line: usize,
    ) -> Result<Vec<Symbol>> {
        for (name, ty) in &function.params {
            if provided.contains_key(name) {
                continue;
            }
            if !function.ideal_params.contains(name) {
                return Err(format!("line {line}: missing runtime argument {name}"));
            }
            let mut candidates = Vec::new();
            for (parameter, formal) in &function.params {
                if let Some(actual) = provided.get(parameter) {
                    infer_extent(formal, &actual.ty(), name, &mut candidates);
                }
            }
            let Some(value) = candidates.first().cloned() else {
                return Err(format!(
                    "line {line}: cannot infer ideal argument {name}; pass it explicitly"
                ));
            };
            for other in candidates.iter().skip(1) {
                self.prove(
                    &equal(&value, other)?,
                    "agreement of inferred array extents",
                    line,
                )?;
            }
            let target = match ty {
                Type::Nat => Ty::Nat,
                Type::Int => Ty::Int,
                Type::Machine(integer) => Ty::Machine(*integer),
                _ => {
                    return Err(format!(
                        "line {line}: ideal argument {name} requires an explicit value"
                    ))
                }
            };
            if !matches!(target, Ty::Int) {
                let (low, high) = match target {
                    Ty::Machine(integer) => (integer.bounds().0, Some(integer.bounds().1)),
                    _ => (0, None),
                };
                self.prove(
                    &Formula::Ge(value.sub(&Linear::number(low))?),
                    "inferred extent lower bound",
                    line,
                )?;
                if let Some(high) = high {
                    self.prove(
                        &Formula::Ge(Linear::number(high).sub(&value)?),
                        "inferred extent upper bound",
                        line,
                    )?;
                }
            }
            provided.insert(name.clone(), Symbol::Number(target, value));
        }
        function
            .params
            .iter()
            .map(|(name, _)| {
                provided
                    .remove(name)
                    .ok_or_else(|| format!("missing argument {name}"))
            })
            .collect()
    }
}

pub(super) fn infer_extent(formal: &Type, actual: &Ty, parameter: &str, out: &mut Vec<Linear>) {
    match (formal, actual) {
        (Type::Ref(formal), Ty::Ref(actual)) | (Type::Plane(formal), Ty::Plane(actual)) => {
            infer_extent(formal, actual, parameter, out);
        }
        (Type::Array(element, extent), Ty::Array(actual, length)) => {
            if matches!(&extent.kind, Kind::Name(name) if name == parameter) {
                out.push(length.clone());
            }
            infer_extent(element, actual, parameter, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod inference_tests {
    use super::*;

    #[test]
    fn array_extents_infer_erased_arguments_in_any_parameter_position() {
        let source = "fn sum(ideal n: nat, a: &[u8; n], ideal m: nat, b: &[u8; m]) -> u16 where(n > 0 && m > 0) {u16((*a)[0]) + u16((*b)[0])} fn main() -> u16 {let a: [u8; 1] = [40]; let b: [u8; 2] = [2, 3]; sum(&a, &b)}";
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        let arrays = "fn main() -> usize {let data: [usize; 2] = [7, 1]; arrays::set(&data, 1, 42); data[1]}";
        assert_eq!(verify(arrays).unwrap().run().unwrap().to_string(), "42");
        let explicit = source.replace("sum(&a, &b)", "sum(1, &a, 2, &b)");
        assert_eq!(verify(&explicit).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn inference_rejects_disagreeing_or_unavailable_evidence() {
        let same = "fn first(ideal n: nat, a: &[usize; n], b: &[usize; n]) -> usize where(n > 0) {(*a)[0]} fn main() -> usize {let a: [usize; 1] = [42]; let b: [usize; 2] = [1, 2]; first(&a, &b)}";
        assert!(verify(same).unwrap_err().contains("inferred array extents"));
        let unbound = "fn answer(ideal expected: nat) -> usize where(expected == 42) {42} fn main() -> usize {answer()}";
        assert!(verify(unbound)
            .unwrap_err()
            .contains("cannot infer ideal argument expected"));
        let overflow =
            "fn main() -> isize {let data: [u8; 2] = [65, 66]; linux_io::write(1, &data, 3)}";
        assert!(verify(overflow).is_err());
        let missing_runtime =
            "fn main() -> isize {let data: [u8; 2] = [65, 66]; linux_io::write(1, &data)}";
        assert!(verify(missing_runtime)
            .unwrap_err()
            .contains("3 runtime arguments"));
    }
}
