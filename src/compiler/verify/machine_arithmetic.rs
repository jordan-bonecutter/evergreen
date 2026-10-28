//! Machine operations retain their mathematical value only when it fits.
//! Otherwise each execution produces a fresh value bounded by its result type.
//! No modular identity, equality between executions, or falsehood is assumed.

use super::*;

impl Context<'_> {
    pub(super) fn machine_arithmetic(&mut self, ty: &Ty, exact: Option<Linear>) -> Result<Symbol> {
        let Ty::Machine(integer) = ty else {
            return Err("machine arithmetic requires a machine type".into());
        };
        if let Some(value) = exact {
            let (lo, hi) = integer.bounds();
            if value.terms.is_empty() && (lo..=hi).contains(&value.constant) {
                return Ok(Symbol::Number(ty.clone(), value));
            }
            let bounds = value.sub(&Linear::number(lo)).and_then(|lower| {
                Ok(Formula::Ge(lower).and(Formula::Ge(Linear::number(hi).sub(&value)?)))
            });
            if let Ok(bounds) = bounds {
                if self.follows(&bounds)? {
                    return Ok(Symbol::Number(ty.clone(), value));
                }
            }
        }
        if self.execution.ideal_execution && self.execution.phase != Phase::Specification {
            return Err("ideal functions require defined machine arithmetic; prove its bounds or use integer arithmetic".into());
        }
        if self.execution.phase == Phase::Runtime {
            self.execution.unspecified_arithmetic = true;
        }
        self.arbitrary(ty)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unspecified_results_have_a_stable_binding_and_only_their_type_bounds() {
        let source = "fn increment(n: usize) -> usize {n + 1} fn main() -> usize {let value = increment(usize::MAX); proof _: typeof(value) == usize; proof _: value >= 0 && value <= usize::MAX; proof _: value == value; value}";
        let (program, bundle) = prove(source).unwrap();
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        for claim in [
            "value == 0",
            "value == usize::MAX",
            "value > usize::MAX",
            "value < 0",
            "false",
        ] {
            let bad = source.replace("proof _: value == value;", &format!("proof _: {claim};"));
            assert!(verify(&bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn repeated_overflow_expressions_do_not_imply_equal_results() {
        for source in [
            "fn main() {proof _: usize::MAX + 1 == 0;}",
            "fn main() {let a = usize::MAX + 1; let b = usize::MAX + 1; proof _: a == b;}",
            "fn main() {fact f = usize::MAX + 1 == 0; proof a: f by {trustme}; proof _: usize::MAX + 1 == 0;}",
            "fn main() {let a = usize::MAX + 1; proof _: a == usize::MAX + 1;}",
            "fn main() {fact f = usize::MAX + 1 == 0; proof a: f by {trustme}; proof b: f by {exact a};}",
        ] {
            assert!(verify(source).is_err(), "{source}");
        }
        verify("fn main() {proof _: typeof(usize::MAX + 1) == usize;}").unwrap();
        verify("ideal fn observe() -> bool {proof _: typeof(usize::MAX + 1) == usize; true}")
            .unwrap();
    }

    #[test]
    fn unspecified_operations_cannot_be_cached_as_pure_definitions() {
        for source in [
            "ideal fn increment(n: usize) -> usize {n + 1}",
            "fn increment(n: usize) -> usize {n + 1} fn main() {ideal let n = increment(usize::MAX);}",
            "fn increment(n: usize) -> usize {n + 1} fn forward(n: usize) -> usize {increment(n)} fn main() {ideal let n = forward(usize::MAX);}",
        ] {
            assert!(verify(source).is_err(), "{source}");
        }
        verify("ideal fn increment(n: usize) -> usize where n < usize::MAX {n + 1}").unwrap();
        verify("ideal fn increment(n: integer) -> integer {n + 1}").unwrap();
    }

    #[test]
    fn unconstrained_products_and_host_coefficient_overflow_become_typed_values() {
        for (ty, expression) in [
            ("u64", "u64::MAX * u64::MAX"),
            ("i64", "i64::MIN * i64::MIN"),
            ("u8", "u8::MAX + 1"),
            ("i8", "-i8::MIN"),
            ("u16", "0 - 1"),
        ] {
            let source = format!("fn main() -> {ty} {{let x: {ty} = {expression}; proof _: typeof(x) == {ty}; proof _: x >= {ty}::MIN && x <= {ty}::MAX; x}}");
            let (program, bundle) = prove(&source).unwrap();
            program.run().unwrap();
            verify_with_certificate(&source, &bundle).unwrap();
        }
        verify("fn multiply(a: usize, b: usize) -> usize {a * b}").unwrap();
    }

    #[test]
    fn unknown_results_still_need_index_and_record_refinement_proofs() {
        for source in [
            "fn main() -> usize {let data: [usize; 1] = [42]; let index = usize::MAX + 1; data[index]}",
            "type NonZero struct {data: usize} where data != 0; fn main() {let data = usize::MAX + 1; let value = NonZero {data: data};}",
        ] {
            assert!(verify(source).is_err(), "{source}");
        }
        verify("type NonZero struct {data: usize} where data != 0; fn main() {let data = usize::MAX + 1; if data != 0 {let value = NonZero {data: data};}} ").unwrap();
    }

    #[test]
    fn source_word_policies_and_associated_ideal_views_replay_without_trust() {
        let source = include_str!("../../../examples/non_overflowing_sum.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        for source in [
            source.replace("NonZero::new(10)", "NonZero::new(usize::MAX)"),
            source.replace(
                "sum.data\n}",
                "let raw = usize::MAX + 1; proof _: raw == 0; sum.data\n}",
            ),
            "fn main() -> usize {integer::from(42)}".into(),
            "fn main() {ideal let value = nat::from::<isize>(-1);}".into(),
            "fn main() {ideal let value = integer::from::<bool>(true);}".into(),
        ] {
            assert!(verify(&source).is_err(), "{source}");
        }
        let views = "fn views(value: i8) {proof _: integer::from::<i8>(value) == integer(value);} fn main() -> usize {ideal let value = nat::from::<isize>(42); proof _: value == 42; views(-1); 42}";
        let (program, bundle) = prove(views).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        verify_with_certificate(views, &bundle).unwrap();
    }

    #[test]
    fn exact_mathematical_contract_still_requires_a_bound() {
        let source =
            "fn increment(n: usize) -> usize ensures integer(result) == integer(n) + 1 {n + 1}";
        assert!(verify(source).unwrap_err().contains("postcondition"));
        let bounded = source.replace("ensures", "where n < usize::MAX ensures");
        verify(&bounded).unwrap();
    }
}
