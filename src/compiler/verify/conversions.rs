//! Checked numeric conversions preserve the mathematical integer value.

use super::*;

impl Context<'_> {
    pub(super) fn convert_integer(
        &mut self,
        target: MachineInt,
        args: &[Expr],
        line: usize,
    ) -> Result<Symbol> {
        let [argument] = args else {
            return Err("integer conversion requires exactly one integer".into());
        };
        let source = self.hint(argument).unwrap_or(Ty::Machine(target));
        if !matches!(source, Ty::Machine(_) | Ty::Int | Ty::Nat) {
            return Err("integer conversion requires an integer value".into());
        }
        let value = self.eval(argument, Some(&source))?.number()?;
        let (low, high) = target.bounds();
        self.prove(
            &Formula::Ge(value.sub(&Linear::number(low))?),
            "integer conversion lower bound",
            line,
        )?;
        self.prove(
            &Formula::Ge(Linear::number(high).sub(&value)?),
            "integer conversion upper bound",
            line,
        )?;
        Ok(Symbol::Number(Ty::Machine(target), value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_is_a_zero_only_word_without_pointer_authority() {
        let source = include_str!("../../../examples/null.evg");
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
            "fn main() -> Null {1}",
            "fn main() {let value: Null = 1;}",
            "fn main() {let value: Null = 0; value = 1;}",
            "fn set(value: &Null) modifies(value) {*value = 1;}",
            "fn null(value: usize) -> Null {Null(value)}",
            "fn main() -> Null {Null(usize::MAX + 1)}",
            "fn main() {let value: Null = 0; proof _: typeof(value) == usize;}",
            "fn main() {let pointer: unique(usize) = 0;}",
            "fn main() {let pointer: &usize = Null(0);}",
            "fn main() {let value: Null | unique(usize) = 0; let pointer: unique(usize) = move(value);}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn checked_conversions_preserve_values_and_replay() {
        let source = include_str!("../../../examples/integer_conversions.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        let maximum = "fn main() -> u64 {u64(18446744073709551615)}";
        assert_eq!(
            verify(maximum).unwrap().run().unwrap().to_string(),
            "18446744073709551615"
        );
    }

    #[test]
    fn conversions_require_bounds_and_cannot_materialize_erased_values() {
        for source in [
            "fn main() -> u8 {u8(256)}",
            "fn main() -> u8 {u8(-1)}",
            "fn main() -> isize {isize(usize::MAX)}",
            "fn main() -> usize {usize(isize::MIN)}",
            "fn main() -> u8 {u8(true)}",
            "fn main() -> u8 {u8()}",
            "fn main() -> u8 {u8(1, 2)}",
            "fn main() -> u8 {let n: usize = 42; u8(&n)}",
            "fn main() -> u8 {ideal let n: nat = 42; u8(n)}",
            "fn main() -> u8 {u8(nat(42))}",
            "fn narrow(n: usize) -> u8 {u8(n)} fn main() -> u8 {narrow(42)}",
            "fn main() -> i16 ensures result == 128 {i16(i8::MAX + 1)}",
            "fn u8() -> usize {42} fn main() -> usize {42}",
            "module m {fn usize() -> usize {42}} fn main() -> usize {42}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
        let ideal = "ideal fn byte(n: nat) -> u8 where(n <= 255) ensures(nat(result) == n) {u8(n)} fn main() -> usize {42}";
        assert!(verify(ideal).is_ok());
    }

    #[test]
    fn checked_conversions_work_in_entry_snapshots_and_drop_helpers() {
        let source = "fn widen(n: u8) -> usize ensures(nat(result) == nat(n)) {usize(n)} type Resource struct {tag: u8} where(tag == 7); impl Drop for Resource {fn drop(self) {let tag = widen(self.tag); proof valid: tag == 7;}} fn change(n: &u8) where(*n < u8::MAX) modifies(n) ensures(usize(*n) == old(usize(*n)) + 1) {*n = *n + 1;} fn main() -> usize {let resource = Resource {tag: 7}; let n: u8 = 41; change(&n); widen(n)}";
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    }
}
