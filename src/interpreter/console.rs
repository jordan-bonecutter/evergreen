//! The portable console boundary captures bytes, with the evaluator's work budget.

use super::*;

impl Evaluator<'_> {
    pub(super) fn console_write(&mut self, values: Vec<Value>) -> Result<Value> {
        let [length, Value::Ref(_, reference, path)] = values.as_slice() else {
            return Err("console_write operand mismatch".into());
        };
        let length = usize::try_from(length.number()?).map_err(|_| "invalid console length")?;
        let Value::Array(_, bytes) = project(self.memory.read(*reference)?, path)? else {
            return Err("console_write requires a byte array".into());
        };
        if length > bytes.len() || length > self.fuel {
            return Err("console output exceeds array bounds or execution work limit".into());
        }
        self.fuel -= length;
        for byte in &bytes[..length] {
            self.stdout
                .push(u8::try_from(byte.number()?).map_err(|_| "invalid console byte")?);
        }
        Ok(Value::Unit)
    }
}

#[cfg(test)]
mod tests {
    use crate::compiler::verify::{prove, verify, verify_with_certificate};

    #[test]
    fn console_bytes_are_captured_per_run_and_contract_replays() {
        let source = "fn main() {console::print(&\"λ\\0\"); console::println(&\"\");}";
        let (program, certificate) = prove(source).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        for _ in 0..2 {
            assert_eq!(
                super::super::run_with_output(&program).unwrap().1,
                "λ\0\n".as_bytes()
            );
        }
        assert_eq!(
            verify_with_certificate(source, &certificate)
                .unwrap()
                .proof_search_count(),
            0
        );
        assert!(verify(
            "extern console_write fn bad(n: usize, data: &u8); proof {trustme} fn main() {}"
        )
        .is_err());
    }
}
