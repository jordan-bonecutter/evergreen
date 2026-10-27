//! String spelling supplies concrete bytes; values use the ordinary array
//! model and have no extra runtime string identity or UTF-8 invariant.

use super::*;

impl Context<'_> {
    pub(super) fn byte_literal(&mut self, bytes: &[u8]) -> Result<Symbol> {
        self.charge_value_work(bytes.len())?;
        let element = Ty::Machine(MachineInt {
            signed: false,
            bits: 8,
        });
        Ok(Symbol::Array {
            element: Box::new(element.clone()),
            len: Linear::number(bytes.len() as i128),
            items: Some(
                bytes
                    .iter()
                    .map(|&byte| Symbol::Number(element.clone(), Linear::number(i128::from(byte))))
                    .collect(),
            ),
            cells: BTreeMap::new(),
            identity: self.fresh_name(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_byte_arrays_preserve_unicode_extents_and_replay_without_trust() {
        let source = include_str!("../../../examples/string_bytes.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        for bad in [
            r#"fn main() {let text: [u16; 1] = "a";}"#,
            r#"fn main() {let text: [u8; 2] = "a";}"#,
            r#"fn main() -> u8 {"λ"[2]}"#,
            r#"fn main() -> u8 {let view = &"a"; (*view)[0]}"#,
            r#"fn main() -> u8 {ideal let text = "a"; text[0]}"#,
        ] {
            assert!(verify(bad).is_err(), "accepted {bad}");
        }
    }

    #[test]
    fn empty_string_and_array_values_keep_their_element_types() {
        for source in [
            r#"fn main() -> usize {ideal let text = "λ"; proof bytes: text[0] == 206 && text[1] == 187; 42}"#,
            r#"fn empty(ideal n: nat, data: &[u8; n]) -> usize where n == 0 {42} fn main() -> usize {let text = ""; empty(&text)}"#,
            r#"fn consume(value: [u8; 0]) -> usize {42} fn main() -> usize {let value: [u8; 0] | bool = ""; consume(value)}"#,
            "fn consume(value: [[u8; 2]; 0]) -> usize {42} fn make() -> [[u8; 2]; 0] {[]} fn main() -> usize {let value: [[u8; 2]; 0] | bool = make(); consume(value)}",
            "fn empty(data: [bool; 0]) -> usize {42} fn main() -> usize {let data: [bool; 0] = []; empty(data)}",
        ] {
            let (program, bundle) = prove(source).unwrap();
            assert_eq!(program.run().unwrap().to_string(), "42", "{source}");
            assert_eq!(verify_with_certificate(source, &bundle).unwrap().proof_search_count(), 0);
        }
    }
}
