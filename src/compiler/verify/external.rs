//! Trusted external contracts. The kernel checks their use, not OS behavior.

use super::*;

impl Context<'_> {
    pub(super) fn check_external(&mut self, function: &Function, result: &Ty) -> Result<()> {
        if function.ideal
            || !function.ideal_params.is_empty()
            || function.decreases.is_some()
            || function.drop_target.is_some()
            || function.name == "main"
            || !function.borrows.is_empty()
            || function.params.len() > 6
            || function.ret != Type::Machine(MachineInt::parse("isize").unwrap())
        {
            return Err("syscall declarations require at most six runtime arguments and an isize result, without decreases, borrows, Drop, or ideal execution".into());
        }
        if !matches!(function.proof.as_deref(), Some([step]) if step == "trustme") {
            return Err("external syscall contracts require an explicit proof {trustme}".into());
        }
        for (_, ty) in &function.params {
            match ty {
                Type::Machine(integer) if integer.bits == 64 => {}
                Type::Ref(inner)
                    if !type_has_reference(inner, self.structs)
                        && !heap::owns_planes_type(inner, self.structs) => {
                    crate::compiler::layout::of(inner, self.structs)?;
                }
                _ => return Err("syscall arguments require 64-bit integers or borrows of fixed-layout data without pointers or owners".into()),
            }
        }
        // Check the contract's expressions normally, but make no claim to have
        // proved that the operating system implements it. Audit the entire
        // declaration even when no caller uses its postcondition.
        self.phase = Phase::Specification;
        // A postcondition describes the state after the declared writes, not
        // an accidental equality between entry and exit symbols.
        for write in self.writable.clone() {
            let id = self.memory.plane(write.reference)?;
            let mut value = self.arbitrary(&write.ty)?;
            self.charge_value_work(symbol_weight(self.memory.read(write.reference)?)?)?;
            let mut root = self.memory.read(write.reference)?.clone();
            self.preserve_views(project(&root, &write.path)?, &mut value)?;
            self.replace_projection(&mut root, &write.path, value)?;
            self.memory.write(id, root, false)?;
        }
        let value = self.arbitrary(result)?;
        self.env.insert("result".into(), value);
        if let Some(post) = &function.post {
            self.proposition(post)?;
        }
        self.session.trust(
            &[],
            format!("linux-x86_64 syscall declaration {function:?}").as_bytes(),
            function.line,
            &format!("external syscall contract for {}", function.name),
        )?;
        self.obligations += 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DECLARATION: &str =
        "extern syscall(39) fn process_id() -> isize ensures(result > 0); proof {trustme}";

    #[test]
    fn external_contracts_are_audited_replayable_and_runtime_only() {
        let source = format!("{DECLARATION} fn main() -> usize {{let id = process_id(); proof positive: id > 0; 42}}");
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(bundle.trusted_assumption_count(), 1);
        let replay = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(replay.proof_search_count(), 0);
        assert_eq!(replay.trusted_assumptions().len(), 1);
        assert_eq!(
            program
                .potentially_diverging_functions()
                .collect::<Vec<_>>(),
            ["process_id", "main"]
        );
        assert!(program.run().unwrap_err().contains("native executable"));
        let unused = verify(&format!("{DECLARATION} fn main() -> usize {{42}}")).unwrap();
        assert_eq!(unused.trusted_assumptions().len(), 1);
        assert!(
            verify_with_certificate(&source.replace("syscall(39)", "syscall(110)"), &bundle)
                .is_err()
        );
        for body in [
            "fn main() -> usize {proof impossible: process_id() > 0; 42}",
            "ideal fn erased() -> isize {process_id()} fn main() -> usize {42}",
            "fn main() -> usize where(process_id() > 0) {42}",
        ] {
            assert!(
                verify(&format!("{DECLARATION} {body}")).is_err(),
                "accepted {body}"
            );
        }
    }

    #[test]
    fn invalid_external_interfaces_and_unchecked_calls_are_rejected() {
        for declaration in [
            "extern syscall(39) fn bad() -> isize;",
            "extern syscall(39) fn bad() -> isize; proof {omega}",
            "extern syscall(39) fn bad() -> u8; proof {trustme}",
            "extern syscall(39) fn bad(a: u8) -> isize; proof {trustme}",
            "extern syscall(39) fn bad(a: [u8; 1]) -> isize; proof {trustme}",
            "extern syscall(39) fn bad(a: plane(u8)) -> isize; proof {trustme}",
            "extern syscall(39) fn bad(a: &&u8) -> isize; proof {trustme}",
            "extern syscall(39) fn bad(a: usize, b: usize, c: usize, d: usize, e: usize, f: usize, g: usize) -> isize; proof {trustme}",
            "ideal extern syscall(39) fn bad() -> isize; proof {trustme}",
            "extern syscall(39) fn bad() -> isize decreases(0); proof {trustme}",
            "extern syscall(39) fn bad() -> isize ensures(result); proof {trustme}",
            "extern syscall(39) fn bad() -> isize {0}",
            "extern syscall(4294967296) fn bad() -> isize; proof {trustme}",
        ] {
            assert!(verify(&format!("{declaration} fn main() -> usize {{42}}")).is_err(), "accepted {declaration}");
        }
        let io = include_str!("../../../stdlib/linux_io.evg");
        assert!(verify(&format!(
            "{io} fn main() -> isize {{let byte: u8 = 42; linux_io::write_byte(1, &byte, 2)}}"
        ))
        .is_err());
        let undeclared_write = "extern syscall(0) fn read(fd: usize, byte: &u8, count: usize) -> isize where(count <= 1) modifies(byte); proof {trustme} fn forward(byte: &u8) -> isize {read(0, byte, 1)} fn main() -> usize {42}";
        assert!(verify(undeclared_write).unwrap_err().contains("modifies"));
        let invalid_exit_index = "extern syscall(0) fn bad(index: &usize, data: &[u8; 1]) -> isize where(*index == 0) modifies(index) ensures((*data)[*index] == 0); proof {trustme} fn main() -> usize {42}";
        assert!(verify(invalid_exit_index).is_err());
        let alias = "extern syscall(39) fn inspect(a: &u8, b: &u8) -> isize; proof {trustme} fn main() -> isize {let a: u8 = 42; inspect(&a, &a)}";
        assert!(verify(alias).unwrap_err().contains("overlapping reference"));
        let opened = "type Data struct {n: usize} where(fact positive = n > 0; positive); extern syscall(39) fn process_id() -> isize; proof {trustme} fn main() -> usize {let data = Data {n: 1}; update(data) lifts positive {let id = process_id();} data.n}";
        assert!(verify(opened).unwrap_err().contains("invariants are open"));
    }
}
