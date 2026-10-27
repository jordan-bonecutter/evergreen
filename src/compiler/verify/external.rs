//! Trusted external contracts. The kernel checks their use, not machine behavior.

use super::*;

impl Context<'_> {
    pub(super) fn check_external(&mut self, function: &Function, result: &Ty) -> Result<()> {
        if function.ideal
            || function.decreases.is_some()
            || function.drop_target.is_some()
            || function.name == "main"
            || !function.borrows.is_empty()
        {
            return Err(
                "external declarations cannot be ideal, main, Drop, recursive, or return borrows"
                    .into(),
            );
        }
        if !matches!(function.proof.as_deref(), Some([step]) if step == "trustme") {
            return Err("external contracts require an explicit proof {trustme}".into());
        }
        let runtime = function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .collect::<Vec<_>>();
        match function.external {
            Some(syntax::External::Syscall(_)) => {
                self.check_syscall_interface(function, &runtime)?
            }
            Some(syntax::External::CompareExchange64) => {
                Self::check_compare_exchange_interface(function, &runtime)?
            }
            None => return Err("missing external operation".into()),
        }
        // Check the contract's expressions normally, but make no claim to have
        // proved that the target implements it. Audit the entire
        // declaration even when no caller uses its postcondition.
        self.execution.phase = Phase::Specification;
        // A postcondition describes the state after the declared writes, not
        // an accidental equality between entry and exit symbols.
        for write in self.storage.writable.clone() {
            let id = self.storage.memory.plane(write.reference)?;
            let mut value = self.arbitrary(&write.ty)?;
            self.charge_value_work(symbol_weight(self.storage.memory.read(write.reference)?)?)?;
            let mut root = self.storage.memory.read(write.reference)?.clone();
            self.preserve_views(project(&root, &write.path)?, &mut value)?;
            self.replace_projection(&mut root, &write.path, value)?;
            self.note_state_write(id, &write.path)?;
            self.storage.memory.write(id, root, false)?;
        }
        let value = self.arbitrary(result)?;
        self.locals.values.insert("result".into(), value);
        if let Some(post) = &function.post {
            self.proposition(post)?;
        }
        let trust = self.session.trust(
            &[],
            format!("x86_64 external declaration {function:?}").as_bytes(),
            function.line,
            &format!("external contract for {}", function.name),
        )?;
        let source = self.proof.evidence.import_trust(trust)?;
        self.proof.uses.push(source);
        self.proof.contract_uses.push(source);
        self.work.obligations += 1;
        Ok(())
    }

    fn check_syscall_interface(
        &self,
        function: &Function,
        runtime: &[&(String, Type)],
    ) -> Result<()> {
        if runtime.len() > 6 || function.ret != Type::Machine(MachineInt::parse("isize").unwrap()) {
            return Err(
                "syscall declarations require at most six runtime arguments and an isize result"
                    .into(),
            );
        }
        for (_, ty) in runtime {
            match ty {
                Type::Machine(integer) if integer.bits == 64 => {}
                Type::Ref(inner) if !type_has_reference(inner, self.declarations.structs)
                    && !heap::owns_planes_type(inner, self.declarations.structs) => {
                    let storage = match inner.as_ref() {
                        Type::Array(element, _) => element,
                        other => other,
                    };
                    crate::compiler::layout::of(storage, self.declarations.structs)?;
                }
                _ => return Err("syscall arguments require 64-bit integers or borrows without embedded pointers or owners".into()),
            }
        }
        Ok(())
    }

    fn check_compare_exchange_interface(
        function: &Function,
        runtime: &[&(String, Type)],
    ) -> Result<()> {
        let [(pointer, Type::Ref(inner)), (_, expected), (_, desired)] = runtime else {
            return Err(
                "compare_exchange64 requires a reference, expected value, and desired value".into(),
            );
        };
        if !matches!(inner.as_ref(), Type::Machine(integer) if integer.bits == 64)
            || inner.as_ref() != expected
            || expected != desired
            || function.ret != *expected
        {
            return Err(
                "compare_exchange64 operands and result must use the same 64-bit integer type"
                    .into(),
            );
        }
        if !matches!(function.modifies.as_slice(), [expression] if matches!(&expression.kind, Kind::Name(name) if name == pointer))
        {
            return Err(
                "compare_exchange64 requires a modifies footprint for its pointer operand".into(),
            );
        }
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
        let io = concat!(
            include_str!("../../../stdlib/linux_io/linux_io.evg"),
            "\u{1e}"
        );
        assert!(verify(&format!(
            "{io} fn main() -> isize {{let byte: u8 = 42; linux_io::write_byte(1, &byte, 2)}}"
        ))
        .is_err());
        for call in [
            "linux_io::write(1, &bytes, 3, 2)",
            "linux_io::write(1, &bytes, 2, 3)",
        ] {
            assert!(
                verify(&format!(
                    "{io} fn main() -> isize {{let bytes: [u8; 2] = [65, 66]; {call}}}"
                ))
                .is_err(),
                "accepted {call}"
            );
        }
        let prefix = format!("{io} fn main() -> isize {{let bytes: [u8; 3] = [65, 66, 67]; linux_io::write(1, &bytes, 2, 3)}}");
        let (program, bundle) = prove(&prefix).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(
            verify_with_certificate(&prefix, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
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

#[cfg(test)]
mod atomic_tests {
    use super::*;

    const ATOMIC: &str = concat!(
        include_str!("../../../stdlib/x86_64_atomics/x86_64_atomics.evg"),
        "\u{1e}"
    );

    #[test]
    fn compare_exchange_contracts_execute_and_replay() {
        let source = format!(
            "{ATOMIC} {}",
            include_str!("../../../examples/compare_exchange.evg")
        );
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }

    #[test]
    fn library_cas_loops_prove_overflow_underflow_and_final_decrement() {
        let source = format!(
            "{ATOMIC} {} {}",
            concat!(
                include_str!("../../../stdlib/atomic_counter/atomic_counter.evg"),
                "\u{1e}"
            ),
            include_str!("../../../examples/atomic_counter.evg")
        );
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(
            verify_with_certificate(&source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
    }

    #[test]
    fn atomic_interface_and_effect_errors_are_rejected() {
        for declaration in [
            "extern compare_exchange64 fn cas(v: &u8, e: u8, d: u8) -> u8 modifies(v); proof {trustme}",
            "extern compare_exchange64 fn cas(v: &usize, e: usize, d: usize) -> isize modifies(v); proof {trustme}",
            "extern compare_exchange64 fn cas(v: &usize, e: isize, d: usize) -> usize modifies(v); proof {trustme}",
            "extern compare_exchange64 fn cas(v: &usize, e: usize, d: usize) -> usize; proof {trustme}",
            "extern compare_exchange64 fn cas(v: &usize, e: usize, d: usize) -> usize modifies(v);",
            "extern compare_exchange64 fn cas(v: &usize, e: usize) -> usize modifies(v); proof {trustme}",
        ] {
            assert!(verify(&format!("{declaration} fn main() -> usize {{42}}")).is_err(), "accepted {declaration}");
        }
        let undeclared = format!("{ATOMIC} fn change(value: &usize) -> usize {{x86_64_atomics::compare_exchange(value, 7, 42)}} fn main() -> usize {{42}}");
        assert!(verify(&undeclared).unwrap_err().contains("modifies"));
        let erased = format!("{ATOMIC} fn main() -> usize {{let value: usize = 7; proof erased: x86_64_atomics::compare_exchange(&value, 7, 42) == 7; 42}}");
        assert!(verify(&erased).is_err());
    }
}
