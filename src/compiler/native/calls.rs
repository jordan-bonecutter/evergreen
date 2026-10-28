//! Call expressions and the private native argument/return convention.

use super::*;

impl Emitter<'_> {
    pub(super) fn push_value(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            let size = storage::argument_size(ty, self.structs)?;
            self.code.extend([0x48, 0x81, 0xec]);
            self.code.extend((size as u32).to_le_bytes());
            self.temporary += size;
            self.peak = self.peak.max(self.temporary);
            self.code.extend([0x48, 0x89, 0xe1]); // rcx = argument home
            self.copy_address(ty)?;
        } else {
            self.push();
        }
        Ok(())
    }

    pub(super) fn invoke(&mut self, name: &str, argument_bytes: usize) -> Result<()> {
        let callee = self
            .known
            .get(name)
            .ok_or_else(|| format!("native callee {name} is recursive or has not been compiled"))?;
        self.peak = self.peak.max(self.temporary + 8 + callee.stack);
        self.code.push(0xe8);
        let displacement = self.code.len();
        self.code.extend([0; 4]);
        patch(self.code, displacement, callee.offset)?;
        if argument_bytes != 0 {
            self.code.extend([0x48, 0x81, 0xc4]);
            self.code.extend(
                u32::try_from(argument_bytes)
                    .map_err(|_| "native argument stack overflow")?
                    .to_le_bytes(),
            );
            self.temporary = self
                .temporary
                .checked_sub(argument_bytes)
                .ok_or("native argument stack underflow")?;
        }
        Ok(())
    }

    pub(super) fn call_expression(
        &mut self,
        name: &str,
        args: &[Expr],
        expected: Option<&Type>,
    ) -> Result<Type> {
        Ok(match name {
            "size_of" | "align_of" => {
                let value = layout::query::value(name, args, self.structs)?;
                self.immediate(value as u64);
                Type::Machine(MachineInt::parse("usize").unwrap())
            }
            name if MachineInt::parse(name).is_some() => {
                let target = Type::Machine(MachineInt::parse(name).unwrap());
                let [argument] = args else {
                    return Err("integer conversion requires one argument".into());
                };
                let source = self.hint(argument).unwrap_or_else(|| target.clone());
                self.expr(argument, Some(&source))?;
                // Verification proved representability. Registers already hold
                // the same mathematical value; conversion needs no instruction.
                target
            }
            "move" | "drop" | "leak" => {
                if args.len() != 1 {
                    return Err("invalid native move/drop".into());
                }
                let ty = self.expr(&args[0], None)?;
                if let Kind::Name(binding) = &args[0].kind {
                    self.mark_moved(binding);
                }
                if name == "drop" {
                    self.drop_value(&ty)?;
                    self.immediate(0);
                    Type::Unit
                } else if name == "leak" {
                    self.immediate(0);
                    Type::Unit
                } else {
                    ty
                }
            }
            "alloc" if args.len() == 2 => self.allocate_filled(args, expected)?,
            "alloc" => {
                let [value] = args else {
                    return Err("allocation requires one value or a count and initializer".into());
                };
                self.allocate_value(value, expected)?
            }
            "shape" => {
                let [value] = args else {
                    return Err("shape requires one type".into());
                };
                self.shape_value(value)?
            }
            _ => {
                let function = self.functions.get(name).ok_or("unknown native callee")?;
                let supplied = function.supplied_parameters(args.len())?;
                let saved_temporary = self.temporary;
                for ((parameter, ty), arg) in supplied.into_iter().zip(args) {
                    if function.ideal_params.contains(parameter) {
                        continue;
                    }
                    self.expr(arg, Some(ty))?;
                    self.push_value(ty)?;
                }
                if layout::aggregate(&function.ret) {
                    let output = self.allocate(&function.ret)?;
                    self.frame_address(output);
                    self.push();
                }
                self.invoke(name, self.temporary - saved_temporary)?;
                function.ret.clone()
            }
        })
    }
}
