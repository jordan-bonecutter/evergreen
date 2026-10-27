//! Program startup, function ABI, frame budgets, and compilation order.

use super::*;

struct Entry {
    main_call: usize,
    stack_pointer: usize,
}

struct ProgramEmitter<'a> {
    program: &'a VerifiedProgram,
    trace: TraceMode,
    code: Vec<u8>,
    known: BTreeMap<String, Compiled>,
    functions: BTreeMap<String, &'a Function>,
    drop_ids: BTreeMap<String, u32>,
    heap_ownership: bool,
}

pub(super) fn emit(program: &VerifiedProgram, trace: TraceMode) -> Result<Vec<u8>> {
    program.check_entry()?;
    let mut emitter = ProgramEmitter::new(program, trace)?;
    let entry = emitter.entry();
    for function in super::order::compilation_order(program)? {
        emitter.compile_function(function)?;
    }
    let main = emitter.known.get("main").ok_or("missing native main")?;
    patch(&mut emitter.code, entry.main_call, main.offset)?;
    Ok(super::elf::executable(emitter.code, entry.stack_pointer))
}

impl<'a> ProgramEmitter<'a> {
    fn new(program: &'a VerifiedProgram, trace: TraceMode) -> Result<Self> {
        let drop_ids = program
            .drops
            .iter()
            .enumerate()
            .map(|(index, name)| {
                Ok((
                    name.clone(),
                    u32::try_from(index + 1).map_err(|_| "native trace type count overflow")?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        let functions = program
            .functions
            .iter()
            .map(|function| (function.name.clone(), function))
            .collect();
        Ok(Self {
            program,
            trace,
            code: Vec::new(),
            known: BTreeMap::new(),
            functions,
            drop_ids,
            heap_ownership: program.uses_owned_planes(),
        })
    }

    fn entry(&mut self) -> Entry {
        self.code.extend([0x48, 0xbc]); // mov rsp, private stack end
        let stack_pointer = self.code.len();
        self.code.extend([0; 8]);
        self.code.extend([0x45, 0x31, 0xf6]); // r14: recursive activations
        if self.trace != TraceMode::Value {
            self.code.extend([0x4d, 0x31, 0xff]);
        }
        self.code.push(0xe8);
        let main_call = self.code.len();
        self.code.extend([0; 4]);
        self.code.extend(if self.trace == TraceMode::Value {
            [0x48, 0x89, 0xc7]
        } else {
            [0x4c, 0x89, 0xff]
        });
        self.code
            .extend([0xb8, 60, 0, 0, 0, 0x0f, 0x05, 0x0f, 0x0b]);
        Entry {
            main_call,
            stack_pointer,
        }
    }

    fn compile_function(&mut self, function: &Function) -> Result<()> {
        if function.ideal {
            return Ok(());
        }
        if function.name == "main" {
            scalar(&function.ret)?;
        }
        let parameters = ParameterLayout::new(function, &self.program.structs)?;
        let offset = self.code.len();
        let recursive = crate::compiler::effects::recursive(function);
        let frame_fixup = self.begin_function(&function.name, offset, recursive);
        let mut emitter = Emitter {
            code: &mut self.code,
            known: &self.known,
            functions: &self.functions,
            slots: BTreeMap::new(),
            frame: 0,
            structs: &self.program.structs,
            temporary: 0,
            peak: 0,
            drops: &self.program.drops,
            alive: BTreeSet::new(),
            temporaries: Vec::new(),
            trace: self.trace,
            drop_ids: &self.drop_ids,
        };
        parameters.bind(&mut emitter)?;
        if let Some(external) = function.external {
            match external {
                External::Syscall(number) => emitter.syscall(function, number)?,
                External::CompareExchange64 => emitter.compare_exchange64(function)?,
            }
        } else {
            for statement in &function.body {
                emitter.statement(statement)?;
            }
            emitter.scoped_expr(&function.result, Some(&function.ret))?;
        }
        let preserve_result = !self.program.drops.is_empty() || self.heap_ownership;
        emitter.return_from_function(function, &parameters, preserve_result)?;
        let stack = emitter.finish_function(frame_fixup, recursive)?;
        self.known
            .insert(function.name.clone(), Compiled { offset, stack });
        Ok(())
    }

    fn begin_function(&mut self, name: &str, offset: usize, recursive: bool) -> usize {
        if recursive {
            // This limits execution resources; it is not a termination proof.
            self.code.extend([0x49, 0x81, 0xfe]); // cmp r14, limit
            self.code.extend((RECURSION_LIMIT as u32).to_le_bytes());
            self.code.extend([0x72, 14]); // jb over exit(125), ud2
            self.code.extend([
                0xbf, 125, 0, 0, 0, 0xb8, 60, 0, 0, 0, 0x0f, 0x05, 0x0f, 0x0b,
            ]);
            self.code.extend([0x49, 0xff, 0xc6]); // inc r14
                                                  // A self edge contributes no callee estimate. The local frame and
                                                  // maximum outgoing call cost are multiplied in finish_function.
            self.known
                .insert(name.to_owned(), Compiled { offset, stack: 0 });
        }
        self.code.extend([0x55, 0x48, 0x89, 0xe5, 0x48, 0x81, 0xec]);
        let frame_fixup = self.code.len();
        self.code.extend([0; 4]);
        frame_fixup
    }
}

struct ParameterLayout<'a> {
    values: Vec<&'a (String, Type)>,
    sizes: Vec<usize>,
    result_pointer: usize,
}

impl<'a> ParameterLayout<'a> {
    fn new(function: &'a Function, structs: &BTreeMap<String, Struct>) -> Result<Self> {
        layout::of(&function.ret, structs)?;
        let result_pointer = usize::from(layout::aggregate(&function.ret)) * 8;
        let values = function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .collect::<Vec<_>>();
        let sizes = values
            .iter()
            .map(|(_, ty)| storage::argument_size(ty, structs))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            values,
            sizes,
            result_pointer,
        })
    }

    fn bind(&self, emitter: &mut Emitter<'_>) -> Result<()> {
        let mut incoming_offsets = vec![0usize; self.sizes.len()];
        let mut incoming_bytes = 16 + self.result_pointer;
        for index in (0..self.sizes.len()).rev() {
            incoming_offsets[index] = incoming_bytes;
            incoming_bytes = incoming_bytes
                .checked_add(self.sizes[index])
                .ok_or("native parameter layout overflow")?;
        }
        for (index, (name, ty)) in self.values.iter().enumerate() {
            emitter.code.extend(if layout::aggregate(ty) {
                [0x48, 0x8d, 0x85]
            } else {
                [0x48, 0x8b, 0x85]
            });
            let incoming = u32::try_from(incoming_offsets[index])
                .map_err(|_| "native parameter offset overflow")?;
            emitter.code.extend(incoming.to_le_bytes());
            emitter.slot(name, ty.clone())?;
        }
        Ok(())
    }
}

impl Emitter<'_> {
    fn return_from_function(
        &mut self,
        function: &Function,
        parameters: &ParameterLayout<'_>,
        preserve_result: bool,
    ) -> Result<()> {
        let saved_result = if !preserve_result {
            None
        } else {
            let home = self.allocate(&function.ret)?;
            self.copy_frame(home, &function.ret)?;
            Some(home)
        };
        let names = parameters
            .values
            .iter()
            .map(|(n, _)| n.as_str())
            .chain(
                function
                    .body
                    .iter()
                    .flat_map(|statement| statement.runtime_bindings(self.structs)),
            )
            .collect::<Vec<_>>();
        for name in names.into_iter().rev() {
            self.cleanup_binding(name, name == "self" && function.drop_target.is_some())?;
        }
        if let Some(home) = saved_result {
            self.frame_address(home);
            if !layout::aggregate(&function.ret) {
                self.load_scalar(&function.ret)?;
            }
        }
        if parameters.result_pointer != 0 {
            self.code.extend([0x48, 0x8b, 0x8d]);
            self.code.extend(16i32.to_le_bytes());
            self.copy_address(&function.ret)?;
            self.code.extend([0x48, 0x89, 0xc8]);
        }
        Ok(())
    }

    fn finish_function(&mut self, frame_fixup: usize, recursive: bool) -> Result<usize> {
        if self.temporary != 0 {
            return Err("unbalanced native expression stack".into());
        }
        let frame = self.frame.next_multiple_of(8);
        self.code[frame_fixup..frame_fixup + 4].copy_from_slice(&(frame as u32).to_le_bytes());
        let stack = (8 + frame + self.peak)
            .checked_mul(if recursive { RECURSION_LIMIT } else { 1 })
            .ok_or("native recursion stack estimate overflow")?;
        if stack + 8 > STACK {
            return Err("native call tree exceeds 64 KiB private stack budget".into());
        }
        if recursive {
            self.code.extend([0x49, 0xff, 0xce]); // dec r14
        }
        self.code.extend([0x48, 0x89, 0xec, 0x5d, 0xc3]);
        if self.code.len() > MAX_CODE {
            return Err("native code exceeds 8 MiB limit".into());
        }
        Ok(stack)
    }
}
