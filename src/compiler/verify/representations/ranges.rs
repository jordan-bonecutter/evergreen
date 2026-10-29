//! Prefix copies observe bytes; the checked transfer moves existing payloads.
use super::*;

struct Operand {
    reference: Reference,
    path: Vec<Projection<Linear>>,
    array: Symbol,
    element: Ty,
    payload: Ty,
    len: Linear,
}

impl Context<'_> {
    fn range_operand(&mut self, expression: &Expr) -> Result<Operand> {
        let pointer = self.eval(expression, None)?;
        self.validate_argument(&pointer, expression.line)?;
        let Symbol::Ref(ty, reference, path) = pointer else {
            return Err("prefix representation needs array references".into());
        };
        let Ty::Array(element, len) = *ty else {
            return Err("prefix representation needs array storage".into());
        };
        let Ty::Union(members) = element.as_ref() else {
            return Err("prefix representation needs T | shape(T) elements".into());
        };
        let Some(Ty::Shape(payload)) = members.iter().find(|m| matches!(m, Ty::Shape(_))) else {
            return Err("prefix representation needs a shape member".into());
        };
        if members.len() != 2 || !members.contains(payload.as_ref()) {
            return Err("prefix representation needs exactly T | shape(T)".into());
        }
        let payload = *payload.clone();
        let cost = symbol_weight(project(self.storage.memory.read(reference)?, &path)?)?;
        self.charge_value_work(cost)?;
        let array = project(self.storage.memory.read(reference)?, &path)?.clone();
        Ok(Operand {
            reference,
            path,
            array,
            element: *element,
            payload,
            len,
        })
    }

    fn prefix_bits(&mut self, operand: &Operand, count: &Linear) -> Result<Linear> {
        let stamp = self.proof.subjects.observe(
            &self.storage.memory,
            operand.reference,
            operand.path.clone(),
        )?;
        let key = (stamp, count.clone());
        if let Some(bits) = self.proof.prefix_representations.get(&key) {
            return Ok(bits.clone());
        }
        let bits = Linear::variable(&self.fresh_name());
        self.proof.prefix_representations.insert(key, bits.clone());
        Ok(bits)
    }

    fn write_prefix_array(
        &mut self,
        operand: &Operand,
        value: Symbol,
        line: usize,
        validate: bool,
    ) -> Result<()> {
        self.validate_member_path(operand.reference, &operand.path, line)?;
        let plane = self.storage.memory.plane(operand.reference)?;
        let owned = self.owns_plane(plane)?;
        if !self.write_permitted(operand.reference, &operand.path, owned)? {
            return Err("prefix write needs a matching effect contract".into());
        }
        if project(self.storage.memory.read(operand.reference)?, &operand.path)?.ty() != value.ty()
        {
            return Err(
                "prefix transfer must preserve its physical array extent and element layout".into(),
            );
        }
        let cost = symbol_weight(self.storage.memory.read(operand.reference)?)?;
        self.charge_value_work(cost)?;
        let mut root = self.storage.memory.read(operand.reference)?.clone();
        self.replace_projection(&mut root, &operand.path, value)?;
        self.note_state_write(plane, &operand.path)?;
        self.storage.memory.write(plane, root.clone(), false)?;
        let lifted = self
            .storage
            .opened_planes
            .get(&plane)
            .cloned()
            .unwrap_or_default();
        if validate {
            self.retained_valid_with(&root, line, &lifted)?;
        }
        for (name, id) in &self.locals.places {
            if *id == plane {
                self.locals.values.insert(name.clone(), root.clone());
            }
        }
        if validate {
            self.validate_opened_planes(line)
        } else {
            Ok(())
        }
    }

    fn vacant_array(&mut self, element: &Ty, payload: &Ty, len: &Linear) -> Result<Symbol> {
        let vacant = self.union_coercion(
            Symbol::Shape(Box::new(payload.clone())),
            Some(element),
            0,
            None,
        )?;
        let identity = self.fresh_name();
        self.arrays
            .history
            .insert(identity.clone(), ArrayHistory::Uninitialized(vacant));
        Ok(Symbol::Array {
            element: Box::new(element.clone()),
            len: len.clone(),
            identity,
            items: None,
            cells: BTreeMap::new(),
        })
    }

    pub(super) fn range_representation_call(
        &mut self,
        name: &str,
        args: &[Expr],
        line: usize,
    ) -> Result<Symbol> {
        if args.iter().any(|arg| !arg.pure_read()) {
            return Err("prefix operations require pure arguments".into());
        }
        let source = self.range_operand(&args[0])?;
        let target = self.range_operand(&args[1])?;
        if source.element != target.element {
            return Err("prefix transfer requires identical element types at both ends".into());
        }
        let word = Ty::Machine(
            self.declarations
                .target
                .integer("usize")
                .ok_or("missing target usize")?,
        );
        let count = self.eval(&args[2], Some(&word))?.number()?;
        self.prove(
            &Formula::Ge(count.clone()),
            "nonnegative prefix length",
            line,
        )?;
        self.prove(
            &Formula::Ge(source.len.sub(&count)?),
            "source prefix bounds",
            line,
        )?;
        self.prove(
            &Formula::Ge(target.len.sub(&count)?),
            "destination prefix bounds",
            line,
        )?;
        let source_bits = self.prefix_bits(&source, &count)?;
        let target_bits = self.prefix_bits(&target, &count)?;
        if name == "same_representation" {
            if self.execution.phase == Phase::Runtime {
                return Err("representation equality is ideal-only".into());
            }
            return Ok(Symbol::Bool(equal(&source_bits, &target_bits)?));
        }
        if self.execution.phase != Phase::Runtime {
            return Err("prefix copies and transfers are runtime operations".into());
        }
        if self.storage.memory.plane(source.reference)?
            == self.storage.memory.plane(target.reference)?
            && subjects::overlap(&source.path, &target.path)
        {
            return Err("prefix copy and transfer require disjoint storage".into());
        }
        let zero = Linear::number(0);
        let shape = Ty::Shape(Box::new(source.payload.clone()));
        let empty = self.array_member_range(&target.array, &shape, &zero, &target.len)?;
        let empty_proof =
            self.prove_with_subjects(&empty, "vacant destination storage", line, None, None)?;
        let cleared = self.vacant_array(&target.element, &target.payload, &target.len)?;
        if name == "copy_representation" {
            let syntax = heap::syntax_type(&source.payload, line)?;
            let stride = crate::compiler::layout::of_for(
                self.declarations.target,
                &syntax,
                self.declarations.structs,
            )?
            .size;
            let maximum = self.declarations.target.max_array_length(stride);
            self.prove(
                &Formula::Ge(Linear::number(maximum).sub(&count)?),
                "prefix byte size fits target address range",
                line,
            )?;
            self.write_prefix_array(&target, cleared, line, true)?;
            let stamp =
                self.proof
                    .subjects
                    .observe(&self.storage.memory, target.reference, target.path)?;
            self.proof
                .prefix_representations
                .insert((stamp, count), source_bits);
            return Ok(Symbol::Unit);
        }
        let bits_equal = self.prove_with_subjects(
            &equal(&source_bits, &target_bits)?,
            "identical prefix representations",
            line,
            None,
            None,
        )?;
        let live = self.array_member_range(&source.array, &source.payload, &zero, &count)?;
        let live_proof =
            self.prove_with_subjects(&live, "initialized source prefix", line, None, None)?;
        let suffix = self.array_member_range(&source.array, &shape, &count, &source.len)?;
        let suffix_proof =
            self.prove_with_subjects(&suffix, "vacant source suffix", line, None, None)?;
        let retired = self.vacant_array(&source.element, &source.payload, &source.len)?;
        if let Symbol::Array { identity, .. } = &source.array {
            self.charge_value_work(symbol_weight(&source.array)?)?;
            self.arrays
                .frozen
                .entry(identity.clone())
                .or_insert_with(|| source.array.clone());
        }

        self.charge_value_work(symbol_weight(&source.array)?)?;
        let Symbol::Array {
            identity: base,
            items,
            mut cells,
            ..
        } = source.array.clone()
        else {
            return Err("missing source array".into());
        };
        // Shape byte identities do not move outside the copied prefix. Forget
        // those observations conservatively; live payloads keep their tokens.
        let clear_shape_bits = |value: &mut Symbol| {
            if let Symbol::Union {
                members, payloads, ..
            } = value
            {
                for (member, value) in members.iter().zip(payloads) {
                    if let Ty::Shape(ty) = member {
                        *value = Some(Symbol::Shape(ty.clone()));
                    }
                }
            }
        };
        for value in cells.values_mut() {
            clear_shape_bits(value);
        }
        let mut items = items;
        if let Some(items) = &mut items {
            for value in items {
                clear_shape_bits(value);
            }
        }
        let Symbol::Array { identity: rest, .. } = cleared else {
            return Err("missing vacant destination".into());
        };
        let identity = self.fresh_name();
        self.arrays.history.insert(
            identity.clone(),
            ArrayHistory::Prefix {
                end: count.clone(),
                base_len: source.len.clone(),
                base,
                rest,
            },
        );
        let moved = Symbol::Array {
            element: Box::new(target.element.clone()),
            len: target.len.clone(),
            identity,
            items,
            cells,
        };
        let pending = self.fresh_name();
        self.charge_value_work(symbol_weight(&moved)?.saturating_mul(2))?;
        self.locals.values.insert(pending.clone(), moved.clone());
        self.write_prefix_array(&source, retired, line, false)?;
        self.write_prefix_array(&target, moved.clone(), line, false)?;
        self.locals.values.remove(&pending);
        // The fact concerns this array contents revision, independently of
        // which local pointer currently carries its allocation authority.
        let stamp = self.proof.subjects.observe(
            &self.storage.memory,
            target.reference,
            target.path.clone(),
        )?;
        let snapshot = subjects::Snapshot::from_key(subjects::ClaimKey::Read(stamp));
        let initialized = self.array_member_range(&moved, &source.payload, &zero, &count)?;
        self.import_logical_contract(
            initialized,
            snapshot,
            vec![live_proof, suffix_proof, empty_proof, bits_equal],
        )?;
        // Type/ownership changes do not write bytes. Preserve the equality
        // of the transferred prefix at both successor contents revisions.
        for operand in [&source, &target] {
            let stamp = self.proof.subjects.observe(
                &self.storage.memory,
                operand.reference,
                operand.path.clone(),
            )?;
            self.proof
                .prefix_representations
                .insert((stamp, count.clone()), source_bits.clone());
        }
        // Both payload trees are installed before checking enclosing nominal
        // invariants. No source statement observes an intermediate type state.
        for operand in [&source, &target] {
            let plane = self.storage.memory.plane(operand.reference)?;
            self.charge_value_work(symbol_weight(self.storage.memory.get(plane)?)?)?;
            let root = self.storage.memory.get(plane)?.clone();
            let lifted = self
                .storage
                .opened_planes
                .get(&plane)
                .cloned()
                .unwrap_or_default();
            self.retained_valid_with(&root, line, &lifted)?;
        }
        self.validate_opened_planes(line)?;
        self.validate_live(line)?;
        Ok(Symbol::Unit)
    }
}
