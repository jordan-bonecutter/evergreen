//! Reference identity and the independent-input boundary of modular contracts.
use super::*;

impl Context<'_> {
    pub(super) fn reference_equality(&mut self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        let (Symbol::Ref(_, a, a_path), Symbol::Ref(_, b, b_path)) = (a, b) else {
            return Err("reference equality requires reference operands".into());
        };
        // Identity comparisons do not make stale generations observable again.
        project(self.memory.read(*a)?, a_path)?;
        project(self.memory.read(*b)?, b_path)?;
        self.charge_value_work(a_path.len().saturating_add(b_path.len()))?;
        if a != b || a_path.len() != b_path.len() {
            return Ok(Formula::False);
        }
        let mut same = Formula::True;
        for (a, b) in a_path.iter().zip(b_path) {
            let component = match (a, b) {
                (Projection::Field(a), Projection::Field(b)) if a == b => Formula::True,
                (Projection::Index(a), Projection::Index(b)) => equal(a, b)?,
                _ => return Ok(Formula::False),
            };
            same = same.and(component);
        }
        Ok(same)
    }

    pub(super) fn reference_ports_overlap(&mut self, inputs: &[InputReference]) -> Result<bool> {
        // Distinct planes need no pairwise arithmetic checks. Charge every
        // input and every same-plane comparison to the common proof-work budget.
        let mut planes: BTreeMap<PlaneId, Vec<usize>> = BTreeMap::new();
        for (index, input) in inputs.iter().enumerate() {
            self.charge_value_work(1)?;
            let plane = self.memory.plane(input.reference)?;
            let previous = planes.entry(plane).or_default();
            for other in previous.iter().map(|index| &inputs[*index]) {
                self.charge_value_work(1)?;
                if !self.paths_disjoint(&input.path, &other.path)? {
                    return Ok(true);
                }
            }
            previous.push(index);
        }
        Ok(false)
    }
}

impl Context<'_> {
    // Join constraints must be installed before checking the selected index or
    // materializing its view. No new plane is allocated for a conditional borrow.
    pub(super) fn materialize_joined_reference(
        &mut self,
        value: &Symbol,
        line: usize,
    ) -> Result<()> {
        let Symbol::Ref(target, reference, path) = value else {
            return Err("invalid joined reference".into());
        };
        let Some((Projection::Index(index), prefix)) = path.split_last() else {
            return Err("joined references require an array element".into());
        };
        self.charge_value_work(symbol_weight(self.memory.read(*reference)?)?)?;
        let mut root = self.memory.read(*reference)?.clone();
        let Symbol::Array {
            element,
            len,
            items,
            cells,
            identity,
        } = project(&root, prefix)?
        else {
            return Err("joined reference prefix requires array storage".into());
        };
        if element != target {
            return Err("joined reference element type changed".into());
        }
        self.prove(
            &Formula::Ge(index.clone()),
            "joined reference index is nonnegative",
            line,
        )?;
        self.prove(
            &Formula::Ge(len.sub(index)?.add(&Linear::number(-1))?),
            "joined reference index < length",
            line,
        )?;
        let value = self.read_array(element, identity, index, items.as_deref(), cells)?;
        let Symbol::Array { cells, .. } = project_mut(&mut root, prefix)? else {
            return Err("invalid joined array storage".into());
        };
        cells.insert(index.clone(), value);
        let plane = self.memory.plane(*reference)?;
        self.memory.write(plane, root, false)
    }
}
