//! A historical branch fact can describe a current projection only where that
//! exact revision survived. Overlapping writes and dead generations stop reuse.

use super::*;

impl Subjects {
    pub(in crate::compiler::verify) fn branch_availability(
        &mut self,
        snapshot: &Snapshot,
        memory: &Memory<Symbol>,
    ) -> Result<Formula> {
        if !snapshot.complete {
            return Ok(Formula::False);
        }
        let (_, reads) = snapshot.guarded_reads(true)?;
        let mut available = Formula::True;
        let mut cache = BTreeMap::new();
        for (stamp, guard) in reads {
            let subject = self
                .entries
                .get(stamp.subject)
                .ok_or("missing branch proof subject")?;
            let same = if memory.plane(subject.reference).ok() == Some(subject.plane) {
                let current = self.history.region(
                    self.state.version(subject.plane),
                    stamp.subject,
                    &subject.path,
                )?;
                self.revision_condition(current, stamp, &mut cache, 0)?
            } else {
                Formula::False
            };
            available = available.and(guard.not().or(same));
        }
        Ok(available)
    }

    fn revision_condition(
        &mut self,
        current: state::Revision,
        wanted: Stamp,
        cache: &mut BTreeMap<(state::Revision, Stamp), Formula>,
        depth: usize,
    ) -> Result<Formula> {
        self.history.charge(1)?;
        if current == wanted.revision {
            return Ok(Formula::True);
        }
        if let Some(known) = cache.get(&(current, wanted)) {
            self.history.charge(known.storage_weight()?)?;
            return Ok(known.clone());
        }
        if depth >= 64 {
            return Err("branch proof revision depth limit reached".into());
        }
        let Some((_, condition, left, right)) = self.history.join_view(current) else {
            return Ok(Formula::False);
        };
        let path = self.entries[wanted.subject].path.clone();
        let left = self.history.region(left, wanted.subject, &path)?;
        let right = self.history.region(right, wanted.subject, &path)?;
        let left = self.revision_condition(left, wanted, cache, depth + 1)?;
        let right = self.revision_condition(right, wanted, cache, depth + 1)?;
        self.history.charge(
            condition
                .storage_weight()?
                .saturating_mul(2)
                .saturating_add(left.storage_weight()?)
                .saturating_add(right.storage_weight()?),
        )?;
        let result = if left == right {
            left
        } else {
            (*condition)
                .clone()
                .and(left)
                .or((*condition).clone().not().and(right))
        };
        cache.insert((current, wanted), result.clone());
        Ok(result)
    }
}
