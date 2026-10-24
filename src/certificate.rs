//! Portable, untrusted arithmetic proof artifacts. Replay regenerates all VCs
//! with the current frontend and checks every certificate against those VCs.
use crate::kernel::{self, Certificate, Linear};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, io::Read, path::Path, sync::Arc};
type Result<T> = std::result::Result<T, String>;
pub const MAX_ARTIFACT_BYTES: usize = 32 * 1024 * 1024;
const MAX_RECORDS: usize = 20_000;
const MAX_WEIGHTS: usize = 2048;
const MAX_CHECK_WORK: usize = 2_000_000;
const HEADER: &str = "evergreen-proof 1";
const MODEL: &str = "model bootstrap64-linear-v1";

fn source_hash(source: &str) -> String {
    let mut h = Sha256::new();
    h.update(b"evergreen-source-v1\0");
    h.update(source.as_bytes());
    format!("{:x}", h.finalize())
}
fn statement_hash(rows: &[Linear]) -> String {
    let mut h = Sha256::new();
    h.update(b"evergreen-linear-v1\0");
    h.update((rows.len() as u64).to_le_bytes());
    for row in rows {
        h.update(row.constant.to_le_bytes());
        h.update((row.terms.len() as u64).to_le_bytes());
        for (name, coefficient) in &row.terms {
            h.update((name.len() as u64).to_le_bytes());
            h.update(name.as_bytes());
            h.update(coefficient.to_le_bytes());
        }
    }
    format!("{:x}", h.finalize())
}
fn digest(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

#[derive(Clone, Debug)]
struct Record {
    statement: String,
    certificate: Option<Certificate>,
    optional: bool,
}
#[derive(Clone, Debug)]
struct TrustRecord {
    line: usize,
    statement: String,
}
#[derive(Clone, Debug)]
pub struct TrustedAssumption {
    pub line: usize,
    pub goal: String,
}
#[derive(Clone, Debug)]
pub struct ProofBundle {
    source: String,
    records: Arc<Vec<Record>>,
    trusted: Arc<Vec<TrustRecord>>,
}
impl ProofBundle {
    pub fn certificate_count(&self) -> usize {
        self.records
            .iter()
            .filter(|r| r.certificate.is_some())
            .count()
    }
    pub fn trusted_assumption_count(&self) -> usize {
        self.trusted.len()
    }
    pub fn to_text(&self) -> String {
        use std::fmt::Write;
        let mut out = format!(
            "{HEADER}\n{MODEL}\nsource {}\ntrusted {}\n",
            self.source,
            self.trusted.len()
        );
        for trust in self.trusted.iter() {
            let _ = writeln!(out, "{} {}", trust.line, trust.statement);
        }
        let _ = writeln!(out, "queries {}", self.records.len());
        for record in self.records.iter() {
            let weights = record
                .certificate
                .as_ref()
                .map(|c| c.weights().collect::<Vec<_>>())
                .unwrap_or_default();
            let tag = if record.certificate.is_none() {
                "miss"
            } else if record.optional {
                "probe"
            } else {
                "must"
            };
            let _ = write!(out, "{tag} {} {}", record.statement, weights.len());
            for (index, weight) in weights {
                let _ = write!(out, " {index}:{weight}");
            }
            out.push('\n');
        }
        out.push_str("end\n");
        out
    }
    pub fn parse(text: &str) -> Result<Self> {
        if text.len() > MAX_ARTIFACT_BYTES {
            return Err("proof artifact exceeds 32 MiB limit".into());
        }
        let mut lines = text.lines();
        if lines.next() != Some(HEADER) || lines.next() != Some(MODEL) {
            return Err("unsupported proof artifact format or data model".into());
        }
        let source = lines
            .next()
            .and_then(|s| s.strip_prefix("source "))
            .ok_or("missing source digest")?;
        if !digest(source) {
            return Err("invalid source digest".into());
        }
        let trusted_count = lines
            .next()
            .and_then(|s| s.strip_prefix("trusted "))
            .ok_or("missing trusted assumption count")?
            .parse::<usize>()
            .map_err(|_| "invalid trusted count")?;
        if trusted_count > MAX_RECORDS {
            return Err("trusted assumption limit reached".into());
        }
        let mut trusted = Vec::with_capacity(trusted_count);
        for _ in 0..trusted_count {
            let (line, statement) = lines
                .next()
                .and_then(|s| s.split_once(' '))
                .ok_or("malformed trusted assumption")?;
            let line = line
                .parse::<usize>()
                .map_err(|_| "invalid trusted source line")?;
            if line == 0 || !digest(statement) {
                return Err("invalid trusted assumption".into());
            }
            trusted.push(TrustRecord {
                line,
                statement: statement.into(),
            });
        }
        let count = lines
            .next()
            .and_then(|s| s.strip_prefix("queries "))
            .ok_or("missing proof count")?
            .parse::<usize>()
            .map_err(|_| "invalid proof count")?;
        if count > MAX_RECORDS {
            return Err("proof artifact record limit reached".into());
        }
        let mut records = Vec::with_capacity(count);
        for _ in 0..count {
            let mut fields = lines
                .next()
                .ok_or("truncated proof artifact")?
                .split_whitespace();
            let tag = fields.next().ok_or("missing query kind")?;
            if !matches!(tag, "must" | "probe" | "miss") {
                return Err("invalid proof query kind".into());
            }
            let statement = fields.next().ok_or("missing statement digest")?;
            if !digest(statement) {
                return Err("invalid statement digest".into());
            }
            let count = fields
                .next()
                .ok_or("missing certificate weight count")?
                .parse::<usize>()
                .map_err(|_| "invalid weight count")?;
            if count > MAX_WEIGHTS {
                return Err("certificate weight limit reached".into());
            }
            if tag == "miss" && count != 0 {
                return Err("optional miss cannot carry proof weights".into());
            }
            let mut weights = BTreeMap::new();
            for _ in 0..count {
                let (index, weight) = fields
                    .next()
                    .and_then(|s| s.split_once(':'))
                    .ok_or("malformed certificate weight")?;
                let index = index
                    .parse::<usize>()
                    .map_err(|_| "invalid certificate index")?;
                let weight = weight
                    .parse::<i128>()
                    .map_err(|_| "invalid certificate coefficient")?;
                if weights.insert(index, weight).is_some() {
                    return Err("duplicate certificate index".into());
                }
            }
            if fields.next().is_some() {
                return Err("trailing certificate fields".into());
            }
            records.push(Record {
                statement: statement.into(),
                certificate: if tag == "miss" {
                    None
                } else {
                    Some(Certificate::from_weights(weights)?)
                },
                optional: tag != "must",
            });
        }
        if lines.next() != Some("end") || lines.next().is_some() {
            return Err("missing end marker or trailing proof data".into());
        }
        Ok(Self {
            source: source.into(),
            records: Arc::new(records),
            trusted: Arc::new(trusted),
        })
    }
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let mut text = String::new();
        std::fs::File::open(path.as_ref())
            .map_err(|e| e.to_string())?
            .take((MAX_ARTIFACT_BYTES + 1) as u64)
            .read_to_string(&mut text)
            .map_err(|e| e.to_string())?;
        Self::parse(&text)
    }
    pub(crate) fn check_source(&self, source: &str) -> Result<()> {
        if self.source != source_hash(source) {
            return Err("proof artifact is for different source content".into());
        }
        Ok(())
    }
}

pub(crate) struct Session {
    replay: Option<ProofBundle>,
    cursor: usize,
    recording: bool,
    records: Vec<Record>,
    work: usize,
    trusted: Vec<TrustRecord>,
    trust_summary: Vec<TrustedAssumption>,
    searches: usize,
}
impl Session {
    pub(crate) fn search() -> Self {
        Self {
            replay: None,
            cursor: 0,
            recording: false,
            records: Vec::new(),
            work: 0,
            trusted: Vec::new(),
            trust_summary: Vec::new(),
            searches: 0,
        }
    }
    pub(crate) fn recording() -> Self {
        Self {
            recording: true,
            ..Self::search()
        }
    }
    pub(crate) fn replay(bundle: &ProofBundle) -> Self {
        Self {
            replay: Some(bundle.clone()),
            ..Self::search()
        }
    }
    pub(crate) fn prove(&mut self, rows: &[Linear]) -> Result<()> {
        if !self.query(rows, false)? {
            return Err("required certificate is missing".into());
        }
        Ok(())
    }
    pub(crate) fn probe(&mut self, rows: &[Linear]) -> Result<bool> {
        self.query(rows, true)
    }
    fn query(&mut self, rows: &[Linear], optional: bool) -> Result<bool> {
        if self.cursor >= MAX_RECORDS {
            return Err("verification query limit reached".into());
        }
        let statement = if self.recording || self.replay.is_some() {
            statement_hash(rows)
        } else {
            String::new()
        };
        let certificate = if let Some(bundle) = &self.replay {
            let record = bundle
                .records
                .get(self.cursor)
                .ok_or("proof artifact is missing a required query")?;
            if record.statement != statement || record.optional != optional {
                return Err(
                    "cached query does not match the regenerated verification condition".into(),
                );
            }
            record.certificate.clone()
        } else {
            self.searches += 1;
            match kernel::solve(rows) {
                Ok(certificate) => Some(certificate),
                Err(_) if optional => None,
                Err(e) => return Err(e),
            }
        };
        if let Some(certificate) = &certificate {
            let mut work = 0usize;
            for (index, _) in certificate.weights() {
                let row = rows.get(index).ok_or("certificate index out of range")?;
                work = work
                    .checked_add(row.terms.len() + 1)
                    .ok_or("proof checking work overflow")?;
            }
            self.work = self
                .work
                .checked_add(work)
                .ok_or("proof checking work overflow")?;
            if self.work > MAX_CHECK_WORK {
                return Err("proof checking work budget reached".into());
            }
            kernel::check(rows, certificate)?;
        } else if !optional {
            return Err("required goal has no certificate".into());
        }
        let proved = certificate.is_some();
        if self.recording {
            self.records.push(Record {
                statement,
                certificate,
                optional,
            });
        }
        self.cursor += 1;
        Ok(proved)
    }
    pub(crate) fn finish(&self) -> Result<()> {
        if self
            .replay
            .as_ref()
            .is_some_and(|b| b.records.len() != self.cursor)
        {
            return Err("proof artifact contains unused certificates".into());
        }
        if self
            .replay
            .as_ref()
            .is_some_and(|b| b.trusted.len() != self.trusted.len())
        {
            return Err("proof artifact contains unused trusted assumptions".into());
        }
        Ok(())
    }
    pub(crate) fn trust(
        &mut self,
        paths: &[Vec<Linear>],
        goal: &[u8],
        line: usize,
        label: &str,
    ) -> Result<()> {
        if self.trusted.len() >= MAX_RECORDS {
            return Err("trusted assumption limit reached".into());
        }
        let mut hash = Sha256::new();
        hash.update(b"evergreen-trusted-v1\0");
        hash.update((goal.len() as u64).to_le_bytes());
        hash.update(goal);
        hash.update((paths.len() as u64).to_le_bytes());
        for path in paths {
            hash.update(statement_hash(path).as_bytes());
        }
        let statement = format!("{:x}", hash.finalize());
        if let Some(bundle) = &self.replay {
            let expected = bundle
                .trusted
                .get(self.trusted.len())
                .ok_or("proof artifact omits a trustme assumption")?;
            if expected.line != line || expected.statement != statement {
                return Err(
                    "cached trusted assumption does not match the source obligation".into(),
                );
            }
        }
        self.trusted.push(TrustRecord { line, statement });
        self.trust_summary.push(TrustedAssumption {
            line,
            goal: label.into(),
        });
        Ok(())
    }
    pub(crate) fn trusted_assumptions(&self) -> &[TrustedAssumption] {
        &self.trust_summary
    }
    pub(crate) fn search_count(&self) -> usize {
        self.searches
    }
    pub(crate) fn bundle(self, source: &str) -> Result<ProofBundle> {
        let bundle = ProofBundle {
            source: source_hash(source),
            records: Arc::new(self.records),
            trusted: Arc::new(self.trusted),
        };
        if bundle.to_text().len() > MAX_ARTIFACT_BYTES {
            return Err("proof artifact exceeds 32 MiB limit".into());
        }
        Ok(bundle)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::{prove, verify, verify_with_certificate};
    #[test]
    fn checked_in_protocol_artifact_replays_without_search() {
        let bundle = ProofBundle::parse(include_str!("../proofs/rc_protocol.evgproof")).unwrap();
        let program =
            verify_with_certificate(include_str!("../proofs/rc_protocol.evg"), &bundle).unwrap();
        assert_eq!(program.proof_search_count(), 0);
        assert!(program.trusted_assumptions().is_empty());
    }
    #[test]
    fn opaque_credit_interfaces_replay_without_search() {
        let source = [
            include_str!("../stdlib/credits.evg"),
            include_str!("../proofs/opaque_credits.evg"),
            include_str!("../proofs/ideal_credit_bindings.evg"),
        ]
        .join("\n");
        let (_, bundle) = prove(&source).unwrap();
        let program = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(program.proof_search_count(), 0);
        assert!(program.trusted_assumptions().is_empty());
    }
    #[test]
    fn disjoint_write_contracts_replay_without_search() {
        let source = [
            include_str!("../stdlib/swap.evg"),
            include_str!("../examples/disjoint_writes.evg"),
        ]
        .join("\n");
        let (_, bundle) = prove(&source).unwrap();
        let program = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(program.proof_search_count(), 0);
        assert_eq!(program.run().unwrap().to_string(), "42");
    }
    #[test]
    fn erased_count_refinement_replays_and_executes_without_search() {
        let source = [
            include_str!("../proofs/rc_protocol.evg"),
            include_str!("../stdlib/counter.evg"),
            include_str!("../proofs/rc_count_refinement.evg"),
            include_str!("../examples/rc_count.evg"),
        ]
        .join("\n");
        let (_, bundle) = prove(&source).unwrap();
        let program =
            verify_with_certificate(&source, &ProofBundle::parse(&bundle.to_text()).unwrap())
                .unwrap();
        assert_eq!(program.proof_search_count(), 0);
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(program.run().unwrap().to_string(), "0");
    }

    #[test]
    fn replay_checks_certificates_without_search() {
        for source in [
            include_str!("../examples/ideal_bindings.evg"),
            include_str!("../examples/erased_resources.evg"),
            include_str!("../examples/opaque_values.evg"),
            include_str!("../examples/indexed_borrows.evg"),
            include_str!("../examples/weak_invariant.evg"),
            include_str!("../examples/array_borrows.evg"),
            include_str!("../examples/borrow_returns.evg"),
            include_str!("../examples/contracts.evg"),
            include_str!("../examples/drop.evg"),
            include_str!("../examples/selective_update.evg"),
            include_str!("../examples/conditional_records.evg"),
            include_str!("../examples/affine_values.evg"),
            include_str!("../examples/destructure.evg"),
            include_str!("../proofs/affine_credits.evg"),
            include_str!("../examples/write_contracts.evg"),
            include_str!("../examples/conditional_writes.evg"),
            include_str!("../stdlib/counter.evg"),
            include_str!("../examples/ideal_parameters.evg"),
            include_str!("../examples/array_contracts.evg"),
            include_str!("../proofs/rc_protocol.evg"),
        ] {
            let (original, bundle) = prove(source).unwrap();
            let text = bundle.to_text();
            let decoded = ProofBundle::parse(&text).unwrap();
            let replay = verify_with_certificate(source, &decoded).unwrap();
            assert_eq!(original.obligations, replay.obligations);
            assert_eq!(replay.proof_search_count(), 0);
            assert_eq!(prove(source).unwrap().1.to_text(), text);
            assert!(verify_with_certificate(&format!("{source}\n"), &decoded).is_err());
        }
    }

    #[test]
    fn replay_rejects_forged_missing_and_extra_evidence() {
        let source = include_str!("../examples/contracts.evg");
        let (_, bundle) = prove(source).unwrap();
        let mut forged = bundle.clone();
        let record = Arc::make_mut(&mut forged.records)
            .iter_mut()
            .find(|r| !r.optional && r.certificate.is_some())
            .unwrap();
        record.certificate =
            Some(Certificate::from_weights(BTreeMap::from([(usize::MAX, 1)])).unwrap());
        assert!(verify_with_certificate(source, &forged).is_err());
        let mut missing = bundle.clone();
        Arc::make_mut(&mut missing.records).clear();
        assert!(verify_with_certificate(source, &missing).is_err());
        let mut extra = bundle.clone();
        Arc::make_mut(&mut extra.records).push(bundle.records[0].clone());
        assert!(verify_with_certificate(source, &extra).is_err());
    }

    #[test]
    fn trust_is_explicit_and_cannot_be_hidden_in_artifacts() {
        let source = include_str!("../examples/trustme.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert_eq!(bundle.trusted_assumption_count(), 1);
        let replay =
            verify_with_certificate(source, &ProofBundle::parse(&bundle.to_text()).unwrap())
                .unwrap();
        assert_eq!(replay.trusted_assumptions().len(), 1);
        let mut hidden = bundle.clone();
        Arc::make_mut(&mut hidden.trusted).clear();
        assert!(verify_with_certificate(source, &hidden).is_err());
        let mut altered = bundle.clone();
        Arc::make_mut(&mut altered.trusted)[0].line += 1;
        assert!(verify_with_certificate(source, &altered).is_err());
        assert!(verify(&source.replace("trustme", "omega")).is_err());
        assert!(verify(&source.replace("trustme", "trustme; omega")).is_err());
    }

    #[test]
    fn layout_probe_misses_replay_conservatively() {
        let source = "type Storage struct {len: usize, data: [usize; len]} fn main() -> usize {let s = Storage {len: 1, data: [7]}; s = Storage {len: 2, data: [11, 42]}; s.data[1]}";
        let (_, bundle) = prove(source).unwrap();
        assert!(bundle
            .records
            .iter()
            .any(|r| r.optional && r.certificate.is_none()));
        let replay = verify_with_certificate(source, &bundle).unwrap();
        assert_eq!(replay.proof_search_count(), 0);
        assert_eq!(replay.run().unwrap().to_string(), "42");
        let mut forged = bundle.clone();
        let record = Arc::make_mut(&mut forged.records)
            .iter_mut()
            .find(|r| r.optional && r.certificate.is_none())
            .unwrap();
        record.certificate = Some(Certificate::from_weights(BTreeMap::from([(0, 1)])).unwrap());
        assert!(verify_with_certificate(source, &forged).is_err());
        let dangling = source
            .replace("s = Storage", "let r = &s.data[0]; s = Storage")
            .replace("s.data[1]", "*r");
        assert!(verify(&dangling).is_err());
    }

    #[test]
    fn malformed_artifacts_fail_closed() {
        let hash = "0".repeat(64);
        let prefix = format!("{HEADER}\n{MODEL}\nsource {hash}\ntrusted 0\nqueries 1\n");
        for record in [
            format!("must {hash} 1 0:0"),
            format!("must {hash} 1 0:-1"),
            format!("must {hash} 2 0:1 0:2"),
            format!("must {hash} 1 0:170141183460469231731687303715884105728"),
            format!("miss {hash} 1 0:1"),
            format!("must {hash} 2049"),
            format!("unknown {hash} 0"),
            format!("must {hash} 1"),
        ] {
            assert!(
                ProofBundle::parse(&format!("{prefix}{record}\nend\n")).is_err(),
                "{record}"
            );
        }
        assert!(ProofBundle::parse(&"x".repeat(MAX_ARTIFACT_BYTES + 1)).is_err());
    }
}
