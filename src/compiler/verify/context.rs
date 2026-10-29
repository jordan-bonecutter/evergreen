//! State used while verifying one body. Declaration knowledge is immutable;
//! local bindings, execution mode, symbolic storage, and proof work are separate.

use super::*;

#[derive(Clone, Copy)]
pub(super) struct Declarations<'a> {
    pub(super) target: crate::compiler::TargetKind,
    pub(super) summaries: &'a BTreeMap<String, summaries::Summary>,
    pub(super) functions: &'a BTreeMap<String, Function>,
    pub(super) structs: &'a BTreeMap<String, Struct>,
    pub(super) drops: &'a BTreeSet<String>,
    pub(super) destructors: &'a BTreeMap<String, Function>,
    pub(super) helpers: &'a BTreeSet<String>,
    pub(super) cleanup_helpers: &'a BTreeSet<String>,
}

#[derive(Default)]
pub(super) struct Locals {
    pub(super) quantified_checks: Vec<Vec<quantified::Check>>,
    pub(super) quantified_evaluation: usize,
    pub(super) logical_bindings: Vec<LogicalBinding>,
    pub(super) values: BTreeMap<String, Symbol>,
    pub(super) places: BTreeMap<String, PlaneId>,
    pub(super) ideal_bindings: BTreeSet<String>,
    pub(super) module: Option<String>,
    pub(super) declaring: Option<String>,
}

pub(super) struct LogicalBinding {
    pub(super) name: String,
    pub(super) variable: String,
    pub(super) quantified: bool,
}

#[derive(Default)]
pub(super) struct ProofState {
    // Immutable normalization results, not proofs or state-dependent truth.
    pub(super) normal_forms: BTreeMap<Formula, std::sync::Arc<Formula>>,
    // Closed arithmetic theorems proved solely from their own quantified domains.
    pub(super) definedness: BTreeMap<Formula, evidence::NodeId>,
    pub(super) representations: BTreeMap<subjects::Stamp, Linear>,
    pub(super) facts: BTreeMap<String, Expr>,
    // Dependency footprints, indexed by call identity; never cached truth.
    pub(super) fact_calls: BTreeMap<subjects::ClaimKey, Vec<subjects::Snapshot>>,
    pub(super) witnesses: BTreeMap<String, evidence::NodeId>,
    // Subjects of named intermediate proofs live only for their proof scope.
    pub(super) scoped_subjects: BTreeMap<evidence::NodeId, subjects::Snapshot>,
    pub(super) evidence: evidence::Evidence,
    pub(super) subjects: subjects::Subjects,
    pub(super) claims: BTreeSet<evidence::NodeId>,
    // A branch-local logical claim remains usable only in its original arm.
    pub(super) claim_guards: BTreeMap<evidence::NodeId, Formula>,
    pub(super) value_claims: Vec<evidence::NodeId>,
    pub(super) uses: Vec<evidence::NodeId>,
    pub(super) contract_uses: Vec<evidence::NodeId>,
    pub(super) results: Vec<value_evidence::CallResult>,
    pub(super) control: Option<Formula>,
    pub(super) recursive_contexts: Vec<admissions::RecursiveContext>,
    pub(super) contract_parents: Vec<evidence::NodeId>,
    pub(super) paths: paths::Paths,
    pub(super) states: Vec<state::State>,
}

pub(super) struct Execution {
    pub(super) phase: Phase,
    pub(super) current: Option<String>,
    pub(super) measure: Option<Linear>,
    pub(super) ideal_execution: bool,
    pub(super) partial_execution: bool,
    pub(super) unspecified_arithmetic: bool,
    pub(super) dropping: bool,
    pub(super) cleanup_depth: usize,
    pub(super) replacing_cleanup: usize,
    pub(super) rechecking: usize,
    pub(super) materializing_input: bool,
    pub(super) deferred_cleanup_roots: BTreeSet<PlaneId>,
}

impl Default for Execution {
    fn default() -> Self {
        Self {
            phase: Phase::Runtime,
            current: None,
            measure: None,
            ideal_execution: false,
            partial_execution: false,
            unspecified_arithmetic: false,
            dropping: false,
            cleanup_depth: 0,
            replacing_cleanup: 0,
            rechecking: 0,
            materializing_input: false,
            deferred_cleanup_roots: BTreeSet::new(),
        }
    }
}

#[derive(Default)]
pub(super) struct Storage {
    pub(super) memory: Memory<Symbol>,
    pub(super) presence: BTreeMap<PlaneId, Formula>,
    pub(super) allocation_guard: Option<Formula>,
    pub(super) opened_planes: BTreeMap<PlaneId, BTreeSet<String>>,
    pub(super) writable: Vec<WritePlace>,
    pub(super) inputs: Vec<InputReference>,
    pub(super) temporaries: Vec<(Symbol, usize)>,
    pub(super) loops: Vec<loops::Frame>,
    pub(super) reference_reads: BTreeMap<guarded_references::ReadKey, Symbol>,
}

#[derive(Default)]
pub(super) struct EntryState {
    pub(super) world: state::WorldId,
    pub(super) values: BTreeMap<String, Symbol>,
    pub(super) memory: Option<Box<EntryMemory>>,
}

#[derive(Default)]
pub(super) struct Arrays {
    // Only words allocated as Booleans belong here; arbitrary numeric equalities
    // with one must never be mistaken for a Boolean representation.
    pub(super) boolean_words: BTreeMap<Formula, Linear>,
    pub(super) scalar_bindings:
        BTreeMap<array_values::Contents, BTreeMap<Linear, array_values::ReadBinding>>,
    pub(super) captured_values: BTreeMap<(array_values::Contents, Linear), Symbol>,
    pub(super) observing_values: BTreeSet<(array_values::Contents, Linear)>,
    pub(super) value_equalities: BTreeMap<array_values::Key, array_values::Equality>,
    pub(super) value_equality_origins: BTreeMap<String, array_values::Key>,
    pub(super) value_predicates: BTreeMap<String, BTreeSet<String>>,
    pub(super) value_literals: BTreeMap<String, Vec<Symbol>>,
    pub(super) type_predicates: BTreeMap<(String, Ty), array_predicates::Selector>,
    pub(super) predicate_definitions: BTreeMap<String, evidence::DefinitionId>,
    pub(super) reads: BTreeMap<(String, Linear), Symbol>,
    pub(super) history: BTreeMap<String, ArrayHistory>,
    // Whole-value frames for resource stores whose selector history retains a uniform default.
    pub(super) whole_stores: BTreeMap<String, (String, Linear)>,
    // Successful type transfers identify the written element with an earlier source value.
    pub(super) value_transfers: BTreeMap<String, (String, Linear)>,
    pub(super) read_depth: usize,
    pub(super) inputs: BTreeSet<String>,
    pub(super) ports: BTreeMap<String, BTreeMap<Linear, Symbol>>,
    pub(super) initial_planes: BTreeMap<PlaneId, Symbol>,
}

#[derive(Default)]
pub(super) struct Work {
    pub(super) fresh: usize,
    // Diagnostic metadata only; fresh identities are never reused across states.
    pub(super) scalar_types: BTreeMap<String, Ty>,
    // Address observations are lazy and stable for a live plane generation.
    // Logical provenance stays separate; equal addresses grant no authority.
    pub(super) empty_addresses: BTreeMap<(Reference, Vec<Projection>), Linear>,
    pub(super) eval_depth: usize,
    pub(super) eval_steps: usize,
    pub(super) value_work: usize,
    pub(super) obligations: usize,
    pub(super) ownership_transitions: usize,
}

pub(super) struct Context<'a> {
    pub(super) declarations: Declarations<'a>,
    pub(super) locals: Locals,
    pub(super) proof: ProofState,
    pub(super) execution: Execution,
    pub(super) storage: Storage,
    pub(super) entry: EntryState,
    pub(super) arrays: Arrays,
    pub(super) applications: ideal::Applications,
    pub(super) censuses: BTreeMap<Reference, Linear>,
    pub(super) work: Work,
    pub(super) cases: cases::Trace,
    pub(super) session: &'a mut Session,
}

impl<'a> Context<'a> {
    pub(super) fn new(declarations: Declarations<'a>, session: &'a mut Session) -> Self {
        Self {
            declarations,
            locals: Locals::default(),
            proof: ProofState {
                paths: paths::Paths::unit(),
                ..ProofState::default()
            },
            execution: Execution::default(),
            storage: Storage::default(),
            entry: EntryState::default(),
            arrays: Arrays::default(),
            applications: ideal::Applications::default(),
            censuses: BTreeMap::new(),
            work: Work::default(),
            cases: cases::Trace::default(),
            session,
        }
    }
}
