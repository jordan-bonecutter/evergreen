//! State used while verifying one body. Declaration knowledge is immutable;
//! local bindings, execution mode, symbolic storage, and proof work are separate.

use super::*;

pub(super) struct Declarations<'a> {
    pub(super) functions: &'a BTreeMap<String, Function>,
    pub(super) structs: &'a BTreeMap<String, Struct>,
    pub(super) drops: &'a BTreeSet<String>,
    pub(super) destructors: &'a BTreeMap<String, Function>,
    pub(super) helpers: &'a BTreeSet<String>,
    pub(super) cleanup_helpers: &'a BTreeSet<String>,
}

#[derive(Default)]
pub(super) struct Locals {
    pub(super) values: BTreeMap<String, Symbol>,
    pub(super) places: BTreeMap<String, PlaneId>,
    pub(super) ideal_bindings: BTreeSet<String>,
    pub(super) module: Option<String>,
    pub(super) declaring: Option<String>,
}

#[derive(Default)]
pub(super) struct ProofState {
    pub(super) facts: BTreeMap<String, Expr>,
    pub(super) witnesses: BTreeMap<String, evidence::NodeId>,
    pub(super) evidence: evidence::Evidence,
    pub(super) subjects: subjects::Subjects,
    pub(super) paths: paths::Paths,
}

pub(super) struct Execution {
    pub(super) phase: Phase,
    pub(super) current: Option<String>,
    pub(super) measure: Option<Linear>,
    pub(super) ideal_execution: bool,
    pub(super) partial_execution: bool,
    pub(super) dropping: bool,
    pub(super) cleanup_depth: usize,
}

impl Default for Execution {
    fn default() -> Self {
        Self {
            phase: Phase::Runtime,
            current: None,
            measure: None,
            ideal_execution: false,
            partial_execution: false,
            dropping: false,
            cleanup_depth: 0,
        }
    }
}

#[derive(Default)]
pub(super) struct Storage {
    pub(super) memory: Memory<Symbol>,
    pub(super) opened_planes: BTreeMap<PlaneId, BTreeSet<String>>,
    pub(super) writable: Vec<WritePlace>,
    pub(super) inputs: Vec<InputReference>,
    pub(super) temporaries: Vec<(Symbol, usize)>,
}

#[derive(Default)]
pub(super) struct EntryState {
    pub(super) values: BTreeMap<String, Symbol>,
    pub(super) memory: Option<Box<EntryMemory>>,
}

#[derive(Default)]
pub(super) struct Arrays {
    pub(super) reads: BTreeMap<(String, Linear), Symbol>,
    pub(super) history: BTreeMap<String, ArrayHistory>,
    pub(super) read_depth: usize,
}

#[derive(Default)]
pub(super) struct Work {
    pub(super) fresh: usize,
    pub(super) eval_depth: usize,
    pub(super) eval_steps: usize,
    pub(super) value_work: usize,
    pub(super) obligations: usize,
}

pub(super) struct Context<'a> {
    pub(super) declarations: Declarations<'a>,
    pub(super) locals: Locals,
    pub(super) proof: ProofState,
    pub(super) execution: Execution,
    pub(super) storage: Storage,
    pub(super) entry: EntryState,
    pub(super) arrays: Arrays,
    pub(super) work: Work,
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
            work: Work::default(),
            session,
        }
    }
}
