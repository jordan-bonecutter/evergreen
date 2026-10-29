//! Per-session diagnostic sink. Failed optional proof attempts cannot donate
//! stale details to a different final error; details follow the error message.

use super::Session;
use crate::shared::diagnostics::{Diagnostic, Requirement, SourceOrigin};

impl Session {
    pub(crate) fn clear_diagnostic(&mut self) {
        self.diagnostic = None;
    }

    fn failure(&mut self, message: &str) -> &mut Diagnostic {
        if !self
            .diagnostic
            .as_ref()
            .is_some_and(|diagnostic| message.contains(&diagnostic.message))
        {
            self.diagnostic = Some(Diagnostic::new(message));
        }
        let diagnostic = self.diagnostic.as_mut().unwrap();
        diagnostic.message = message.to_owned();
        diagnostic
    }

    pub(crate) fn note_obligation(&mut self, message: &str, goal: String) {
        self.failure(message).obligation = Some(goal);
    }

    pub(crate) fn note_source_obligation(&mut self, message: &str, goal: String) {
        self.failure(message).source_obligation = Some(goal.into_boxed_str());
    }

    pub(crate) fn note_requirement(&mut self, message: &str, requirement: Requirement) {
        self.failure(message).requirement = Some(Box::new(requirement));
    }

    pub(crate) fn note_source(&mut self, message: &str, origin: SourceOrigin, line: usize) {
        let diagnostic = self.failure(message);
        if diagnostic.origin == SourceOrigin::Unspecified {
            diagnostic.origin = origin;
        }
        if diagnostic.line.is_none() {
            diagnostic.line = Some(line);
        }
    }

    pub(crate) fn report(&mut self, message: String) -> Diagnostic {
        self.failure(&message);
        self.diagnostic.take().unwrap()
    }
}
