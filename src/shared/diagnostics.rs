//! Structured diagnostic details kept outside proof certificates and search.

use std::{fmt, path::PathBuf};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SourceOrigin {
    #[default]
    Unspecified,
    Input(usize),
    Bundled(&'static str),
}

#[derive(Clone, Debug)]
pub struct Requirement {
    pub kind: &'static str,
    pub text: String,
    pub origin: SourceOrigin,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct SourceText {
    pub path: PathBuf,
    pub text: String,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub message: String,
    pub origin: SourceOrigin,
    pub line: Option<usize>,
    pub obligation: Option<String>,
    /// Source-level claim for presentation; the normalized obligation is retained
    /// separately for tools that need the verifier's internal form.
    pub source_obligation: Option<Box<str>>,
    pub requirement: Option<Box<Requirement>>,
    pub source: Option<Box<SourceText>>,
}

impl Diagnostic {
    pub fn new(message: impl Into<String>) -> Self {
        let message = message.into();
        let line = message
            .strip_prefix("line ")
            .and_then(|tail| tail.split_once(':'))
            .and_then(|(number, _)| number.parse().ok());
        Self {
            message,
            origin: SourceOrigin::Unspecified,
            line,
            obligation: None,
            source_obligation: None,
            requirement: None,
            source: None,
        }
    }

    pub fn with_source(mut self, path: PathBuf, text: String) -> Self {
        self.source = Some(Box::new(SourceText { path, text }));
        self
    }
}

impl From<String> for Diagnostic {
    fn from(message: String) -> Self {
        Self::new(message)
    }
}
impl From<&str> for Diagnostic {
    fn from(message: &str) -> Self {
        Self::new(message)
    }
}
impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(required) = &self.requirement {
            write!(f, "\nrequired: {}", required.text)?;
        }
        if let Some(goal) = self
            .source_obligation
            .as_deref()
            .or(self.obligation.as_deref())
        {
            write!(f, "\nobligation: {goal}")?;
        }
        Ok(())
    }
}
impl std::error::Error for Diagnostic {}

mod render;
pub use render::render;
