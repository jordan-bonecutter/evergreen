//! Command syntax and input-file selection.

use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "evg",
    version,
    about = "Evergreen proof-oriented language compiler"
)]
pub(super) struct Cli {
    /// Reject any use of trustme, including in unused definitions.
    #[arg(long, global = true)]
    pub(super) deny_trust: bool,
    #[command(subcommand)]
    pub(super) command: Action,
}

#[derive(Subcommand)]
pub(super) enum Action {
    /// Emit a verified scalar Linux x86-64 executable.
    Build {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        #[arg(short, long)]
        output: PathBuf,
        /// Replay checked source certificates before native emission.
        #[arg(long)]
        proof: Option<PathBuf>,
    },
    /// Verify a program with the internal proof kernel.
    Check {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Replay this proof artifact without invoking proof search.
        #[arg(long)]
        proof: Option<PathBuf>,
    },
    /// Verify source and save a portable, checked proof artifact.
    Prove {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        #[arg(short, long)]
        output: PathBuf,
    },
    /// Verify and evaluate main with bounded execution.
    Run {
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },
    /// Emit Lean source for the reference backend (does not verify).
    Emit {
        file: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Verify with the optional pinned Lean toolchain.
    LeanCheck { file: PathBuf },
    /// Evaluate the ideal reference model using the optional Lean toolchain.
    LeanRun { file: PathBuf },
}

impl Action {
    pub(super) fn files(&self) -> &[PathBuf] {
        match self {
            Self::Check { files, .. }
            | Self::Prove { files, .. }
            | Self::Run { files }
            | Self::Build { files, .. } => files,
            Self::Emit { file, .. } | Self::LeanCheck { file } | Self::LeanRun { file } => {
                std::slice::from_ref(file)
            }
        }
    }
}
