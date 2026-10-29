//! Command syntax and input-file selection.

use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

#[derive(Clone, Copy, ValueEnum)]
pub(super) enum Color {
    Auto,
    Always,
    Never,
}

#[derive(Parser)]
#[command(
    name = "evg",
    version,
    about = "Evergreen proof-oriented language compiler"
)]
pub(super) struct Cli {
    /// Color compiler diagnostics: auto, always, or never.
    #[arg(long, global = true, value_enum, default_value = "auto")]
    pub(super) color: Color,
    /// Reject any use of trustme, including in unused definitions.
    #[arg(long, global = true)]
    pub(super) deny_trust: bool,
    /// Root directory for local package imports (defaults to the working directory).
    #[arg(long, global = true)]
    pub(super) package_root: Option<PathBuf>,
    #[command(subcommand)]
    pub(super) command: Action,
}

#[derive(Subcommand)]
pub(super) enum Action {
    /// Format Evergreen source without running the proof checker.
    Fmt {
        /// Files to format (defaults to all tracked .evg files).
        #[arg(conflicts_with_all = ["all", "staged"])]
        files: Vec<PathBuf>,
        /// Check formatting without rewriting files.
        #[arg(long)]
        check: bool,
        /// Format all tracked .evg files.
        #[arg(long, conflicts_with = "staged")]
        all: bool,
        /// Check staged blobs, including partially staged files.
        #[arg(long, requires = "check")]
        staged: bool,
    },
    /// Emit a verified Linux x86-64 executable or WebAssembly module.
    Build {
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Output path (defaults to the last source path without its extension).
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Replay checked source certificates before native emission.
        #[arg(long)]
        proof: Option<PathBuf>,
        /// Output target. WebAssembly exports main and imports the console host.
        #[arg(long, value_enum, default_value_t = Target::X86_64)]
        target: Target,
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
}

#[derive(Clone, Copy, ValueEnum)]
pub(super) enum Target {
    #[value(name = "x86_64", alias = "x86_64-unknown-linux-gnu")]
    X86_64,
    #[value(name = "wasm32", alias = "wasm32-unknown-unknown", alias = "wasm")]
    Wasm32,
}

impl Action {
    pub(super) fn files(&self) -> &[PathBuf] {
        match self {
            Self::Fmt { files, .. }
            | Self::Check { files, .. }
            | Self::Prove { files, .. }
            | Self::Run { files }
            | Self::Build { files, .. } => files,
        }
    }
}
