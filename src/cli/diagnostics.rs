//! Terminal color selection for the shared source-aware diagnostic renderer.
use super::args::Color;
use evergreen::shared::diagnostics::Diagnostic;
use std::{io::IsTerminal, path::PathBuf};

pub(super) fn render(
    diagnostic: &Diagnostic,
    files: &[PathBuf],
    input: &str,
    color: Color,
) -> String {
    let color = match color {
        Color::Always => true,
        Color::Never => false,
        Color::Auto => std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none(),
    };
    evergreen::shared::diagnostics::render(diagnostic, files, input, color)
}
