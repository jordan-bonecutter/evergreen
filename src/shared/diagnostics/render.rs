//! Source-aware diagnostic rendering shared by CLI and browser hosts.
use super::{Diagnostic, SourceOrigin};
use std::{
    fmt::Write,
    path::{Path, PathBuf},
};

pub fn render(diagnostic: &Diagnostic, files: &[PathBuf], input: &str, color: bool) -> String {
    let red = if color { "\x1b[1;31m" } else { "" };
    let blue = if color { "\x1b[1;34m" } else { "" };
    let bold = if color { "\x1b[1m" } else { "" };
    let reset = if color { "\x1b[0m" } else { "" };
    let primary_source = diagnostic
        .source
        .as_ref()
        .map(|source| (source.path.as_path(), source.text.as_str()))
        .or_else(|| source(diagnostic.origin, files, input));
    let has_line = primary_source
        .zip(diagnostic.line)
        .is_some_and(|((_, text), line)| {
            line.checked_sub(1)
                .and_then(|index| text.lines().nth(index))
                .is_some()
        });
    let message = if has_line {
        diagnostic
            .message
            .strip_prefix("line ")
            .and_then(|tail| tail.split_once(':'))
            .map_or(diagnostic.message.as_str(), |(_, rest)| rest.trim_start())
    } else {
        &diagnostic.message
    };
    let (title, arithmetic_help) =
        match message.split_once(": cannot prove obligation with bounded linear arithmetic") {
            Some((title, _)) => (title, true),
            None => (message, false),
        };
    let mut out = format!("{red}error{reset}{bold}: {}{reset}", readable(title));
    if let (Some((path, text)), Some(line)) = (primary_source, diagnostic.line) {
        if let Some(code) = line
            .checked_sub(1)
            .and_then(|index| text.lines().nth(index))
        {
            let code = visible(code);
            let indent = code.len() - code.trim_start().len();
            let column = code[..indent].chars().count() + 1;
            let width = code.trim_start().chars().count().clamp(1, 160);
            let digits = line.to_string().len();
            let path = display_path(path);
            let _ = write!(out, "\n{blue} --> {path}:{line}:{column}{reset}\n{:digits$} {blue}|{reset}\n{blue}{line:>digits$} |{reset} {code}\n{:digits$} {blue}|{reset} {}{red}{}{reset}", "", "", " ".repeat(column - 1), "^".repeat(width));
        }
    }
    if let Some(requirement) = &diagnostic.requirement {
        let _ = write!(
            out,
            "\n  {blue}={reset} required: {}",
            readable(&requirement.text)
        );
        if let Some((path, _)) = source(requirement.origin, files, input) {
            let _ = write!(
                out,
                "\n  {blue}={reset} {} declared at {}:{}",
                requirement.kind,
                display_path(path),
                requirement.line
            );
        }
    }
    if let Some(goal) = &diagnostic.obligation {
        let _ = write!(
            out,
            "\n  {blue}={reset} unproved obligation: {}",
            readable(goal)
        );
    }
    if arithmetic_help {
        let _ = write!(
            out,
            "\n  {blue}={reset} help: supply stronger facts or an explicit proof"
        );
    }
    out
}

fn source<'a>(
    origin: SourceOrigin,
    files: &'a [PathBuf],
    input: &'a str,
) -> Option<(&'a Path, &'a str)> {
    match origin {
        SourceOrigin::Input(index) => Some((
            files.get(index)?.as_path(),
            input
                .split('\u{1e}')
                .filter(|unit| !unit.trim().is_empty())
                .nth(index)?,
        )),
        SourceOrigin::Bundled(path) => {
            Some((Path::new(path), crate::compiler::bundled_source(path)?))
        }
        SourceOrigin::Unspecified => None,
    }
}

fn display_path(path: &Path) -> String {
    let relative = std::env::current_dir()
        .ok()
        .and_then(|cwd| path.strip_prefix(cwd).ok().map(Path::to_owned));
    visible(&relative.as_deref().unwrap_or(path).to_string_lossy())
}

fn visible(text: &str) -> String {
    let mut out = String::new();
    for character in text.chars().take(240) {
        match character {
            '\t' => out.push_str("    "),
            c if c.is_control() => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    if text.chars().count() > 240 {
        out.push('…');
    }
    out
}

fn readable(text: &str) -> String {
    // Generated instance numbers are compiler identities, not useful type names.
    let mut out = String::new();
    let mut rest = text;
    while let Some(start) = rest.find("evg_generic_") {
        out.push_str(&rest[..start]);
        let tail = &rest[start + "evg_generic_".len()..];
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        if digits > 0 && tail.as_bytes().get(digits) == Some(&b'_') {
            rest = &tail[digits + 1..];
        } else {
            out.push_str("evg_generic_");
            rest = tail;
        }
    }
    out.push_str(rest);
    out.chars()
        .map(|character| {
            if character.is_control() && character != '\n' {
                '?'
            } else {
                character
            }
        })
        .collect()
}
