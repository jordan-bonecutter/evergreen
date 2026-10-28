//! Whitespace formatting over concrete tokens. The compiler parser supplies
//! optional layout hints; comments and literal spellings stay in the source.

use super::{lex, parse_unit_with_hints};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Default)]
pub(super) struct Hints {
    pub clauses: BTreeMap<usize, usize>,
    pub bodies: BTreeSet<usize>,
    pub angles: BTreeSet<usize>,
    pub prefix: BTreeSet<usize>,
}

impl super::Parser {
    pub(super) fn note_format_clause(&mut self, start: usize) {
        if self.pos != start {
            if let Some(hints) = &mut self.format_hints {
                hints.clauses.insert(start, self.pos);
            }
        }
    }
}

struct Item<'a> {
    text: &'a str,
    code: Option<usize>,
    blank_before: bool,
    inline_comment: bool,
}

/// Format one source file without verification or importing dependencies.
/// Malformed declarations can still be formatted when they tokenize correctly.
/// A second lexical pass checks that no token or comment was changed or merged.
pub fn source(source: &str) -> Result<String, String> {
    let tokens = lex(source)?;
    let hints = parse_unit_with_hints(source, Some(Hints::default()))
        .ok()
        .and_then(|(_, hints)| hints)
        .unwrap_or_default();
    let items = concrete(source, &tokens)?;
    let formatted = render(&items, &hints);
    let after = lex(&formatted)?;
    if tokens
        .iter()
        .map(|t| (&t.text, &t.bytes))
        .ne(after.iter().map(|t| (&t.text, &t.bytes)))
    {
        return Err("formatter would change the token stream; source left untouched".into());
    }
    let comments = |items: Vec<Item<'_>>| {
        items
            .into_iter()
            .filter(|item| item.code.is_none())
            .map(|item| item.text.to_owned())
            .collect::<Vec<_>>()
    };
    if comments(items) != comments(concrete(&formatted, &after)?) {
        return Err("formatter would change comments; source left untouched".into());
    }
    Ok(formatted)
}

fn concrete<'a>(source: &'a str, tokens: &[super::Token]) -> Result<Vec<Item<'a>>, String> {
    let mut items = Vec::new();
    let mut offset = 0;
    for (index, token) in tokens.iter().enumerate() {
        loop {
            let rest = &source[offset..];
            let whitespace = rest.len() - rest.trim_start_matches(char::is_whitespace).len();
            let gap = &rest[..whitespace];
            offset += whitespace;
            if source[offset..].starts_with("//") {
                let end = source[offset..]
                    .find('\n')
                    .map_or(source.len(), |n| offset + n);
                items.push(Item {
                    text: source[offset..end].trim_end_matches('\r'),
                    code: None,
                    blank_before: gap.bytes().filter(|b| *b == b'\n').count() > 1,
                    inline_comment: !items.is_empty() && !gap.contains('\n'),
                });
                offset = end;
                continue;
            }
            if token.text == "<eof>" {
                return Ok(items);
            }
            if !source[offset..].starts_with(&token.text) {
                return Err("formatter could not locate a source token".into());
            }
            let end = offset + token.text.len();
            items.push(Item {
                text: &source[offset..end],
                code: Some(index),
                blank_before: gap.bytes().filter(|b| *b == b'\n').count() > 1,
                inline_comment: false,
            });
            offset = end;
            break;
        }
    }
    Ok(items)
}

#[derive(Default)]
struct Writer {
    output: String,
    line: String,
}

impl Writer {
    fn word(&mut self, text: &str, indent: usize, space: bool) {
        if self.line.is_empty() {
            self.line.push_str(&"    ".repeat(indent));
        } else if space && !self.line.ends_with(' ') {
            self.line.push(' ');
        }
        self.line.push_str(text);
    }
    fn newline(&mut self) {
        if !self.line.is_empty() {
            self.output.push_str(&self.line);
            self.output.push('\n');
            self.line.clear();
        }
    }
    fn blank(&mut self) {
        self.newline();
        if !self.output.is_empty() && !self.output.ends_with("\n\n") {
            self.output.push('\n');
        }
    }
    fn finish(mut self) -> String {
        self.newline();
        while self.output.ends_with("\n\n") {
            self.output.pop();
        }
        self.output
    }
}

struct Group {
    close: &'static str,
    multiline: bool,
    indent: usize,
}

#[derive(Clone, Copy, Default)]
struct Metrics {
    width: usize,
    comments: usize,
    semicolons: usize,
    braces: usize,
    declarations: usize,
    commas: usize,
}

fn groups(items: &[Item<'_>], hints: &Hints) -> BTreeMap<usize, (usize, bool)> {
    // Prefix totals avoid repeated scans of nested token ranges;
    // even syntax rejected by the parser never rescans each enclosing group.
    let mut totals = vec![Metrics::default()];
    for item in items {
        let mut total = *totals.last().unwrap();
        total.width += item.text.len() + 1;
        total.comments += usize::from(item.code.is_none());
        total.semicolons += usize::from(item.text == ";");
        total.braces += usize::from(item.text == "{");
        total.declarations += usize::from(matches!(item.text, "fn" | "method"));
        total.commas += usize::from(item.text == ",");
        totals.push(total);
    }
    let mut stack = Vec::new();
    let mut groups = BTreeMap::new();
    for (i, item) in items.iter().enumerate() {
        let angle = item.code.is_some_and(|code| hints.angles.contains(&code));
        if matches!(item.text, "(" | "[" | "{") || (item.text == "<" && angle) {
            stack.push((i, item.text));
        } else if matches!(item.text, ")" | "]" | "}") || (item.text == ">" && angle) {
            let Some(&(start, open)) = stack.last() else {
                continue;
            };
            if closing(open) != item.text {
                continue;
            }
            stack.pop();
            let before = totals[start + 1];
            let after = totals[i];
            let body = items[start]
                .code
                .is_some_and(|code| hints.bodies.contains(&code));
            let multiline = i > start + 1
                && (body
                    || after.comments > before.comments
                    || (open == "{"
                        && (after.semicolons > before.semicolons
                            || after.braces > before.braces
                            || after.declarations > before.declarations))
                    || (open == "(" && after.semicolons > before.semicolons)
                    || (after.width - before.width > 88
                        && (open == "{" || after.commas > before.commas)));
            groups.insert(start, (i, multiline));
        }
    }
    groups
}

fn closing(open: &str) -> &'static str {
    match open {
        "(" => ")",
        "[" => "]",
        "{" => "}",
        "<" => ">",
        _ => "",
    }
}

fn render(items: &[Item<'_>], hints: &Hints) -> String {
    let groups = groups(items, hints);
    let mut stack: Vec<Group> = Vec::new();
    let mut writer = Writer::default();
    let mut indent = 0;
    let mut clause = None;
    let mut previous = "";
    let mut previous_prefix = false;
    let mut previous_angle = false;
    for (i, item) in items.iter().enumerate() {
        let text = item.text;
        let next_item = items.get(i + 1);
        let next = next_item.map_or("", |item| item.text);
        let trailing_comment = next_item.is_some_and(|item| item.inline_comment);
        if item.code.is_none() {
            if !item.inline_comment {
                writer.newline();
            }
            if item.blank_before {
                writer.blank();
            }
            writer.word(text, indent, item.inline_comment);
            writer.newline();
            continue;
        }
        let code = item.code.unwrap();
        if let Some((end, base)) = clause {
            if code == end {
                indent = base;
                clause = None;
                writer.newline();
            }
        }
        if let Some(&end) = hints.clauses.get(&code) {
            let base = indent;
            writer.newline();
            writer.word(text, base + 1, false);
            indent = base + 2;
            clause = Some((end, base));
            if matches!(text, "where" | "ensures" | "invariant") {
                writer.newline();
            }
            previous = text;
            previous_prefix = false;
            previous_angle = false;
            continue;
        }
        if item.blank_before && writer.line.is_empty() {
            writer.blank();
        }
        let angle = hints.angles.contains(&code);
        let prefix = hints.prefix.contains(&code)
            || (matches!(text, "&" | "!" | "*") && !ends_expression(previous));
        let space = needs_space(previous, text, previous_prefix, angle, previous_angle);
        if let Some(&(_, multiline)) = groups.get(&i) {
            // Contract bodies start after the final clause; ordinary function
            // bodies share their signature line.
            writer.word(text, indent, space);
            stack.push(Group {
                close: closing(text),
                multiline,
                indent,
            });
            if multiline {
                indent += 1;
                writer.newline();
            }
        } else if stack.last().is_some_and(|group| group.close == text) {
            let group = stack.pop().unwrap();
            if group.multiline {
                writer.newline();
                indent = group.indent;
            }
            writer.word(text, indent, false);
            let declaration_follows = matches!(
                next,
                "fn" | "method" | "type" | "opaque" | "ideal" | "impl" | "module" | "import"
            );
            if text == "}"
                && !trailing_comment
                && (declaration_follows
                    || (group.multiline
                        && !matches!(
                            next,
                            ";" | "," | ")" | "]" | "." | "::" | "else" | "where" | "proof"
                        )))
            {
                writer.newline();
            }
        } else {
            writer.word(text, indent, space);
            let break_line = (text == ";" && !matches!(stack.last().map(|g| g.close), Some("]")))
                || (text == "," && stack.last().is_some_and(|g| g.multiline))
                || (text == "&&" && clause.is_some());
            if break_line && !trailing_comment {
                writer.newline();
            }
        }
        previous = text;
        previous_prefix = prefix;
        previous_angle = angle;
    }
    writer.finish()
}

fn ends_expression(text: &str) -> bool {
    text.ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_')
        || matches!(text, ")" | "]" | "}")
}

fn needs_space(
    previous: &str,
    text: &str,
    previous_prefix: bool,
    angle: bool,
    previous_angle: bool,
) -> bool {
    if previous.is_empty() {
        return false;
    }
    // Keep distinct tokens distinct (especially two nested reference operators).
    if matches!(
        (previous, text),
        ("&", "&")
            | ("|", "|")
            | ("<", "=")
            | (">", "=")
            | ("!", "=")
            | ("=", "=")
            | ("=", ">")
            | ("-", ">")
            | (":", ":")
            | ("/", "/")
    ) {
        return true;
    }
    if matches!(text, ")" | "]" | "}" | "," | ";" | "." | "::" | ":")
        || matches!(previous, "(" | "[" | "{" | "." | "::")
    {
        return false;
    }
    if (angle && matches!(text, "<" | ">")) || (previous_angle && previous == "<") {
        return false;
    }
    if previous_prefix {
        return false;
    }
    if text == "(" {
        return matches!(
            previous,
            "if" | "while" | "match" | "where" | "ensures" | "invariant" | "return"
        ) || !(ends_expression(previous) || (previous_angle && previous == ">"));
    }
    if text == "[" {
        return !ends_expression(previous);
    }
    if text == "&" && previous == "method" {
        return false;
    }
    true
}

#[cfg(test)]
mod tests;

#[cfg(test)]
pub(crate) mod test_edit;
