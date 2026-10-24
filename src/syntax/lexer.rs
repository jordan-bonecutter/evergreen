//! Source tokenization shared by all compiler frontends.

#[derive(Clone, Debug)]
pub(super) struct Token {
    pub(super) text: String,
    pub(super) line: usize,
}

pub(super) fn lex(source: &str) -> Result<Vec<Token>, String> {
    let mut out = Vec::new();
    let chars: Vec<char> = source.chars().collect();
    let (mut i, mut line) = (0, 1);
    while i < chars.len() {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        if c.is_ascii_alphabetic() || c == '_' {
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
        } else if c.is_ascii_digit() {
            i += 1;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
        } else if "(){}[],:;.+-*/%<>=!&|".contains(c) {
            i += 1;
            if i < chars.len()
                && matches!(
                    (c, chars[i]),
                    ('-', '>')
                        | ('<', '=')
                        | ('>', '=')
                        | ('=', '=')
                        | ('=', '>')
                        | ('!', '=')
                        | ('&', '&')
                        | ('|', '|')
                        | (':', ':')
                )
            {
                i += 1;
            }
        } else {
            return Err(format!("line {line}: unexpected character {c:?}"));
        }
        out.push(Token {
            text: chars[start..i].iter().collect(),
            line,
        });
    }
    out.push(Token {
        text: "<eof>".into(),
        line,
    });
    Ok(out)
}
