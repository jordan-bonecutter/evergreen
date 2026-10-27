//! Decode source strings to UTF-8 bytes. Runtime storage remains an ordinary
//! fixed byte array; there is no compiler-defined runtime string type.

pub(super) fn literal(
    chars: &[char],
    cursor: &mut usize,
    line: &mut usize,
) -> Result<Vec<u8>, String> {
    let opening_line = *line;
    let mut decoded = String::new();
    *cursor += 1;
    while let Some(&next) = chars.get(*cursor) {
        *cursor += 1;
        match next {
            '"' => return Ok(decoded.into_bytes()),
            '\n' => {
                *line += 1;
                decoded.push('\n');
            }
            '\\' => decoded
                .push(escape(chars, cursor).map_err(|error| format!("line {line}: {error}"))?),
            other => decoded.push(other),
        }
    }
    Err(format!("line {opening_line}: unterminated string literal"))
}

fn escape(chars: &[char], cursor: &mut usize) -> Result<char, &'static str> {
    let next = *chars.get(*cursor).ok_or("unterminated string escape")?;
    *cursor += 1;
    Ok(match next {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '0' => '\0',
        '\\' => '\\',
        '"' => '"',
        'x' => {
            let mut byte = 0;
            for _ in 0..2 {
                let digit = chars
                    .get(*cursor)
                    .and_then(|c| c.to_digit(16))
                    .ok_or("byte escape requires two hexadecimal digits")?;
                *cursor += 1;
                byte = byte * 16 + digit;
            }
            if byte > 127 {
                return Err("string byte escapes must be ASCII; use a Unicode scalar escape");
            }
            char::from_u32(byte).ok_or("invalid ASCII escape")?
        }
        'u' => {
            if chars.get(*cursor) != Some(&'{') {
                return Err("Unicode escape requires braces: \\u{...}");
            }
            *cursor += 1;
            let mut value = 0;
            let mut digits = 0;
            while let Some(&c) = chars.get(*cursor) {
                if c == '}' {
                    break;
                }
                if digits == 6 {
                    return Err("Unicode escape exceeds six hexadecimal digits");
                }
                value = value * 16 + c.to_digit(16).ok_or("invalid Unicode escape digit")?;
                digits += 1;
                *cursor += 1;
            }
            if digits == 0 || chars.get(*cursor) != Some(&'}') {
                return Err(
                    "Unicode escape requires one to six hexadecimal digits and a closing brace",
                );
            }
            *cursor += 1;
            char::from_u32(value).ok_or("Unicode escape is not a valid scalar value")?
        }
        _ => return Err("unknown string escape"),
    })
}
