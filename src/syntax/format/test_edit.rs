//! Test fixture edits match concrete tokens when formatting changes whitespace.
//! Every edit must match: an unchanged negative fixture must never pass silently.

use super::{concrete, lex};

pub(crate) trait SourceEdit: AsRef<str> {
    fn replace_evg(&self, from: impl ToString, to: &str) -> String {
        self.replacen_evg(from, to, usize::MAX)
    }

    fn replacen_evg(&self, from: impl ToString, to: &str, count: usize) -> String {
        let source = self.as_ref();
        let from = from.to_string();
        assert!(!from.is_empty(), "fixture edit needs a nonempty pattern");
        if source.contains(&from) {
            return source.replacen(&from, to, count);
        }
        let tokens = lex(source).expect("fixture source must tokenize");
        let items = concrete(source, &tokens).unwrap();
        let code: Vec<_> = items.iter().filter(|item| item.code.is_some()).collect();
        let mut pattern = lex(&from).expect("fixture edit must tokenize");
        pattern.pop(); // EOF is not part of the fragment.
        assert!(!pattern.is_empty(), "unmatched fixture comment: {from:?}");
        let (mut result, mut copied, mut index, mut matches) = (String::new(), 0, 0, 0);
        while index + pattern.len() <= code.len() && matches < count {
            let end = index + pattern.len();
            if code[index..end]
                .iter()
                .map(|item| item.text)
                .eq(pattern.iter().map(|t| t.text.as_str()))
            {
                let start_offset = code[index].text.as_ptr() as usize - source.as_ptr() as usize;
                let end_item = code[end - 1].text;
                let end_offset =
                    end_item.as_ptr() as usize - source.as_ptr() as usize + end_item.len();
                result.push_str(&source[copied..start_offset]);
                result.push_str(to);
                copied = end_offset;
                index = end;
                matches += 1;
            } else {
                index += 1;
            }
        }
        assert!(
            matches > 0,
            "fixture edit matched no source tokens: {from:?}"
        );
        result.push_str(&source[copied..]);
        result
    }
}

impl<T: AsRef<str> + ?Sized> SourceEdit for T {}

#[test]
fn edits_match_formatted_fragments_and_never_modify_literal_contents_as_tokens() {
    assert_eq!(
        "let x = 1;\nlet y = 2;".replace_evg("let x=1; let y=2;", "42"),
        "42"
    );
    assert_eq!("fn f() {\n    x\n}".replace_evg("{x}", "{y}"), "fn f() {y}");
    assert_eq!("\"x y\"; x   y".replace_evg("x  y", "z"), "\"x y\"; z");
}

#[test]
#[should_panic(expected = "fixture edit matched no source tokens")]
fn missing_edits_fail_instead_of_leaving_negative_tests_unchanged() {
    "fn main() {42}".replace_evg("not_present", "false");
}
