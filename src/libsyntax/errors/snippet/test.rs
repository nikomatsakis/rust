use codemap::{BytePos, CodeMap, NO_EXPANSION, Span};
use std::rc::Rc;
use super::SnippetData;

/// Returns the span corresponding to the `n`th occurrence of
/// `substring` in `source_text`.
trait CodeMapExtension {
    fn span_substr(&self,
                   source_text: &str,
                   substring: &str,
                   n: usize)
                   -> Span;
}

impl CodeMapExtension for CodeMap {
    fn span_substr(&self,
                   source_text: &str,
                   substring: &str,
                   n: usize)
                   -> Span
    {
        let mut i = 0;
        let mut hi = 0;
        loop {
            let offset = source_text[hi..].find(substring).unwrap_or_else(|| {
                panic!("source_text `{}` does not have {} occurrences of `{}`, only {}",
                       source_text, n, substring, i);
            });
            let lo = hi + offset;
            hi = lo + substring.len();
            if i == n {
                let span = Span {
                    lo: BytePos(lo as u32),
                    hi: BytePos(hi as u32),
                    expn_id: NO_EXPANSION,
                };
                assert_eq!(&self.span_to_snippet(span).unwrap()[..],
                           substring);
                return span;
            }
            i += 1;
        }
    }
}

#[test]
fn test() {
    let file_text = r#"
fn foo() {
    vec.push(vec.pop().unwrap());
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);
    let span_vec0 = cm.span_substr(file_text, "vec", 0);
    let span_vec1 = cm.span_substr(file_text, "vec", 1);
    let span_semi = cm.span_substr(file_text, ";", 0);

    let mut snippet = SnippetData::new(cm);
    snippet.push(span_vec0, Some(format!("previous borrow of `vec` occurs here")));
    snippet.push(span_vec1, Some(format!("error occurs here")));
    snippet.push(span_semi, Some(format!("previous borrow ends here")));

    let lines = snippet.render_lines();
    println!("{:#?}", lines);
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: "    vec.push(vec.pop().unwrap());",
        kind: SourceText
    },
    RenderedLine {
        text: "    ~~~      ~~~                ~ previous borrow ends here",
        kind: Highlights
    },
    RenderedLine {
        text: "    |        |",
        kind: Highlights
    },
    RenderedLine {
        text: "    |        error occurs here",
        kind: Highlights
    },
    RenderedLine {
        text: "    previous borrow of `vec` occurs here",
        kind: Highlights
    }
]"#);
}
