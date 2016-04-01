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
fn one_line() {
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

#[test]
fn multi_line() {
    let file_text = r#"
fn foo() {
    let name = find_id(&data, 22).unwrap();

    // Add one more item we forgot to the vector. Silly us.
    data.push(Data { name: format!("Hera"), id: 66 });

    // Print everything out.
    println!("Name: {:?}", name);
    println!("Data: {:?}", data);
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);
    let span_data0 = cm.span_substr(file_text, "data", 0);
    let span_data1 = cm.span_substr(file_text, "data", 1);
    let span_rbrace = cm.span_substr(file_text, "}", 3);

    let mut snippet = SnippetData::new(cm);
    snippet.push(span_data0, Some(format!("immutable borrow begins here")));
    snippet.push(span_data1, Some(format!("mutable borrow occurs here")));
    snippet.push(span_rbrace, Some(format!("immutable borrow ends here")));

    let lines = snippet.render_lines();
    println!("{:#?}", lines);
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: "    let name = find_id(&data, 22).unwrap();",
        kind: SourceText
    },
    RenderedLine {
        text: "                        ~~~~ immutable borrow begins here",
        kind: Highlights
    },
    RenderedLine {
        text: "...",
        kind: Elision
    },
    RenderedLine {
        text: "    data.push(Data { name: format!(\"Hera\"), id: 66 });",
        kind: SourceText
    },
    RenderedLine {
        text: "    ~~~~ mutable borrow occurs here",
        kind: Highlights
    },
    RenderedLine {
        text: "...",
        kind: Elision
    },
    RenderedLine {
        text: "}",
        kind: SourceText
    },
    RenderedLine {
        text: "~ immutable borrow ends here",
        kind: Highlights
    }
]"#);
}

#[test]
fn overlapping() {
    let file_text = r#"
fn foo() {
    vec.push(vec.pop().unwrap());
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);
    let span0 = cm.span_substr(file_text, "vec.push", 0);
    let span1 = cm.span_substr(file_text, "vec", 0);
    let span2 = cm.span_substr(file_text, "ec.push", 0);
    let span3 = cm.span_substr(file_text, "unwrap", 0);

    let mut snippet = SnippetData::new(cm);
    snippet.push(span0, Some(format!("A")));
    snippet.push(span1, Some(format!("B")));
    snippet.push(span2, Some(format!("C")));
    snippet.push(span3, Some(format!("D")));

    let lines = snippet.render_lines();
    println!("{:#?}", lines);
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: "    vec.push(vec.pop().unwrap());",
        kind: SourceText
    },
    RenderedLine {
        text: "    ~~~~~~~~           ~~~~~~ D",
        kind: Highlights
    },
    RenderedLine {
        text: "    ||",
        kind: Highlights
    },
    RenderedLine {
        text: "    |C",
        kind: Highlights
    },
    RenderedLine {
        text: "    A",
        kind: Highlights
    },
    RenderedLine {
        text: "    B",
        kind: Highlights
    }
]"#);
}

#[test]
fn one_line_out_of_order() {
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

    // intentionally don't push the snippets left to right
    let mut snippet = SnippetData::new(cm);
    snippet.push(span_vec1, Some(format!("error occurs here")));
    snippet.push(span_vec0, Some(format!("previous borrow of `vec` occurs here")));
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

#[test]
fn elide_unnecessary_lines() {
    let file_text = r#"
fn foo() {
    let mut vec = vec![0, 1, 2];
    let mut vec2 = vec;
    vec2.push(3);
    vec2.push(4);
    vec2.push(5);
    vec2.push(6);
    vec.push(7);
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);
    let span_vec0 = cm.span_substr(file_text, "vec", 3);
    let span_vec1 = cm.span_substr(file_text, "vec", 8);

    let mut snippet = SnippetData::new(cm);
    snippet.push(span_vec0, Some(format!("`vec` moved here because it has type `collections::vec::Vec<i32>`, which is moved by default")));
    snippet.push(span_vec1, Some(format!("use of moved value: `vec`")));

    let lines = snippet.render_lines();
    println!("{:#?}", lines);
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: "    let mut vec2 = vec;",
        kind: SourceText
    },
    RenderedLine {
        text: "                   ~~~ `vec` moved here because it has type `collections::vec::Vec<i32>`, which is moved by default",
        kind: Highlights
    },
    RenderedLine {
        text: "...",
        kind: Elision
    },
    RenderedLine {
        text: "    vec.push(7);",
        kind: SourceText
    },
    RenderedLine {
        text: "    ~~~ use of moved value: `vec`",
        kind: Highlights
    }
]"#);
}