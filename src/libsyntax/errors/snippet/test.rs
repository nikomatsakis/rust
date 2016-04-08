// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Code for testing annotated snippets.

use codemap::{BytePos, CodeMap, NO_EXPANSION, Span};
use std::rc::Rc;
use super::{RenderedLine, SnippetData};

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

fn splice(start: Span, end: Span) -> Span {
    Span {
        lo: start.lo,
        hi: end.hi,
        expn_id: NO_EXPANSION,
    }
}

fn make_string(lines: &[RenderedLine]) -> String {
    lines.iter()
         .flat_map(|rl| {
             rl.text.iter()
                    .map(|s| &s.text[..])
                    .chain(Some("\n"))
         })
         .collect()
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

    let text: String = make_string(&lines);

    println!("text=\n{}", text);
    assert_eq!(&text[..], r#"
3 |>     vec.push(vec.pop().unwrap());
  |>     ~~~      ~~~                ~ previous borrow ends here
  |>     |        |
  |>     |        error occurs here
  |>     previous borrow of `vec` occurs here
"#.trim_left());
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

    let text: String = make_string(&lines);

    println!("text=\n{}", text);
    assert_eq!(&text[..], r#"
3   |>     let name = find_id(&data, 22).unwrap();
    |>                         ~~~~ immutable borrow begins here
...
6   |>     data.push(Data { name: format!("Hera"), id: 66 });
    |>     ~~~~ mutable borrow occurs here
...
11  |> }
    |> ~ immutable borrow ends here
"#.trim_left());
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
    let text: String = make_string(&lines);

    println!("text=r#\"\n{}\".trim_left()", text);
    assert_eq!(&text[..], r#"
3 |>     vec.push(vec.pop().unwrap());
  |>     ~~~~~~~~           ~~~~~~ D
  |>     ||
  |>     |C
  |>     A
  |>     B
"#.trim_left());
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
    let text: String = make_string(&lines);

    println!("text=r#\"\n{}\".trim_left()", text);
    assert_eq!(&text[..], r#"
3 |>     vec.push(vec.pop().unwrap());
  |>     ~~~      ~~~                ~ previous borrow ends here
  |>     |        |
  |>     |        error occurs here
  |>     previous borrow of `vec` occurs here
"#.trim_left());
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
    snippet.push(span_vec0, Some(format!("`vec` moved here because it \
        has type `collections::vec::Vec<i32>`, which is moved by default")));
    snippet.push(span_vec1, Some(format!("use of moved value: `vec`")));

    let lines = snippet.render_lines();
    println!("{:#?}", lines);
    let text: String = make_string(&lines);
    println!("text=r#\"\n{}\".trim_left()", text);
    assert_eq!(&text[..], r#"
4   |>     let mut vec2 = vec;
    |>                    ~~~ `vec` moved here because it has type `collections::vec::Vec<i32>`, which is moved by default
...
9   |>     vec.push(7);
    |>     ~~~ use of moved value: `vec`
"#.trim_left());
}

#[test]
fn spans_without_labels() {
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

    let mut snippet = SnippetData::new(cm.clone());
    for i in 0..4 {
        let span_veci = cm.span_substr(file_text, "vec", i);
        snippet.push(span_veci, None);
    }

    let lines = snippet.render_lines();
    let text: String = make_string(&lines);
    println!("text=r#\"\n{}\n\"#.trim_left()", text);
    assert_eq!(text, r#"
3 |>     let mut vec = vec![0, 1, 2];
  |>             ~~~   ~~~
4 |>     let mut vec2 = vec;
  |>             ~~~    ~~~
"#.trim_left());
}

#[test]
fn span_long_selection() {
    let file_text = r#"
impl SomeTrait for () {
    fn foo(x: u32) {
        // impl 1
        // impl 2
        // impl 3
    }
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);

    let mut snippet = SnippetData::new(cm.clone());
    let fn_span = cm.span_substr(file_text, "fn", 0);
    let rbrace_span = cm.span_substr(file_text, "}", 0);
    snippet.push(splice(fn_span, rbrace_span), None);
    let lines = snippet.render_lines();
    let text: String = make_string(&lines);
    println!("r#\"\n{}\"", text);
    assert_eq!(text, r#"
3   |>     fn foo(x: u32) {
    |>     ~~~~~~~~~~~~~~~~
...
"#.trim_left());
}

#[test]
fn span_overlap_label() {
    // Test that we don't put `x_span` to the right of its highlight,
    // since there is another highlight that overlaps it.

    let file_text = r#"
    fn foo(x: u32) {
    }
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);

    let mut snippet = SnippetData::new(cm.clone());
    let fn_span = cm.span_substr(file_text, "fn foo(x: u32)", 0);
    let x_span = cm.span_substr(file_text, "x", 0);
    snippet.push(fn_span, Some(format!("fn_span")));
    snippet.push(x_span, Some(format!("x_span")));
    let lines = snippet.render_lines();
    let text: String = make_string(&lines);
    println!("r#\"\n{}\"", text);
    assert_eq!(text, r#"
2 |>     fn foo(x: u32) {
  |>     ~~~~~~~~~~~~~~
  |>     |      |
  |>     |      x_span
  |>     fn_span
"#.trim_left());
}

#[test]
fn span_overlap_label2() {
    // Test that we don't put `x_span` to the right of its highlight,
    // since there is another highlight that overlaps it. In this
    // case, the overlap is only at the beginning, but it's still
    // better to show the beginning more clearly.

    let file_text = r#"
    fn foo(x: u32) {
    }
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);

    let mut snippet = SnippetData::new(cm.clone());
    let fn_span = cm.span_substr(file_text, "fn foo(x", 0);
    let x_span = cm.span_substr(file_text, "x: u32)", 0);
    snippet.push(fn_span, Some(format!("fn_span")));
    snippet.push(x_span, Some(format!("x_span")));
    let lines = snippet.render_lines();
    let text: String = make_string(&lines);
    println!("r#\"\n{}\"", text);
    assert_eq!(text, r#"
2 |>     fn foo(x: u32) {
  |>     ~~~~~~~~~~~~~~
  |>     |      |
  |>     |      x_span
  |>     fn_span
"#.trim_left());
}

#[test]
fn span_overlap_label3() {
    // Test that we don't put `x_span` to the right of its highlight,
    // since there is another highlight that overlaps it. In this
    // case, the overlap is only at the beginning, but it's still
    // better to show the beginning more clearly.

    let file_text = r#"
    fn foo() {
       let closure = || {
           inner
       };
    }
}
"#;

    let cm = Rc::new(CodeMap::new());
    cm.new_filemap_and_lines("foo.rs", file_text);

    let mut snippet = SnippetData::new(cm.clone());

    let closure_span = {
        let closure_start_span = cm.span_substr(file_text, "||", 0);
        let closure_end_span = cm.span_substr(file_text, "}", 0);
        splice(closure_start_span, closure_end_span)
    };

    let inner_span = cm.span_substr(file_text, "inner", 0);

    snippet.push(closure_span, Some(format!("foo")));
    snippet.push(inner_span, Some(format!("bar")));

    let lines = snippet.render_lines();
    let text: String = make_string(&lines);
    println!("r#\"\n{}\"", text);
    assert_eq!(text, r#"
3 |>        let closure = || {
  |>                      ~~~~ foo
4 |>            inner
  |> ~~~~~~~~~~~~~~~~
  |>            |
  |>            bar
5 |>        };
  |> ~~~~~~~~
"#.trim_left());
}
