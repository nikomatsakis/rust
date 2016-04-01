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
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:3 ",
                style: FileNameLine
            },
            StyledString {
                text: "    vec.push(vec.pop().unwrap());",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 2
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    ~~~      ~~~                ~ previous borrow ends here",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    |        |",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    |        error occurs here",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    previous borrow of `vec` occurs here",
                style: Label
            }
        ],
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
        text: [
            StyledString {
                text: "foo.rs:3  ",
                style: FileNameLine
            },
            StyledString {
                text: "    let name = find_id(&data, 22).unwrap();",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 2
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "          ",
                style: NoStyle
            },
            StyledString {
                text: "                        ~~~~ immutable borrow begins here",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:4  ",
                style: FileNameLine
            },
            StyledString {
                text: "",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 3
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:5  ",
                style: FileNameLine
            },
            StyledString {
                text: "    // Add one more item we forgot to the vector. Silly us.",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 4
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:6  ",
                style: FileNameLine
            },
            StyledString {
                text: "    data.push(Data { name: format!(\"Hera\"), id: 66 });",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 5
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "          ",
                style: NoStyle
            },
            StyledString {
                text: "    ~~~~ mutable borrow occurs here",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:7  ",
                style: FileNameLine
            },
            StyledString {
                text: "",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 6
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:8  ",
                style: FileNameLine
            },
            StyledString {
                text: "    // Print everything out.",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 7
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:9  ",
                style: FileNameLine
            },
            StyledString {
                text: "    println!(\"Name: {:?}\", name);",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 8
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:10 ",
                style: FileNameLine
            },
            StyledString {
                text: "    println!(\"Data: {:?}\", data);",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 9
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:11 ",
                style: FileNameLine
            },
            StyledString {
                text: "}",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 10
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "          ",
                style: NoStyle
            },
            StyledString {
                text: "~ immutable borrow ends here",
                style: Label
            }
        ],
        kind: Highlights
    }
]"#);

    let text: String = make_string(&lines);

    println!("text=\n{}", text);
    assert_eq!(&text[..], r#"
foo.rs:3      let name = find_id(&data, 22).unwrap();
                                  ~~~~ immutable borrow begins here
foo.rs:4  
foo.rs:5      // Add one more item we forgot to the vector. Silly us.
foo.rs:6      data.push(Data { name: format!("Hera"), id: 66 });
              ~~~~ mutable borrow occurs here
foo.rs:7  
foo.rs:8      // Print everything out.
foo.rs:9      println!("Name: {:?}", name);
foo.rs:10     println!("Data: {:?}", data);
foo.rs:11 }
          ~ immutable borrow ends here
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
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:3 ",
                style: FileNameLine
            },
            StyledString {
                text: "    vec.push(vec.pop().unwrap());",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 2
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    ~~~~~~~~           ~~~~~~ D",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    ||",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    |C",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    A",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    B",
                style: Label
            }
        ],
        kind: Highlights
    }
]"#);

    let text: String = make_string(&lines);

    println!("text=r#\"\n{}\".trim_left()", text);
    assert_eq!(&text[..], r#"
foo.rs:3     vec.push(vec.pop().unwrap());
             ~~~~~~~~           ~~~~~~ D
             ||
             |C
             A
             B
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
    assert_eq!(format!("\n{:#?}", lines), r#"
[
    RenderedLine {
        text: [
            StyledString {
                text: "foo.rs:3 ",
                style: FileNameLine
            },
            StyledString {
                text: "    vec.push(vec.pop().unwrap());",
                style: Quotation
            }
        ],
        kind: SourceText {
            file: FileMap(foo.rs),
            line_index: 2
        }
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    ~~~      ~~~                ~ previous borrow ends here",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    |        |",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    |        error occurs here",
                style: Label
            }
        ],
        kind: Highlights
    },
    RenderedLine {
        text: [
            StyledString {
                text: "         ",
                style: NoStyle
            },
            StyledString {
                text: "    previous borrow of `vec` occurs here",
                style: Label
            }
        ],
        kind: Highlights
    }
]"#);

    let text: String = make_string(&lines);

    println!("text=r#\"\n{}\".trim_left()", text);
    assert_eq!(&text[..], r#"
foo.rs:3     vec.push(vec.pop().unwrap());
             ~~~      ~~~                ~ previous borrow ends here
             |        |
             |        error occurs here
             previous borrow of `vec` occurs here
"#.trim_left());
}

