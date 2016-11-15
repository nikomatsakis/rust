use codemap::CodeMap;
use errors::Handler;
use errors::emitter::EmitterWriter;
use std::io;
use std::io::prelude::*;
use std::rc::Rc;
use std::str;
use std::sync::{Arc, Mutex};
use syntax_pos::{BytePos, NO_EXPANSION, Span, MultiSpan};

/// Identify a position in the text by the Nth occurrence of a string.
struct Position {
    string: &'static str,
    count: usize,
}

struct SpanLabel {
    start: Position,
    end: Position,
    label: &'static str,
}

struct Shared<T: Write> {
    data: Arc<Mutex<T>>,
}

impl<T: Write> Write for Shared<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.data.lock().unwrap().write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.data.lock().unwrap().flush()
    }
}

fn test_harness(file_text: &str, span_labels: Vec<SpanLabel>, expected_output: &str) {
    let output = Arc::new(Mutex::new(Vec::new()));

    let code_map = Rc::new(CodeMap::new());
    code_map.new_filemap_and_lines("test.rs", None, &file_text);

    let primary_span = make_span(&file_text, &span_labels[0].start, &span_labels[0].end);
    let mut msp = MultiSpan::from_span(primary_span);
    for span_label in span_labels {
        let span = make_span(&file_text, &span_label.start, &span_label.end);
        msp.push_span_label(span, span_label.label.to_string());
        println!("span: {:?} label: {:?}", span, span_label.label);
        println!("text: {:?}", code_map.span_to_snippet(span));
    }

    let emitter = EmitterWriter::new(Box::new(Shared { data: output.clone() }),
                                     Some(code_map.clone()));
    let handler = Handler::with_emitter(true, false, Box::new(emitter));
    handler.span_err(msp, "foo");

    assert!(expected_output.chars().next() == Some('\n'),
            "expected output should begin with newline");
    let expected_output = &expected_output[1..];

    let bytes = output.lock().unwrap();
    let actual_output = str::from_utf8(&bytes).unwrap();
    println!("expected output:\n------\n{}------", expected_output);
    println!("actual output:\n------\n{}------", actual_output);

    assert!(expected_output == actual_output)
}

fn make_span(file_text: &str, start: &Position, end: &Position) -> Span {
    let start = make_pos(file_text, start);
    let end = make_pos(file_text, end) + end.string.len(); // just after matching thing ends
    assert!(start <= end);
    Span {
        lo: BytePos(start as u32),
        hi: BytePos(end as u32),
        expn_id: NO_EXPANSION,
    }
}

fn make_pos(file_text: &str, pos: &Position) -> usize {
    let mut remainder = file_text;
    let mut offset = 0;
    for _ in 0..pos.count {
        if let Some(n) = remainder.find(&pos.string) {
            offset += n;
            remainder = &remainder[n + 1..];
        } else {
            panic!("failed to find {} instances of {:?} in {:?}",
                   pos.count,
                   pos.string,
                   file_text);
        }
    }
    offset
}

#[test]
fn ends_on_col0() {
    test_harness(r#"
fn foo() {
}
"#,
                 vec![SpanLabel {
                          start: Position {
                              string: "{",
                              count: 1,
                          },
                          end: Position {
                              string: "}",
                              count: 1,
                          },
                          label: "test",
                      }],
                 r#"
error: foo
 --> test.rs:2:10
  |
2 |   fn foo() {
  |  __________^ starting here...
3 | | }
  | |_^ ...ending here: test

"#);
}

#[test]
fn non_nested() {
    test_harness(r#"
fn foo() {
  X0 Y0
  X1 Y1
}
"#,
                 vec![SpanLabel {
                          start: Position {
                              string: "X0",
                              count: 1,
                          },
                          end: Position {
                              string: "X1",
                              count: 1,
                          },
                          label: "`X` is a good letter",
                 },
                      SpanLabel {
                          start: Position {
                              string: "Y0",
                              count: 1,
                          },
                          end: Position {
                              string: "Y1",
                              count: 1,
                          },
                          label: "`Y` is a good letter too",
                 },
                 ],
                 r#"
error: foo
 --> test.rs:3:3
  |
3 |      X0 Y0
  |  _______- starting here...
  |      |
  |      starting here...
4 | ||   X1 Y1
  | |________- ...ending here: `Y` is a good letter too
  |       |
  |       ...ending here: `X` is a good letter

"#);
}

#[test]
fn nested() {
    test_harness(r#"
fn foo() {
  X0 Y0
  Y1 X1
}
"#,
                 vec![SpanLabel {
                          start: Position {
                              string: "X0",
                              count: 1,
                          },
                          end: Position {
                              string: "X1",
                              count: 1,
                          },
                          label: "`X` is a good letter",
                 },
                      SpanLabel {
                          start: Position {
                              string: "Y0",
                              count: 1,
                          },
                          end: Position {
                              string: "Y1",
                              count: 1,
                          },
                          label: "`Y` is a good letter too",
                 },
                 ],
                 r#"
error: foo
 --> test.rs:3:3
  |
3 |      X0 Y0
  |  _______- starting here...
  |      |
  |      starting here...
4 | ||   Y1 X1
  | ||_______^ ...ending here: `X` is a good letter
  |       |
  |       ...ending here: `Y` is a good letter too

"#);
}
