use errors::{ErrorKind, ExpectedError};
use rustc_serialize::json;
use std::str::FromStr;

// These structs are a subset of the ones found in
// `syntax::errors::json`.

#[derive(RustcEncodable, RustcDecodable)]
struct Diagnostic {
    message: String,
    code: Option<DiagnosticCode>,
    level: String,
    spans: Vec<DiagnosticSpan>,
    children: Vec<Diagnostic>,
}

#[derive(RustcEncodable, RustcDecodable, Clone)]
struct DiagnosticSpan {
    file_name: String,
    line_start: usize,
    line_end: usize,
}

#[derive(RustcEncodable, RustcDecodable, Clone)]
struct DiagnosticCode {
    /// The code itself.
    code: String,
    /// An explanation for the code.
    explanation: Option<String>,
}

pub fn parse_output(file_name: &str, output: &str) -> Vec<ExpectedError> {
    output.lines()
          .flat_map(|line| parse_line(file_name, line))
          .collect()
}

fn parse_line(file_name: &str, line: &str) -> Vec<ExpectedError> {
    match json::decode::<Diagnostic>(line) {
        Ok(diagnostic) => {
            let mut expected_errors = vec![];
            push_expected_errors(&mut expected_errors, &diagnostic, file_name);
            expected_errors
        }
        Err(error) => {
            println!("failed to decode compiler output as json: `{}`", error);
            panic!("failed to decode compiler output as json");
        }
    }
}

fn push_expected_errors(expected_errors: &mut Vec<ExpectedError>,
                        diagnostic: &Diagnostic,
                        file_name: &str) {
    // We only consider messages pertaining to the current file.
    let matching_spans =
        || diagnostic.spans.iter().filter(|span| span.file_name == file_name);
    let with_code =
        |text| match diagnostic.code {
            Some(ref code) =>
                format!("{} [{}]", text, code.code.clone()),
            None =>
                String::from(text),
        };

    // Convert multi-line messages into multiple expected
    // errors. We expect to replace these with something
    // more structured shortly anyhow.
    let mut message_lines = diagnostic.message.lines();
    if let Some(first_line) = message_lines.next() {
        for span in matching_spans() {
            let msg = with_code(first_line);
            let kind = ErrorKind::from_str(&diagnostic.level).ok();
            expected_errors.push(
                ExpectedError {
                    line_num: span.line_start,
                    kind: kind,
                    msg: msg,
                }
            );
        }
    }
    for next_line in message_lines {
        for span in matching_spans() {
            expected_errors.push(
                ExpectedError {
                    line_num: span.line_start,
                    kind: None,
                    msg: with_code(next_line),
                }
            );
        }
    }

    // Flatten out the children.
    for child in &diagnostic.children {
        push_expected_errors(expected_errors, child, file_name);
    }
}

