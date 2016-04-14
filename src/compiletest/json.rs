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

impl Diagnostic {
    fn flatten(&self) -> Vec<Diagnostic> {
        let mut result = vec![
            Diagnostic {
                message: self.message.clone(),
                code: self.code.clone(),
                level: self.level.clone(),
                spans: self.spans.clone(),
                children: vec![]
            }
        ];

        result.extend(self.children.iter()
                                   .flat_map(|x| x.flatten()));
        result
    }
}

pub fn parse_output(file_name: &str, output: &str) -> Vec<ExpectedError> {
    output.lines()
          .flat_map(|line| parse_line(file_name, line))
          .collect()
}

fn diag_to_expected_errors(diagnostic: Diagnostic, file_name: &str) -> Vec<ExpectedError> {
    diagnostic
        .flatten()
        .iter()
        .flat_map(|diag| diag
            .spans
            .iter()
            .filter(|span| span.file_name == file_name)
            .map(move |span| {
                let msg = match diag.code {
                    Some(ref code) =>
                        format!("{} [{}]", diag.message, code.code.clone()),
                    None =>
                        diag.message.clone(),
                };
                if let Ok(kind) = ErrorKind::from_str(&diag.level) {
                  ExpectedError {
                      line_num: span.line_start,
                      kind: Some(kind),
                      msg: msg,
                  }
                }
                else {
                  ExpectedError {
                      line_num: span.line_start,
                      kind: None,
                      msg: msg,
                  }
                }
            })
        )
        .collect()
}

fn parse_line(file_name: &str, line: &str) -> Vec<ExpectedError> {
    match json::decode::<Diagnostic>(line) {
        Ok(diagnostic) => {
            diag_to_expected_errors(diagnostic, file_name)
        }
        Err(error) => {
            println!("failed to decode compiler output as json: `{}`", error);
            panic!("failed to decode compiler output as json");
        }
    }
}
