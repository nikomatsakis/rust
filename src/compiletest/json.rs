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
}

#[derive(RustcEncodable, RustcDecodable)]
struct DiagnosticSpan {
    file_name: String,
    line_start: usize,
    line_end: usize,
}

#[derive(RustcEncodable, RustcDecodable)]
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
            diagnostic
                .spans
                .iter()
                .filter(|span| span.file_name == file_name)
                .map(|span| {
                    let msg = match diagnostic.code {
                        Some(ref code) =>
                            format!("{} [{}]", diagnostic.message, code.code.clone()),
                        None =>
                            diagnostic.message.clone(),
                    };
                    if let Ok(kind) = ErrorKind::from_str(&diagnostic.level) {
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
                .collect()
        }
        Err(error) => {
            println!("failed to decode compiler output as json: `{}`", error);
            panic!("failed to decode compiler output as json");
        }
    }
}
