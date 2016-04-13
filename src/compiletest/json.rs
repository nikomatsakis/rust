use errors::ExpectedError;
use rustc_serialize::json;
use syntax::errors::json::Diagnostic;

// These structs are a subset of the ones found in
// `syntax::errors::json`.

#[derive(RustcEncodable)]
struct Diagnostic<'a> {
    message: String,
    code: Option<DiagnosticCode>,
    level: String,
    spans: Vec<DiagnosticSpan>,
}

#[derive(RustcEncodable)]
struct DiagnosticSpan {
    file_name: String,
    line_start: usize,
    line_end: usize,
}

#[derive(RustcEncodable)]
struct DiagnosticCode {
    /// The code itself.
    code: String,
    /// An explanation for the code.
    explanation: Option<&'static str>,
}

pub fn parse_output(file_name: &str, output: &str) -> Vec<ExpectedError> {
    output.lines()
          .flat_map(|line| parse_line(line))
          .collect()
}

fn parse_line(file_name: &str, line: &str) -> Vec<ExpectedError> {
    match json::decode::<Diagnostic>(line) {
        Ok(diagnostic) => {
            diagnostic.spans
                      .iter()
                      .filter(|span| span.file_name == file_name)
                      .map(|span| {
                          let msg = match diagnostic.code {
                              Some(code) =>
                                  format!("{} [{}]", diagnostic.message, code.code),
                              None =>
                                  diagnostic.message.clone(),
                          };

                          ExpectedError {
                              line_num: span.line_start,
                              kind: ErrorKind::from_str(&diagnostic.level),
                              msg: msg,
                          }
                      })
                      .collect()
        }
        Err(error) => {
            println!("failed to decode compiler output as json: `{}`", error);
            println!("output is:");
            println!("{}", s);
            panic!("failed to decode compiler output as json");
        }
    }
}
