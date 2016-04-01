// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Code for annotating snippets.

#![allow(dead_code)] // TODO

use codemap::{CodeMap, FileMap, Span};
use std::iter;
use std::rc::Rc;
use std::mem;

#[cfg(test)]
mod test;

pub struct SnippetData {
    codemap: Rc<CodeMap>,
    lines: Vec<Line>,
}

struct Line {
    file: Rc<FileMap>,
    line_index: usize,
    annotations: Vec<Annotation>,
}

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq)]
struct Annotation {
    /// Start column, 0-based indexing. Note that it is important that
    /// this field goes first, so that when we sort, we sort orderings
    /// by start column.
    start_col: usize,

    /// End column within the line.
    end_col: usize,

    /// Optional label to display adjacent to the annotation.
    label: Option<String>,
}

#[derive(Debug)]
pub struct RenderedLine {
    text: String,
    kind: RenderedLineKind,
}

#[derive(Debug)]
pub enum RenderedLineKind {
    SourceText,
    Highlights,
    Elision,
}
use self::RenderedLineKind::*;

impl SnippetData {
    pub fn new(codemap: Rc<CodeMap>) -> Self {
        SnippetData {
            codemap: codemap,
            lines: vec![],
        }
    }

    pub fn push(&mut self, span: Span, label: Option<String>) {
        let file_lines = match self.codemap.span_to_lines(span) {
            Ok(file_lines) => file_lines,
            Err(_) => {
                // ignore unprintable spans completely.
                return;
            }
        };

        assert!(file_lines.lines.len() > 0);

        // If a span covers multiple lines, just put the label on the
        // first one. This is a sort of arbitrary choice and not
        // obviously correct.
        let (line0, remaining_lines) = file_lines.lines.split_first().unwrap();
        let index = self.ensure_source_line(&file_lines.file, line0.line_index);
        self.lines[index].annotations.push(Annotation {
            start_col: line0.start_col.0,
            end_col: line0.end_col.0,
            label: label,
        });
        for line in remaining_lines {
            let index = self.ensure_source_line(&file_lines.file, line.line_index);
            self.lines[index].annotations.push(Annotation {
                start_col: line0.start_col.0,
                end_col: line0.end_col.0,
                label: None,
            });
        }
    }

    pub fn render_lines(&self) -> Vec<RenderedLine> {
        let mut line_groups = vec![];

        //Group our lines by those with annotations and those without        
        let mut lines_iter = self.lines.iter().peekable();

        loop {
            match lines_iter.next() {
                None => break,
                Some(line) if line.annotations.is_empty() => {
                    // Collect unannotated group
                    let mut unannotated_group : Vec<&Line> = vec![];
                    
                    unannotated_group.push(line);

                    loop {
                        let next_line = 
                            match lines_iter.peek() {
                                None => break,
                                Some(x) if !x.annotations.is_empty() => break,
                                Some(x) => x.clone()
                            };

                        unannotated_group.push(next_line);
                        lines_iter.next();
                    }

                    line_groups.push((false, unannotated_group));
                }
                Some(line) => {
                    // Collect annotated group
                    let mut annotated_group : Vec<&Line> = vec![];

                    annotated_group.push(line);

                    loop {
                        let next_line = 
                            match lines_iter.peek() {
                                None => break,
                                Some(x) if x.annotations.is_empty() => break,
                                Some(x) => x.clone()
                            };

                        annotated_group.push(next_line);
                        lines_iter.next();
                    }

                    line_groups.push((true, annotated_group));
                }
            }
        }

        let mut output = vec![];
        for &(is_annotated, ref group) in line_groups.iter() {
            if is_annotated {
                let mut v: Vec<RenderedLine> = 
                    group.iter().flat_map(|line| self.render_line(line)).collect();
                output.append(&mut v);
            }
            else {
                if group.len() > 1 {
                    output.push(RenderedLine::from((String::from("..."), Elision)));
                }
                else {
                    let mut v: Vec<RenderedLine> = 
                        group.iter().flat_map(|line| self.render_line(line)).collect();
                    output.append(&mut v);
                }
            }
        }

        output
    }

    fn render_line(&self, line: &Line) -> Vec<RenderedLine> {
        let source_string = line.file.get_line(line.line_index).unwrap().to_string();
        if line.annotations.is_empty() {
            return vec![RenderedLine::from((source_string, SourceText))];
        }

        // We want to display like this:
        //
        //      vec.push(vec.pop().unwrap());
        //      ~~~      ~~~               ~ previous borrow ends here
        //      |        |
        //      |        error occurs here
        //      previous borrow of `vec` occurs here
        //
        // But there are some weird edge cases to be aware of:
        //
        //      vec.push(vec.pop().unwrap());
        //      ~~~~~~~~                    ~ previous borrow ends here
        //      ||
        //      |this makes no sense
        //      previous borrow of `vec` occurs here
        //
        // For this reason, we group the lines into "highlight lines"
        // and "text lines", where the highlight lines have the `~`.

        let mut highlight_line = Self::whitespace(&source_string);

        // Sort the annotations by (start, end col)
        let mut annotations = line.annotations.clone();
        annotations.sort();

        // First create the highlight line.
        for annotation in &annotations {
            for p in annotation.start_col .. annotation.end_col {
                highlight_line[p] = '~';
            }
        }

        // Now add the text labels. The last annotation is different
        // because that goes at the end of the highlight line.
        let (last_annotation, previous_annotations) = annotations.split_last()
                                                                 .unwrap();
        if let Some(ref label) = last_annotation.label {
            Self::write_label(&mut highlight_line,
                              last_annotation.end_col + 1,
                              label);
        }

        let highlight_string: String =
            highlight_line.into_iter().collect();

        // If that's the last annotation, we're done
        if previous_annotations.is_empty() {
            return vec![RenderedLine::from((source_string, SourceText)),
                        RenderedLine::from((highlight_string, Highlights))];
        }

        // Otherwise, total lines will be 1 + number of remaining.
        let total_lines = 1 + previous_annotations.len();

        // Make one string per line.
        let mut extra_lines: Vec<_> =
            (0..total_lines).map(|_| Self::whitespace(&source_string)).collect();

        for (index, annotation) in previous_annotations.iter().enumerate() {
            if let Some(ref label) = annotation.label {
                // Leave:
                // - 1 extra line
                // - One line for each thing that comes after
                let comes_after = previous_annotations.len() - index - 1;
                let blank_lines = 1 + comes_after;

                // For each blank line, draw a `|` at our column. The
                // text ought to be long enough for this.
                for index in 0..blank_lines {
                    extra_lines[index][annotation.start_col] = '|';
                }

                // After we write the `|`, write the label.
                Self::write_label(&mut extra_lines[blank_lines],
                                  annotation.start_col,
                                  label);
            }
        }

        // Convert the Vec<char> into String
        let extra_strings =
            extra_lines.into_iter()
                       .map(|v| RenderedLine::from((v, Highlights)));

        let mut lines: Vec<RenderedLine> =
            iter::once(RenderedLine::from((source_string, SourceText)))
            .chain(Some(RenderedLine::from((highlight_string, Highlights))))
            .chain(extra_strings)
            .collect();

        for line in &mut lines {
            line.trim();
        }

        lines
    }

    fn write_label(text: &mut Vec<char>,
                   position: usize,
                   label: &str)
    {
        if text.len() > position {
            text.truncate(position);
        }

        while text.len() < position {
            text.push(' ');
        }

        text.extend(label.chars());
    }

    fn whitespace(str: &str) -> Vec<char> {
        str.chars()
           .map(|c| match c {
               '\t' => '\t',
               _ => ' ',
           })
           .collect()
    }

    /// Ensure that we have a `Line` struct corresponding to
    /// `line_index` in the file. If we already have some other lines,
    /// then this will add the intervening lines to ensure that we
    /// have a complete snippet. (Note that when we finally display,
    /// some of those lines may be elided.)
    fn ensure_source_line(&mut self, file: &Rc<FileMap>, line_index: usize) -> usize {
        if self.lines.is_empty() {
            self.lines.push(Line {
                file: file.clone(),
                line_index: line_index,
                annotations: vec![]
            });
            return 0;
        }

        // This must come from the same file as any existing lines.
        assert_eq!(file.name, self.lines.first().unwrap().file.name);

        // Find the range of lines we have thus far.
        let first_line_index = self.lines.first().unwrap().line_index;
        let last_line_index = self.lines.last().unwrap().line_index;
        assert!(first_line_index <= last_line_index);

        // If the new line is lower than all the lines we have thus
        // far, then insert the new line and any intervening lines at
        // the front. In a silly attempt at micro-optimization, we
        // don't just call `insert` repeatedly, but instead make a new
        // (empty) vector, pushing the new lines onto it, and then
        // appending the old vector.
        if line_index < first_line_index {
            let lines = mem::replace(&mut self.lines, vec![]);
            self.lines.extend(
                (line_index .. first_line_index)
                    .map(|line| {
                        Line {
                            file: file.clone(),
                            line_index: line,
                            annotations: vec![]
                        }
                    })
                    .chain(lines));
            return 0;
        }

        // If the new line comes after the ones we have so far, insert
        // lines for it.
        if line_index > last_line_index {
            self.lines.extend(
                (last_line_index+1 .. line_index+1)
                    .map(|line| {
                        Line {
                            file: file.clone(),
                            line_index: line,
                            annotations: vec![]
                        }
                    }));
            return self.lines.len() - 1;
        }

        // Otherwise it should already exist.
        return line_index - first_line_index;
    }
}

impl From<(String, RenderedLineKind)> for RenderedLine {
    fn from((text, kind): (String, RenderedLineKind)) -> Self {
        RenderedLine {
            text: text,
            kind: kind,
        }
    }
}

impl From<(Vec<char>, RenderedLineKind)> for RenderedLine {
    fn from((text, kind): (Vec<char>, RenderedLineKind)) -> Self {
        RenderedLine {
            text: text.into_iter().collect(),
            kind: kind,
        }
    }
}

impl RenderedLine {
    fn trim(&mut self) {
        let len = self.text.trim_right().len();
        self.text.truncate(len);
    }
}
