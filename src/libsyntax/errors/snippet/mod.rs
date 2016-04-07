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

use codemap::{CharPos, CodeMap, FileMap, Span};
use std::iter;
use std::rc::Rc;
use std::mem;
use std::ops::Range;

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
    /// Start column, 0-based indexing -- counting *characters*, not
    /// utf-8 bytes. Note that it is important that this field goes
    /// first, so that when we sort, we sort orderings by start
    /// column.
    start_col: usize,

    /// End column within the line.
    end_col: usize,

    /// Optional label to display adjacent to the annotation.
    label: Option<String>,
}

#[derive(Debug)]
pub struct RenderedLine {
    pub text: Vec<StyledString>,
    pub kind: RenderedLineKind,
}

#[derive(Debug)]
pub struct StyledString {
    pub text: String,
    pub style: Style,
}

#[derive(Copy, Clone, Debug)]
pub enum Style {
    FileNameLine,
    Quotation,
    Underline,
    Label,
    NoStyle,
}
use self::Style::*;

#[derive(Debug)]
pub enum RenderedLineKind {
    SourceText {
        file: Rc<FileMap>,
        line_index: usize,
    },
    Annotations,
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
        self.lines[index].push_annotation(line0.start_col,
                                          line0.end_col,
                                          label);
        for line in remaining_lines {
            if line.end_col > line.start_col {
                let index = self.ensure_source_line(&file_lines.file, line.line_index);
                self.lines[index].push_annotation(line.start_col,
                                                  line.end_col,
                                                  None);
            }
        }
    }

    pub fn render_lines(&self) -> Vec<RenderedLine> {
        let mut rendered_lines = self.render_all_lines();
        self.prepend_prefixes(&mut rendered_lines);
        self.trim_lines(&mut rendered_lines);
        rendered_lines
    }

    pub fn render_all_lines(&self) -> Vec<RenderedLine> {
        // Group our lines by those with annotations and those without
        let mut lines_iter = self.lines.iter().peekable();

        let mut line_groups = vec![];

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
                let mut annotation_ends_at_eol = false;
                let mut prev_ends_at_eol = false;
                let mut elide_unlabeled_region = false;

                for group_line in group.iter() {
                    let source_string =
                        group_line.file.get_line(group_line.line_index).unwrap().to_string();

                    for annotation in &group_line.annotations {
                        if annotation.end_col == source_string.len() {
                            annotation_ends_at_eol = true;
                        }
                    }

                    let is_single_unlabeled_annotated_line =
                        if group_line.annotations.len() == 1 {
                            if let Some(annotation) = group_line.annotations.first() {
                                match annotation.label {
                                    Some(_) => false,
                                    None => annotation.start_col == 0 &&
                                            annotation.end_col == source_string.len()
                                }
                            }
                            else {
                                false
                            }
                        }
                        else {
                            false
                        };

                    if prev_ends_at_eol && is_single_unlabeled_annotated_line {
                        if !elide_unlabeled_region {
                            output.push(RenderedLine::from((String::new(),
                                NoStyle, Elision)));
                            elide_unlabeled_region = true;
                            prev_ends_at_eol = true;
                        }
                        continue;
                    }

                    let mut v = self.render_line(group_line);
                    output.append(&mut v);

                    prev_ends_at_eol = annotation_ends_at_eol;
                }
            }
            else {
                if group.len() > 1 {
                    output.push(RenderedLine::from((String::new(), NoStyle, Elision)));
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

    pub fn prepend_prefixes(&self, rendered_lines: &mut [RenderedLine]) {
        let prefixes: Vec<_> =
            rendered_lines.iter()
                          .map(|rl| rl.kind.prefix())
                          .collect();

        // find the max amount of spacing we need; add 1 to
        // p.text.len() to leave space between the prefix and the
        // source text
        let padding_len =
            prefixes.iter()
                    .map(|p| if p.text.len() == 0 { 0 } else { p.text.len() + 1 })
                    .max()
                    .unwrap_or(0);

        for (mut prefix, line) in prefixes.into_iter().zip(rendered_lines) {
            let extra_spaces = (prefix.text.len() .. padding_len).map(|_| ' ');
            prefix.text.extend(extra_spaces);
            line.text.insert(0, prefix);
            match line.kind {
                RenderedLineKind::Elision => {}
                _ => line.text.insert(1, StyledString {text: String::from("|> "), style: FileNameLine})
            }
        }
    }

    fn trim_lines(&self, rendered_lines: &mut [RenderedLine]) {
        for line in rendered_lines {
            while !line.text.is_empty() {
                line.trim_last();
                if line.text.last().unwrap().text.is_empty() {
                    line.text.pop();
                } else {
                    break;
                }
            }
        }
    }

    fn render_line(&self, line: &Line) -> Vec<RenderedLine> {
        let source_string = line.file.get_line(line.line_index).unwrap().to_string();
        let source_kind = SourceText {
            file: line.file.clone(),
            line_index: line.line_index,
        };
        if line.annotations.is_empty() {
            return vec![RenderedLine::from((source_string, Quotation, source_kind))];
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
        // and "annotations lines", where the highlight lines have the `~`.

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

        // Now we are going to write labels in. To start, we'll exclude
        // the annotations with no labels.
        let (labeled_annotations, unlabeled_annotations): (Vec<_>, _) =
            annotations.into_iter()
                       .partition(|a| a.label.is_some());

        // If there are no annotations that need text, we're done.
        if labeled_annotations.is_empty() {
            return vec![RenderedLine::from((source_string, Quotation, source_kind)),
                        RenderedLine::from((highlight_line, Underline, Annotations))];
        }

        // Now add the text labels. We try, when possible, to stick the rightmost
        // annotation at the end of the highlight line:
        //
        //      vec.push(vec.pop().unwrap());
        //      ~~~      ~~~               ~ previous borrow ends here
        //
        // But sometimes that's not possible because one of the other
        // annotations overlaps it. For example, from the test
        // `span_overlap_label`, we have the following annotations
        // (written on distinct lines for clarity):
        //
        //      fn foo(x: u32) {
        //      ~~~~~~~~~~~~~~
        //             ~
        //
        // In this case, we can't stick the rightmost-most label on
        // the highlight line, or we would get:
        //
        //      fn foo(x: u32) {
        //      ~~~~~~~~ x_span
        //      |
        //      fn_span
        //
        // which is totally weird. Instead we want:
        //
        //      fn foo(x: u32) {
        //      ~~~~~~~~~~~~~~
        //      |      |
        //      |      x_span
        //      fn_span
        //
        // which is...less weird, at least. In fact, in general, if
        // the rightmost span overlaps with any other span, we should
        // use the "hang below" version, so we can at least make it
        // clear where the span *starts*.
        let mut labeled_annotations = &labeled_annotations[..];
        let mut highlight_label = String::new();
        match labeled_annotations.split_last().unwrap() {
            (last, previous) => {
                if previous.iter()
                           .chain(&unlabeled_annotations)
                           .all(|a| !overlaps(a, last))
                {
                    // there shouldn't be any squiggles after last.end_col,
                    // but there might be some whitespace; cut it off
                    if highlight_line.len() > last.end_col {
                        highlight_line.truncate(last.end_col);
                    }

                    // append the label afterwards; we keep it in a separate
                    // string
                    highlight_label = format!(" {}", last.label.as_ref().unwrap());
                    labeled_annotations = previous;
                }
            }
        }

        // The ~ line begins with the ~'s, which are Underline, and
        // ends with a (possibly empty) label.
        let highlight_render_line =
            RenderedLine::from(
                (highlight_line, Underline,
                 highlight_label, Label,
                 Annotations));

        // If that's the last annotation, we're done
        if labeled_annotations.is_empty() {
            return vec![
                RenderedLine::from((source_string, Quotation, source_kind)),
                highlight_render_line,
            ];
        }

        // Otherwise, total lines will be 1 + number of remaining.
        let total_lines = 1 + labeled_annotations.len();

        // Make one string per line.
        let mut extra_lines: Vec<_> =
            (0..total_lines).map(|_| Self::whitespace(&source_string)).collect();

        for (index, annotation) in labeled_annotations.iter().enumerate() {
            // Leave:
            // - 1 extra line
            // - One line for each thing that comes after
            let comes_after = labeled_annotations.len() - index - 1;
            let blank_lines = 1 + comes_after;

            // For each blank line, draw a `|` at our column. The
            // text ought to be long enough for this.
            for index in 0..blank_lines {
                extra_lines[index][annotation.start_col] = '|';
            }

            // After we write the `|`, write the label.
            Self::write_label(&mut extra_lines[blank_lines],
                              annotation.start_col,
                              annotation.label.as_ref().unwrap());
        }

        // Convert the Vec<char> into String
        let extra_strings =
            extra_lines.into_iter()
                       .map(|v| RenderedLine::from((v, Label, Annotations)));

        iter::once(RenderedLine::from((source_string, Quotation, source_kind)))
            .chain(Some(highlight_render_line))
            .chain(extra_strings)
            .collect()
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
            self.lines.push(Line::new(file, line_index));
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
                    .map(|line| Line::new(&file, line))
                    .chain(lines));
            return 0;
        }

        // If the new line comes after the ones we have so far, insert
        // lines for it.
        if line_index > last_line_index {
            self.lines.extend(
                (last_line_index+1 .. line_index+1)
                    .map(|line| Line::new(&file, line)));
            return self.lines.len() - 1;
        }

        // Otherwise it should already exist.
        return line_index - first_line_index;
    }
}

pub trait StringSource {
    fn make_string(self) -> String;
}

impl StringSource for String {
    fn make_string(self) -> String {
        self
    }
}

impl StringSource for Vec<char> {
    fn make_string(self) -> String {
        self.into_iter().collect()
    }
}

impl<S> From<(S, Style, RenderedLineKind)> for RenderedLine
    where S: StringSource
{
    fn from((text, style, kind): (S, Style, RenderedLineKind)) -> Self {
        RenderedLine {
            text: vec![StyledString {
                text: text.make_string(),
                style: style,
            }],
            kind: kind,
        }
    }
}

impl<S1,S2> From<(S1, Style, S2, Style, RenderedLineKind)> for RenderedLine
    where S1: StringSource, S2: StringSource
{
    fn from(tuple: (S1, Style, S2, Style, RenderedLineKind))
            -> Self {
        let (text1, style1, text2, style2, kind) = tuple;
        RenderedLine {
            text: vec![
                StyledString {
                    text: text1.make_string(),
                    style: style1,
                },
                StyledString {
                    text: text2.make_string(),
                    style: style2,
                }
            ],
            kind: kind,
        }
    }
}

impl RenderedLine {
    fn trim_last(&mut self) {
        let last_text = &mut self.text.last_mut().unwrap().text;
        let len = last_text.trim_right().len();
        last_text.truncate(len);
    }
}

impl RenderedLineKind {
    fn prefix(&self) -> StyledString {
        match *self {
            SourceText { file: _, line_index } =>
                StyledString {
                    text: format!("{}", line_index + 1),
                    style: FileNameLine,
                },
            Elision => 
                StyledString {
                    text: String::from("..."),
                    style: FileNameLine,
                },
            Annotations =>
                StyledString {
                    text: String::from(""),
                    style: FileNameLine,
                },
        }
    }
}

impl Line {
    fn new(file: &Rc<FileMap>, line_index: usize) -> Line {
        Line {
            file: file.clone(),
            line_index: line_index,
            annotations: vec![]
        }
    }

    fn push_annotation(&mut self, start: CharPos, end: CharPos, label: Option<String>) {
        self.annotations.push(Annotation {
            start_col: start.0,
            end_col: end.0,
            label: label
        });
    }
}

fn overlaps(a1: &Annotation,
            a2: &Annotation)
            -> bool
{
    between(a1.start_col, a2.start_col .. a2.end_col) ||
        between(a2.start_col, a1.start_col .. a1.end_col)
}

fn between(v: usize, range: Range<usize>) -> bool {
    v >= range.start && v < range.end
}
