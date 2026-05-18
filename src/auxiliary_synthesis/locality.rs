use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use smt2parser::{
    concrete::{QualIdentifier, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct FrameSpan {
    pub min_frame: Option<i64>,
    pub max_frame: Option<i64>,
    pub span: i64,
    pub frames: BTreeSet<i64>,
}

impl FrameSpan {
    pub fn from_term(term: &Term) -> Self {
        let mut frames = BTreeSet::new();
        collect_term_frames(term, &mut frames);
        Self::from_frames(frames)
    }

    pub fn from_frames(frames: BTreeSet<i64>) -> Self {
        let min_frame = frames.iter().next().copied();
        let max_frame = frames.iter().next_back().copied();
        let span = match (min_frame, max_frame) {
            (Some(min), Some(max)) => max - min,
            _ => 0,
        };
        Self {
            min_frame,
            max_frame,
            span,
            frames,
        }
    }

    pub fn is_initial_local(&self) -> bool {
        self.frames.is_empty() || self.frames.iter().all(|frame| *frame == 0)
    }

    pub fn is_transition_local(&self) -> bool {
        self.frames.len() <= 2 && self.span <= 1
    }

    pub fn is_non_local(&self) -> bool {
        !self.is_initial_local() && !self.is_transition_local()
    }
}

fn collect_term_frames(term: &Term, frames: &mut BTreeSet<i64>) {
    match term {
        Term::Constant(_) => {}
        Term::QualIdentifier(qi) => collect_qual_identifier_frames(qi, frames),
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            collect_qual_identifier_frames(qual_identifier, frames);
            for arg in arguments {
                collect_term_frames(arg, frames);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_term_frames(binding, frames);
            }
            collect_term_frames(term, frames);
        }
        Term::Forall { term, .. } | Term::Exists { term, .. } => {
            collect_term_frames(term, frames);
        }
        Term::Match { term, cases } => {
            collect_term_frames(term, frames);
            for (_, case_term) in cases {
                collect_term_frames(case_term, frames);
            }
        }
        Term::Attributes { term, .. } => {
            collect_term_frames(term, frames);
        }
    }
}

fn collect_qual_identifier_frames(qi: &QualIdentifier, frames: &mut BTreeSet<i64>) {
    collect_symbol_frames(&qi.get_name(), frames);
}

fn collect_symbol_frames(symbol: &str, frames: &mut BTreeSet<i64>) {
    let Some((name, frame)) = symbol.split_once(VARIABLE_FRAME_DELIMITER) else {
        return;
    };
    if var_is_immutable(name) {
        return;
    }
    if let Ok(frame) = frame.parse::<i64>() {
        frames.insert(frame);
    }
}

#[cfg(test)]
mod tests {
    use smt2parser::get_term_from_term_string;

    use super::*;

    #[test]
    fn no_frames_is_local() {
        let term = get_term_from_term_string("(= x y)");
        let span = FrameSpan::from_term(&term);
        assert!(span.is_initial_local());
        assert!(span.is_transition_local());
        assert!(!span.is_non_local());
    }

    #[test]
    fn adjacent_frames_are_transition_local() {
        let term = get_term_from_term_string("(= x@0 x@1)");
        let span = FrameSpan::from_term(&term);
        assert_eq!(span.min_frame, Some(0));
        assert_eq!(span.max_frame, Some(1));
        assert_eq!(span.span, 1);
        assert!(span.is_transition_local());
        assert!(!span.is_non_local());
    }

    #[test]
    fn distant_frames_are_non_local() {
        let term = get_term_from_term_string("(= x@0 x@2)");
        let span = FrameSpan::from_term(&term);
        assert_eq!(span.span, 2);
        assert!(span.is_non_local());
    }

    #[test]
    fn immutable_variables_do_not_count_as_frames() {
        let term = get_term_from_term_string("(= N@0 N@9)");
        let span = FrameSpan::from_term(&term);
        assert!(span.frames.is_empty());
        assert!(!span.is_non_local());
    }
}
