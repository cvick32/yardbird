use std::collections::{BTreeMap, BTreeSet};

use crate::{
    concrete::{Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

/// This visits a Term and finds all of the frame numbers associated
/// with each variable in the Term.
/// For the Term (= a@0 a@1), we would expect FrameNumGetter.frame_nums to be {0, 1}.
/// We need this information in the Instantiator to when to plug in current variable
/// values or next variable values.
///
/// TODO: Using the Rewriter may not be the best choice here because it rebuilds the term.
/// But, using the TermVisitor like in LetExtract is more cumbersome.
#[derive(Clone, Debug)]
pub struct FrameNumGetter {
    pub visitor: SyntaxBuilder,
    pub instance_term: Term,
    pub frame_map: BTreeSet<(String, usize)>,
}

impl FrameNumGetter {
    pub fn new(instance_term: Term) -> Self {
        let mut frame_getter = FrameNumGetter {
            visitor: SyntaxBuilder,
            instance_term: instance_term.clone(),
            frame_map: BTreeSet::new(),
        };

        instance_term.accept(&mut frame_getter).unwrap();

        frame_getter
    }

    pub(crate) fn max_min_difference(&self) -> usize {
        if self.frame_map.len() < 2 {
            0
        } else {
            self.max() - self.min()
        }
    }

    pub(crate) fn min(&self) -> usize {
        *self.frame_map.iter().map(|(_, frame)| frame).min().unwrap()
    }

    pub(crate) fn max(&self) -> usize {
        *self.frame_map.iter().map(|(_, frame)| frame).max().unwrap()
    }

    pub(crate) fn needs_prophecy(&self) -> bool {
        if self.frame_map.len() <= 2 && self.max_min_difference() >= 1 {
            true
        } else {
            log::info!("NEED TO INSTANTIATE WITH PROPHECY: {}", self.instance_term);
            false
        }
    }
}

impl crate::rewriter::Rewriter for FrameNumGetter {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if let Some((var_name, time_str)) = s.0.split_once(VARIABLE_FRAME_DELIMITER) {
            if var_is_immutable(var_name) {
                // Don't add time step to frame_nums because immutable variables always
                // have the same value.
                Ok(s)
            } else {
                let time = time_str.parse().unwrap();
                self.frame_map.insert((var_name.to_string(), time));
                Ok(s)
            }
        } else {
            Ok(s)
        }
    }
}
