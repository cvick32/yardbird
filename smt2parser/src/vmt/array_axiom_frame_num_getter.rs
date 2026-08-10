use std::{collections::BTreeSet, convert::TryFrom};

use log::debug;

use crate::{
    concrete::{Symbol, SyntaxBuilder, Term},
    vmt::{split_framed_symbol, variable::var_is_immutable},
};

use super::definition_graph::DefinitionFrameInfo;
use super::variable::Variable;

#[derive(Clone, Debug)]
pub struct ArrayAxiomFrameNumGetter {
    pub visitor: SyntaxBuilder,
    pub instance_term: Term,
    pub array_term_frame_map: BTreeSet<(String, u64)>,
    pub int_term_frame_map: BTreeSet<(String, u64)>,
    variables: Vec<Variable>,
}

/// What happens on this example?
/// (not (= i@4 i@2)) => (Read_Int_Int (Read_Int_Int a@4 i@4 i@4) i@2) = (Read_Int_Int a@4 i@2)
/// We set i@2 = i and then quantify out everything else. I feel like this isn't
/// really what we want, what we want is to say forall i@2 then the rest holds. We don't
/// want to quantify over arrays. It's unclear to me if that even makes sense
impl ArrayAxiomFrameNumGetter {
    pub fn new(instance_term: Term, variables: Vec<Variable>) -> Self {
        let mut frame_getter = ArrayAxiomFrameNumGetter {
            visitor: SyntaxBuilder,
            instance_term: instance_term.clone(),
            array_term_frame_map: BTreeSet::new(),
            int_term_frame_map: BTreeSet::new(),
            variables,
        };

        instance_term.accept(&mut frame_getter).unwrap();

        frame_getter
    }

    pub fn max_array(&self) -> u64 {
        *self
            .array_term_frame_map
            .iter()
            .map(|(_, frame)| frame)
            .max()
            .unwrap_or(&0) // If all variables are immutable, return 0.
    }

    pub fn min_array(&self) -> u64 {
        *self
            .array_term_frame_map
            .iter()
            .map(|(_, frame)| frame)
            .min()
            .unwrap_or(&0) // If all variables are immutable, return 0.
    }

    fn get_var_sort(&self, var_name: &str) -> String {
        for variable in &self.variables {
            if variable.get_current_variable_name() == var_name {
                return variable.get_sort_name();
            }
        }
        panic!("Could not find variable {var_name} in {:?}", self.variables);
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn to_substitution(
        &self,
    ) -> Option<(
        std::collections::BTreeMap<(String, u64), String>,
        BTreeSet<String>,
        bool,
    )> {
        if self.max_array() - self.min_array() > 1 {
            // This forces us to never quantify over arrays.
            debug!(
                "[smt2parser] Tried to quantify over array in instantitation: {}",
                self.instance_term
            );
            None
        } else {
            let min_array_frame_number = self.min_array();
            let mut quantified = BTreeSet::new();
            let mut is_current = true;
            let mut subst: std::collections::BTreeMap<(String, u64), String> = self
                .int_term_frame_map
                .iter()
                .enumerate()
                .map(|(idx, (var, frame))| {
                    if *frame == min_array_frame_number || var_is_immutable(var)
                    // || (*frame == min_array_frame_number - 1
                    //     && self.max_array() == self.min_array())
                    {
                        ((var.clone(), *frame), var.clone())
                    } else if *frame == min_array_frame_number + 1 {
                        is_current = false;
                        ((var.clone(), *frame), format!("{var}_next"))
                    } else {
                        let name = format!("PH{idx}");
                        quantified.insert(name.clone());
                        ((var.clone(), *frame), name)
                    }
                })
                .collect();

            let arr_subst: std::collections::BTreeMap<(String, u64), String> = self
                .array_term_frame_map
                .iter()
                .map(|(var, frame)| {
                    if *frame == min_array_frame_number || var_is_immutable(var) {
                        ((var.clone(), *frame), var.clone())
                    } else {
                        is_current = false;
                        ((var.clone(), *frame), format!("{var}_next"))
                    }
                })
                .collect();

            subst.extend(arr_subst);
            Some((subst, quantified, is_current))
        }
    }
}

impl crate::rewriter::Rewriter for ArrayAxiomFrameNumGetter {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if let Some((var_name, time)) = split_framed_symbol(&s.0) {
            if !var_is_immutable(&var_name) {
                let Ok(time) = u64::try_from(time) else {
                    return Ok(s);
                };
                let var_sort = self.get_var_sort(&var_name);
                if var_sort.contains("Array") {
                    self.array_term_frame_map.insert((var_name, time));
                } else {
                    self.int_term_frame_map.insert((var_name, time));
                }
            }
        }
        Ok(s)
    }
}

/// Provides offset information for each variable in a term.
/// This is useful for understanding how to properly instantiate formulas during unrolling.
#[derive(Clone, Debug)]
pub struct VariableOffsetGetter {
    pub visitor: SyntaxBuilder,
    pub variable_offsets: std::collections::BTreeMap<String, Vec<i64>>,
    definition_frames: DefinitionFrameInfo,
}

impl VariableOffsetGetter {
    pub fn new(instance_term: Term) -> Self {
        let mut offset_getter = VariableOffsetGetter {
            visitor: SyntaxBuilder,
            variable_offsets: std::collections::BTreeMap::new(),
            definition_frames: DefinitionFrameInfo::default(),
        };

        instance_term.accept(&mut offset_getter).unwrap();

        offset_getter
    }

    pub fn with_definition_frames(
        instance_term: Term,
        definition_frames: DefinitionFrameInfo,
    ) -> Self {
        let mut offset_getter = VariableOffsetGetter {
            visitor: SyntaxBuilder,
            variable_offsets: std::collections::BTreeMap::new(),
            definition_frames,
        };

        instance_term.accept(&mut offset_getter).unwrap();
        offset_getter
    }

    /// Get the minimum offset across all variables and all their offsets
    pub fn min_offset(&self) -> i64 {
        self.variable_offsets
            .values()
            .flat_map(|v| v.iter())
            .min()
            .copied()
            .unwrap_or(0)
    }

    /// Get the maximum offset across all variables and all their offsets
    pub fn max_offset(&self) -> i64 {
        self.variable_offsets
            .values()
            .flat_map(|v| v.iter())
            .max()
            .copied()
            .unwrap_or(0)
    }

    /// Get the total span of offsets (max - min)
    pub fn offset_span(&self) -> i64 {
        self.max_offset() - self.min_offset()
    }
}

impl crate::rewriter::Rewriter for VariableOffsetGetter {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if let Some((var_name, frame)) = split_framed_symbol(&s.0) {
            if let Some(relative_offsets) = self.definition_frames.offsets(&var_name) {
                let anchor = frame;
                let offsets = self.variable_offsets.entry(var_name).or_default();
                // The helper symbol exists at its anchor even when its body is
                // next-state-only. Keeping the anchor in the span prevents a
                // reusable instance from being shifted to a negative frame.
                offsets.push(anchor);
                offsets.extend(
                    relative_offsets
                        .iter()
                        .map(|offset| anchor + i64::from(*offset)),
                );
            } else if !var_is_immutable(&var_name) {
                // Calculate offset relative to the current frame (0)
                self.variable_offsets
                    .entry(var_name)
                    .or_default()
                    .push(frame);
            }
        }
        Ok(s)
    }
}

#[cfg(test)]
mod tests {
    use super::VariableOffsetGetter;
    use crate::concrete::{QualIdentifier, Term};

    #[test]
    fn variable_offset_getter_reads_quoted_framed_symbols() {
        let term = Term::QualIdentifier(QualIdentifier::simple("|.x{78}@1|"));

        let getter = VariableOffsetGetter::new(term);

        assert_eq!(getter.variable_offsets.get("|.x{78}|"), Some(&vec![1]));
    }
}
