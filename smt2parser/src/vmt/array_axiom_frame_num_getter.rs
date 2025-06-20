use std::collections::BTreeSet;

use log::debug;

use crate::{
    concrete::{Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

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
/// (not (= i@4 i@2)) => (Read-Int-Int (Write-Int-Int a@4 i@4 i@4) i@2) = (Read-Int-Int a@4 i@2)
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

    pub fn max_int(&self) -> u64 {
        *self
            .int_term_frame_map
            .iter()
            .map(|(_, frame)| frame)
            .max()
            .unwrap_or(&0) // If all variables are immutable, return 0.
    }

    pub fn min_int(&self) -> u64 {
        *self
            .int_term_frame_map
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
        if let Some((var_name, time_str)) = s.0.split_once(VARIABLE_FRAME_DELIMITER) {
            if !var_is_immutable(var_name) {
                let time = time_str.parse().unwrap();
                let var_sort = self.get_var_sort(var_name);
                if var_sort.contains("Array") {
                    self.array_term_frame_map
                        .insert((var_name.to_string(), time));
                } else {
                    self.int_term_frame_map.insert((var_name.to_string(), time));
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
    pub instance_term: Term,
    pub variable_offsets: std::collections::BTreeMap<String, Vec<i64>>,
    variables: Vec<Variable>,
}

impl VariableOffsetGetter {
    pub fn new(instance_term: Term, variables: Vec<Variable>) -> Self {
        let mut offset_getter = VariableOffsetGetter {
            visitor: SyntaxBuilder,
            instance_term: instance_term.clone(),
            variable_offsets: std::collections::BTreeMap::new(),
            variables,
        };

        instance_term.accept(&mut offset_getter).unwrap();

        offset_getter
    }

    /// Get the offset for a specific variable (returns the max offset for compatibility)
    pub fn get_offset(&self, var_name: &str) -> Option<i64> {
        self.variable_offsets
            .get(var_name)
            .and_then(|v| v.iter().max().copied())
    }

    /// Get all variable offsets
    pub fn get_all_offsets(&self) -> &std::collections::BTreeMap<String, Vec<i64>> {
        &self.variable_offsets
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

    /// Check if all variables have the same offset (span = 0)
    pub fn is_uniform_offset(&self) -> bool {
        self.offset_span() == 0
    }

    fn get_var_sort(&self, var_name: &str) -> String {
        for variable in &self.variables {
            if variable.get_current_variable_name() == var_name {
                return variable.get_sort_name();
            }
        }
        panic!("Could not find variable {var_name} in {:?}", self.variables);
    }
}

impl crate::rewriter::Rewriter for VariableOffsetGetter {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if let Some((var_name, time_str)) = s.0.split_once(VARIABLE_FRAME_DELIMITER) {
            if !var_is_immutable(var_name) {
                let time: u64 = time_str.parse().unwrap();
                // Calculate offset relative to the current frame (0)
                let offset = time as i64;
                self.variable_offsets
                    .entry(var_name.to_string())
                    .or_default()
                    .push(offset);
            }
        }
        Ok(s)
    }
}
