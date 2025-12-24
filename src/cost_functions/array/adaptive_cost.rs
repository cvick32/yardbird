use egg::Language;
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::{array::array_axioms::ArrayLanguage, list::list_axioms::ListLanguage},
};

/// Adaptive cost function designed to handle complex array examples that timeout
/// with the basic SymbolCost function. Key improvements:
///
/// 1. Penalizes nested Read/Write operations to avoid exponential blowup
/// 2. Strongly prefers simpler arithmetic expressions in indices
/// 3. More balanced frame preference (doesn't overly favor recent frames)
/// 4. Allows selective use of pc variables in certain contexts
/// 5. Lower cost for direct array accesses vs computed indices
#[derive(Clone, Debug)]
pub struct AdaptiveArrayCost {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
    depth: u32,
}

impl AdaptiveArrayCost {
    pub fn new(
        current_bmc_depth: u32,
        init_and_transition_system_terms: Vec<String>,
        property_terms: Vec<String>,
        reads_writes: ReadsAndWrites,
    ) -> Self {
        Self {
            current_bmc_depth,
            init_and_transition_system_terms,
            property_terms,
            reads_writes,
            depth: 0,
        }
    }

    /// Calculate complexity penalty for arithmetic expressions
    /// These costs must be VERY low to avoid exponential blowup in nested expressions
    fn arithmetic_complexity(&self, op: &str) -> u32 {
        match op {
            "Plus" | "Negate" => 1, // Simple arithmetic - keep very low
            "Times" => 10,          // More complex, especially with non-constants
            "Mod" | "Div" => 15,    // Even more complex
            _ => 0,
        }
    }
}

impl egg::CostFunction<ArrayLanguage> for AdaptiveArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        // Track nesting depth to penalize deeply nested terms
        // Keep penalty VERY small - even nested expressions should have reasonable costs
        self.depth += 1;
        let depth_penalty = if self.depth > 5 {
            (self.depth - 5) * 2 // Much gentler penalty
        } else {
            0
        };

        let op_cost = match enode {
            ArrayLanguage::Num(num) => {
                let num_string = num.to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&num_string);
                let in_prop = self.property_terms.contains(&num_string);

                if in_prop {
                    1 // Property constants are good
                } else if in_trans {
                    2 // Transition system constants are okay
                } else {
                    // Don't completely rule out other constants, but make them expensive
                    50
                }
            }
            ArrayLanguage::ConstArrTyped(_) => 0,
            ArrayLanguage::WriteTyped(_) => {
                if self.depth > 2 {
                    10 + ((self.depth - 2) * 5) // Penalize nested writes strongly
                } else {
                    3 // Base write cost - keep low for simple writes
                }
            }
            // Penalize Read operations that are nested
            ArrayLanguage::ReadTyped(_) => {
                if self.depth > 2 {
                    8 + ((self.depth - 2) * 3) // Penalize nested reads
                } else {
                    2 // Base read cost - keep low for simple reads
                }
            }
            ArrayLanguage::And(_) => 1,
            ArrayLanguage::Not(_) => 1,
            ArrayLanguage::Or(_) => 1,
            ArrayLanguage::Implies(_) => 1,
            ArrayLanguage::Eq(_) => 1,
            ArrayLanguage::Geq(_) => 1,
            ArrayLanguage::Gt(_) => 1,
            ArrayLanguage::Leq(_) => 1,
            ArrayLanguage::Lt(_) => 1,

            // Arithmetic operations - penalize based on complexity
            ArrayLanguage::Plus(_) => self.arithmetic_complexity("Plus"),
            ArrayLanguage::Negate(_) => self.arithmetic_complexity("Negate"),
            ArrayLanguage::Times(_) => self.arithmetic_complexity("Times"),
            ArrayLanguage::Mod(_) => self.arithmetic_complexity("Mod"),
            ArrayLanguage::Div(_) => self.arithmetic_complexity("Div"),

            ArrayLanguage::Symbol(sym) => {
                let symbol_str = sym.as_str().to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&symbol_str);
                let in_prop = self.property_terms.contains(&symbol_str);

                if let Some((name, frame_number)) =
                    sym.as_str().split_once(VARIABLE_FRAME_DELIMITER)
                {
                    // Special handling for program counter
                    if name == "pc" {
                        // Allow pc in some contexts, but make it expensive
                        return 500;
                    }

                    // Property terms are preferred
                    if in_prop {
                        return 0;
                    }

                    // Transition system terms are good
                    if in_trans {
                        return 2;
                    }

                    // More balanced frame preference: prefer recent frames, but not too strongly
                    // This allows the solver to consider older frames when needed
                    match frame_number.parse::<u32>() {
                        Ok(n) => {
                            let frame_distance = if n <= self.current_bmc_depth {
                                self.current_bmc_depth - n
                            } else {
                                // Future frame, very expensive
                                return 10000;
                            };

                            // Gentler penalty for older frames compared to SymbolCost
                            // SymbolCost: returns raw distance
                            // AdaptiveCost: returns sqrt-like growth
                            if frame_distance == 0 {
                                0
                            } else if frame_distance <= 5 {
                                frame_distance / 2 // Very recent: 0, 0, 1, 1, 2
                            } else {
                                2 + ((frame_distance - 5) / 3) // Older: grows slowly
                            }
                        }
                        Err(_) => panic!("Couldn't parse `{frame_number}`"),
                    }
                } else {
                    // Uninterpreted constants - allow but make expensive
                    100
                }
            }
        };

        let result = enode.fold(op_cost + depth_penalty, |sum, id| sum + costs(id));

        // Restore depth after calculating children
        self.depth -= 1;

        result
    }
}

impl egg::CostFunction<ListLanguage> for AdaptiveArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        todo!()
    }
}

impl YardbirdCostFunction<ArrayLanguage> for AdaptiveArrayCost {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .clone()
            .into_iter()
            .chain(self.property_terms.clone())
            .collect::<Vec<String>>()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }
}
