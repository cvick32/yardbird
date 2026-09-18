use egg::Language;
use smt2parser::vmt::{split_framed_symbol, ReadsAndWrites};

use crate::{
    cost_functions::{
        array::{ArrayCostContext, ArrayCostFactory},
        YardbirdCostFunction,
    },
    instantiation::language::TermLanguage,
    theories::list::list_axioms::ListLanguage,
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

impl ArrayCostFactory for AdaptiveArrayCost {
    type Config = ();

    fn from_context(smt: &ArrayCostContext, depth: u32, _config: &Self::Config) -> Self {
        Self::new(
            depth,
            smt.get_init_and_transition_subterms(),
            smt.get_property_subterms(),
            smt.get_reads_and_writes(),
        )
    }
}

impl egg::CostFunction<TermLanguage> for AdaptiveArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &TermLanguage, mut costs: C) -> Self::Cost
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
            TermLanguage::Num(num) => {
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
            TermLanguage::ConstArrTyped(_) => 0,
            TermLanguage::WriteTyped(_) => {
                if self.depth > 2 {
                    10 + ((self.depth - 2) * 5) // Penalize nested writes strongly
                } else {
                    3 // Base write cost - keep low for simple writes
                }
            }
            // Penalize Read operations that are nested
            TermLanguage::ReadTyped(_) => {
                if self.depth > 2 {
                    8 + ((self.depth - 2) * 3) // Penalize nested reads
                } else {
                    2 // Base read cost - keep low for simple reads
                }
            }
            TermLanguage::And(_) => 1,
            TermLanguage::Not(_) => 1,
            TermLanguage::Or(_) => 1,
            TermLanguage::Implies(_) => 1,
            TermLanguage::Eq(_) => 1,
            TermLanguage::Geq(_) => 1,
            TermLanguage::Gt(_) => 1,
            TermLanguage::Leq(_) => 1,
            TermLanguage::Lt(_) => 1,

            // Arithmetic operations - penalize based on complexity
            TermLanguage::Plus(_) => self.arithmetic_complexity("Plus"),
            TermLanguage::Negate(_) => self.arithmetic_complexity("Negate"),
            TermLanguage::Times(_) => self.arithmetic_complexity("Times"),
            TermLanguage::Mod(_) => self.arithmetic_complexity("Mod"),
            TermLanguage::Div(_) => self.arithmetic_complexity("Div"),
            TermLanguage::ToReal(_) => self.arithmetic_complexity("ToReal"),
            TermLanguage::Ite(_)
            | TermLanguage::Apply(_)
            | TermLanguage::Domain(_)
            | TermLanguage::SortTag(_) => 5,

            TermLanguage::Symbol(sym) => {
                let symbol_str = sym.as_str().to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&symbol_str);
                let in_prop = self.property_terms.contains(&symbol_str);

                if let Some((name, frame_number)) = split_framed_symbol(sym.as_str()) {
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
                    match u32::try_from(frame_number) {
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
                        Err(_) => 100,
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

impl YardbirdCostFunction<TermLanguage> for AdaptiveArrayCost {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .clone()
            .into_iter()
            .chain(self.property_terms.clone())
            .collect::<Vec<String>>()
    }

    fn get_transition_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms.clone()
    }

    fn get_property_terms(&self) -> Vec<String> {
        self.property_terms.clone()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }
}
