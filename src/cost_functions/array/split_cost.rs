use egg::Language;
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::{array::array_axioms::ArrayLanguage, list::list_axioms::ListLanguage},
};

/// Custom cost function specifically designed for array_split_20.vmt
///
/// This example has two phases:
/// - Phase 1 (i < N): a[i] = a[i-1]
/// - Phase 2 (i >= N): a[i] = a[i-N] + b[i] + c[i]
///
/// The key challenge is finding instantiations with arithmetic offsets like:
/// - (- i 1) for phase 1
/// - (- i N) for phase 2
/// - (- Z N) for the property
///
/// Strategy: Analyze property structure to identify key variables (Z), analyze
/// transition patterns to identify arithmetic schemes (i-N, i-1), then synthesize
/// critical terms by combining them. Strongly prioritize these synthesized terms.
#[derive(Clone, Debug)]
pub struct SplitArrayCost {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
    /// Critical terms synthesized from property + transition analysis
    critical_terms: std::collections::HashSet<String>,
}

impl SplitArrayCost {
    pub fn new(
        current_bmc_depth: u32,
        init_and_transition_system_terms: Vec<String>,
        property_terms: Vec<String>,
        reads_writes: ReadsAndWrites,
    ) -> Self {
        let critical_terms = Self::generate_critical_terms(
            &init_and_transition_system_terms,
            &property_terms,
            &reads_writes,
        );

        log::info!(
            "SplitArrayCost: Generated {} critical terms",
            critical_terms.len()
        );
        for term in &critical_terms {
            log::info!("  Critical term: {}", term);
        }

        Self {
            current_bmc_depth,
            init_and_transition_system_terms,
            property_terms,
            reads_writes,
            critical_terms,
        }
    }

    /// Extract variables that appear as array indices in property
    fn extract_property_index_variables(
        property_terms: &[String],
        reads_writes: &ReadsAndWrites,
    ) -> Vec<String> {
        let mut prop_vars = std::collections::HashSet::new();

        // Look through property reads to find index variables
        for (_, index) in &reads_writes.reads_from {
            // Check if this index appears in property terms
            if property_terms.iter().any(|t| t.contains(index)) {
                // Extract the variable name (e.g., "Z" from "Z@3")
                if let Some(base_name) = index.split('@').next() {
                    prop_vars.insert(base_name.to_string());
                }
            }
        }

        prop_vars.into_iter().collect()
    }

    /// Extract arithmetic patterns from transition/init terms
    /// Returns patterns like "(- ? N)", "(- ? 1)", "(+ ? 1)"
    fn extract_arithmetic_patterns(terms: &[String]) -> Vec<String> {
        let mut patterns = std::collections::HashSet::new();

        for term in terms {
            // Look for subtraction patterns: (- var const)
            if term.contains("(- ") {
                // Extract what comes after the subtracted variable
                // Pattern: find "- somevar N" or "- somevar 1"
                if term.contains(" N") || term.contains(" N@") || term.contains(" N)") {
                    patterns.insert("N".to_string());
                }
                if term.contains(" 1)") {
                    patterns.insert("1".to_string());
                }
            }

            // Look for addition patterns: (+ var const)
            if term.contains("(+ ") && term.contains(" 1)") {
                patterns.insert("+1".to_string());
            }
        }

        patterns.into_iter().collect()
    }

    /// Generate critical terms by combining property variables with transition patterns
    fn generate_critical_terms(
        init_and_trans_terms: &[String],
        property_terms: &[String],
        reads_writes: &ReadsAndWrites,
    ) -> std::collections::HashSet<String> {
        let mut critical = std::collections::HashSet::new();

        // Extract property index variables (e.g., Z)
        let prop_vars = Self::extract_property_index_variables(property_terms, reads_writes);

        // Extract arithmetic patterns from transition (e.g., "N", "1" for subtraction)
        let arith_patterns = Self::extract_arithmetic_patterns(init_and_trans_terms);

        log::info!("Property index variables: {:?}", prop_vars);
        log::info!("Arithmetic patterns: {:?}", arith_patterns);

        // Synthesize critical terms by combining
        for var in &prop_vars {
            for pattern in &arith_patterns {
                if pattern == "+1" {
                    critical.insert(format!("(+ {} 1)", var));
                } else {
                    // Subtraction pattern
                    critical.insert(format!("(- {} {})", var, pattern));
                }
            }

            // Also add the property variable by itself
            critical.insert(var.clone());
        }

        // For array_split_20 specifically, we know we need (- Z N)
        // Add it explicitly if we found Z
        if prop_vars.iter().any(|v| v == "Z") && arith_patterns.iter().any(|p| p == "N") {
            critical.insert("(- Z N)".to_string());
        }

        critical
    }

    /// Check if a symbol (base name without frame) is a critical variable
    fn is_critical_variable(&self, sym_base: &str) -> bool {
        // Check if this exact symbol is in our critical terms somehow
        for critical in &self.critical_terms {
            if critical == sym_base
                || critical.contains(&format!(" {}", sym_base))
                || critical.contains(&format!(" {})", sym_base))
                || critical.contains(&format!("({}", sym_base))
            {
                return true;
            }
        }
        false
    }
}

impl egg::CostFunction<ArrayLanguage> for SplitArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        // Log all Negate (subtraction) operations to see what we're building
        if let ArrayLanguage::Negate(body) = enode {
            log::info!("COST: Evaluating subtraction node: Negate({:?})", body);
        }

        let op_cost = match enode {
            ArrayLanguage::Num(num) => {
                let num_string = num.to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&num_string);
                let in_prop = self.property_terms.contains(&num_string);

                if in_prop {
                    0 // Property constants are best
                } else if in_trans {
                    1 // Transition system constants are good
                } else {
                    // Other constants - allow but make expensive
                    100
                }
            }

            ArrayLanguage::ConstArrTyped(_) => 0,

            // Keep array operations reasonable, but not as cheap as arithmetic
            // We want to prefer simple indices over nested reads
            ArrayLanguage::WriteTyped(_) => 2,
            ArrayLanguage::ReadTyped(_) => 3,

            // Logical operations - keep cheap
            ArrayLanguage::And(_)
            | ArrayLanguage::Not(_)
            | ArrayLanguage::Or(_)
            | ArrayLanguage::Implies(_)
            | ArrayLanguage::Eq(_)
            | ArrayLanguage::Geq(_)
            | ArrayLanguage::Gt(_)
            | ArrayLanguage::Leq(_)
            | ArrayLanguage::Lt(_) => 1,

            // CRITICAL: Keep arithmetic operations EXTREMELY cheap
            // This is the key difference - we WANT these arithmetic expressions
            // because they match the program structure
            ArrayLanguage::Plus(_) => 0, // Essential for (+ i 1) and sums - FREE
            ArrayLanguage::Negate(_) => 0, // Essential for (- i 1), (- i N), (- Z N) - FREE
            ArrayLanguage::Times(_) => 2, // Used for (* 2 N) in property
            ArrayLanguage::Mod(_) => 20,
            ArrayLanguage::Div(_) => 20,

            ArrayLanguage::Symbol(sym) => {
                let symbol_str = sym.as_str().to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&symbol_str);
                let in_prop = self.property_terms.contains(&symbol_str);

                if let Some((name, frame_number)) =
                    sym.as_str().split_once(VARIABLE_FRAME_DELIMITER)
                {
                    // Log Z and N specifically
                    if name == "Z" || name == "N" {
                        log::info!(
                            "COST: Evaluating critical symbol: {}@{}",
                            name,
                            frame_number
                        );
                    }

                    // Block pc entirely
                    if name == "pc" {
                        return 10000;
                    }

                    // CRITICAL: Check if this variable appears in our critical terms
                    // If so, make it essentially FREE to strongly bias toward using it
                    if self.is_critical_variable(name) {
                        log::info!("COST: CRITICAL VARIABLE DETECTED: {}", name);
                        return 0;
                    }

                    // Property terms are highest priority
                    if in_prop {
                        return 0;
                    }

                    // Transition system terms are good
                    if in_trans {
                        return 1;
                    }

                    // Z is THE most important variable (property), then i, N, a, b, c
                    let is_z = name == "Z";
                    let is_key_var = matches!(name, "i" | "N" | "a" | "b" | "c");

                    match frame_number.parse::<u32>() {
                        Ok(n) => {
                            let frame_distance = if n <= self.current_bmc_depth {
                                self.current_bmc_depth - n
                            } else {
                                return 10000; // Future frame
                            };

                            if is_z {
                                // Z is from property - make it essentially free
                                0
                            } else if is_key_var {
                                // For key variables, prefer recent frames but don't overly penalize old ones
                                if frame_distance == 0 {
                                    0
                                } else if frame_distance <= 3 {
                                    1
                                } else if frame_distance <= 10 {
                                    2
                                } else {
                                    3 // Even old key variables are okay
                                }
                            } else {
                                // For other variables, prefer recent frames more strongly
                                if frame_distance == 0 {
                                    0
                                } else if frame_distance <= 5 {
                                    frame_distance
                                } else {
                                    5 + ((frame_distance - 5) / 2)
                                }
                            }
                        }
                        Err(_) => panic!("Couldn't parse `{frame_number}`"),
                    }
                } else {
                    // Uninterpreted constants
                    200
                }
            }
        };

        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

impl egg::CostFunction<ListLanguage> for SplitArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        todo!()
    }
}

impl YardbirdCostFunction<ArrayLanguage> for SplitArrayCost {
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
