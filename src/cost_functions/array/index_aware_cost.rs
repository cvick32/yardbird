use egg::{Language, Symbol};
use rustc_hash::FxHashSet;
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::{array::array_axioms::ArrayLanguage, list::list_axioms::ListLanguage},
};

/// Index-aware cost function that extends ArrayBMCCost by:
/// 1. Using reads_writes to discount symbols appearing as array indices
/// 2. Dampening the frame-distance penalty so early-frame terms needed by
///    multi-phase programs aren't over-penalized
/// 3. Giving compound arithmetic (Times, Mod, Div) a slight discount when
///    their sub-terms appear in index positions
#[derive(Clone)]
pub struct IndexAwareArrayCost {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: FxHashSet<Symbol>,
    pub property_terms: FxHashSet<Symbol>,
    pub reads_writes: ReadsAndWrites,
    /// Symbols that appear as read/write indices (precomputed from reads_writes)
    pub index_symbols: FxHashSet<Symbol>,
}

impl std::fmt::Debug for IndexAwareArrayCost {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IndexAwareArrayCost")
            .field("current_bmc_depth", &self.current_bmc_depth)
            .field(
                "init_and_transition_system_terms",
                &self.init_and_transition_system_terms,
            )
            .field("property_terms", &self.property_terms)
            .field("reads_writes", &self.reads_writes)
            .field("index_symbols", &self.index_symbols)
            .finish()
    }
}

impl IndexAwareArrayCost {
    pub fn new(
        current_bmc_depth: u32,
        init_and_transition_system_terms: FxHashSet<Symbol>,
        property_terms: FxHashSet<Symbol>,
        reads_writes: ReadsAndWrites,
    ) -> Self {
        // Precompute the set of symbols that appear in index positions
        let mut index_symbols = FxHashSet::default();
        for (_array, index) in &reads_writes.reads_from {
            // The index string may be a compound expression like "(+ i 1)",
            // extract leaf symbols from it.
            for token in Self::extract_leaf_symbols(index) {
                index_symbols.insert(token.into());
            }
        }
        for (_array, index, _value) in &reads_writes.writes_to {
            for token in Self::extract_leaf_symbols(index) {
                index_symbols.insert(token.into());
            }
        }

        Self {
            current_bmc_depth,
            init_and_transition_system_terms,
            property_terms,
            reads_writes,
            index_symbols,
        }
    }

    /// Extract leaf symbol names from an s-expression string like "(+ i 1)" or "i"
    fn extract_leaf_symbols(expr: &str) -> Vec<String> {
        let mut symbols = Vec::new();
        for token in expr.replace(['(', ')'], " ").split_whitespace() {
            // Skip operators and numeric literals
            if matches!(
                token,
                "+" | "-"
                    | "*"
                    | "/"
                    | "mod"
                    | "div"
                    | "select"
                    | "store"
                    | "="
                    | "<"
                    | ">"
                    | "<="
                    | ">="
                    | "and"
                    | "or"
                    | "not"
                    | "=>"
                    | "ite"
            ) {
                continue;
            }
            if token.parse::<i64>().is_ok() {
                continue;
            }
            symbols.push(token.to_string());
        }
        symbols
    }

    fn is_index_symbol(&self, sym: &Symbol) -> bool {
        if self.index_symbols.contains(sym) {
            return true;
        }
        // Also check unframed name: if "i+5" is an index symbol, treat "i" as index-related
        if let Some((name, _frame)) = sym.as_str().split_once(VARIABLE_FRAME_DELIMITER) {
            let name_sym: Symbol = name.into();
            return self.index_symbols.contains(&name_sym);
        }
        false
    }
}

impl egg::CostFunction<ArrayLanguage> for IndexAwareArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        let op_cost = match enode {
            ArrayLanguage::Num(num) => {
                let num_symbol: Symbol = num.to_string().into();
                let in_trans = self.init_and_transition_system_terms.contains(&num_symbol);
                let in_prop = self.property_terms.contains(&num_symbol);
                if in_prop {
                    1
                } else if in_trans {
                    2
                } else {
                    5
                }
            }
            ArrayLanguage::ConstArrTyped(_) => 0,
            ArrayLanguage::WriteTyped(_) => 1,
            ArrayLanguage::ReadTyped(_) => 1,
            ArrayLanguage::And(_) => 1,
            ArrayLanguage::Not(_) => 1,
            ArrayLanguage::Or(_) => 1,
            ArrayLanguage::Implies(_) => 1,
            ArrayLanguage::Eq(_) => 1,
            ArrayLanguage::Geq(_) => 1,
            ArrayLanguage::Gt(_) => 1,
            ArrayLanguage::Leq(_) => 1,
            ArrayLanguage::Lt(_) => 1,
            ArrayLanguage::Plus(_) => 1,
            ArrayLanguage::Negate(_) => 1,
            // Discount Times/Mod/Div slightly — compound index expressions like
            // (* 3 i) need these and shouldn't be penalized vs simpler terms.
            ArrayLanguage::Times(_) => 1,
            ArrayLanguage::Mod(_) => 1,
            ArrayLanguage::Div(_) => 1,
            ArrayLanguage::Symbol(sym) => {
                let in_trans = self.init_and_transition_system_terms.contains(sym);
                let in_prop = self.property_terms.contains(sym);
                let is_index = self.is_index_symbol(sym);

                if let Some((name, frame_number)) =
                    sym.as_str().split_once(VARIABLE_FRAME_DELIMITER)
                {
                    if name == "pc" {
                        // Never instantiate with the program counter.
                        return 10000;
                    } else if in_prop {
                        return 0;
                    } else if is_index {
                        // Index symbols get a strong discount — we want to
                        // extract terms that appear in read/write positions.
                        return 1;
                    } else if in_trans {
                        return 3;
                    }
                    // Dampen frame-distance penalty: use half the distance
                    // so early-frame terms in multi-phase programs aren't
                    // prohibitively expensive.
                    match frame_number.parse::<u32>() {
                        Ok(n) => {
                            let distance = self.current_bmc_depth.saturating_sub(n);
                            // Half the distance, minimum 1
                            (distance / 2).max(1)
                        }
                        Err(_) => panic!("Couldn't parse `{frame_number}`"),
                    }
                } else {
                    // Uninterpreted sort constants, etc.
                    100
                }
            }
        };

        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

impl egg::CostFunction<ListLanguage> for IndexAwareArrayCost {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        todo!()
    }
}

impl YardbirdCostFunction<ArrayLanguage> for IndexAwareArrayCost {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .iter()
            .chain(self.property_terms.iter())
            .map(|sym| sym.as_str().to_string())
            .collect()
    }

    fn get_transition_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .iter()
            .map(|sym| sym.as_str().to_string())
            .collect()
    }

    fn get_property_terms(&self) -> Vec<String> {
        self.property_terms
            .iter()
            .map(|sym| sym.as_str().to_string())
            .collect()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }
}
