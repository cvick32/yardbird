//! Structural theory inventory, independent of solver or abstraction support.
//! Visit complete commands so definitions, binder sorts and background axioms
//! participate even when their vocabulary is absent from the main assertions.
use crate::{
    concrete::{Command, Constant, Identifier, QualIdentifier, Sort, SyntaxBuilder, Term},
    rewriter::Rewriter,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TheoryFeatures {
    pub array_sorts: Vec<(Sort, Sort)>,
    pub forall: usize,
    pub exists: usize,
    pub lambdas: usize,
    pub integers: bool,
    pub reals: bool,
    pub bitvectors: bool,
    pub strings: bool,
    pub floating_point: bool,
    pub parameterized_lists: bool,
    pub nonlinear_arithmetic: bool,
    pub sort_aliases: bool,
    pub array_extensions: Vec<String>,
}

impl TheoryFeatures {
    pub fn analyze(commands: &[Command]) -> Self {
        let mut visitor = Inventory {
            features: Self::default(),
            builder: SyntaxBuilder,
        };
        for command in commands {
            // SyntaxBuilder reconstructs an already parsed AST; this cannot fail.
            command
                .clone()
                .accept(&mut visitor)
                .expect("valid syntax tree");
        }
        visitor
            .features
            .array_sorts
            .sort_by_key(|(i, v)| (i.to_string(), v.to_string()));
        visitor.features.array_sorts.dedup();
        visitor.features.array_extensions.sort();
        visitor.features.array_extensions.dedup();
        visitor.features
    }

    pub fn has_arrays(&self) -> bool {
        !self.array_sorts.is_empty()
    }
    pub fn has_quantifiers(&self) -> bool {
        self.forall + self.exists > 0
    }
}

struct Inventory {
    features: TheoryFeatures,
    builder: SyntaxBuilder,
}

impl Rewriter for Inventory {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;
    fn visitor(&mut self) -> &mut SyntaxBuilder {
        &mut self.builder
    }

    fn process_sort(&mut self, sort: Sort) -> Result<Sort, Self::Error> {
        let identifier = match &sort {
            Sort::Simple { identifier } | Sort::Parameterized { identifier, .. } => identifier,
        };
        let name = match identifier {
            Identifier::Simple { symbol } | Identifier::Indexed { symbol, .. } => &symbol.0,
        };
        match name.as_str() {
            "Array" => {
                if let Sort::Parameterized { parameters, .. } = &sort {
                    if parameters.len() == 2 {
                        self.features
                            .array_sorts
                            .push((parameters[0].clone(), parameters[1].clone()));
                    }
                }
            }
            "Int" => self.features.integers = true,
            "Real" => self.features.reals = true,
            "BitVec" => self.features.bitvectors = true,
            "String" => self.features.strings = true,
            "FloatingPoint" | "Float16" | "Float32" | "Float64" | "Float128" | "RoundingMode" => {
                self.features.floating_point = true
            }
            "List" if matches!(&sort, Sort::Parameterized { .. }) => {
                self.features.parameterized_lists = true
            }
            _ => {}
        }
        Ok(sort)
    }

    fn process_qual_identifier(
        &mut self,
        id: QualIdentifier,
    ) -> Result<QualIdentifier, Self::Error> {
        // The bit-pattern constructor can appear without a declared FP sort.
        if id.get_name() == "fp" {
            self.features.floating_point = true;
        }
        if let QualIdentifier::Simple {
            identifier: Identifier::Indexed { symbol, .. },
        } = &id
        {
            if matches!(
                symbol.0.as_str(),
                "+zero"
                    | "-zero"
                    | "+oo"
                    | "-oo"
                    | "NaN"
                    | "to_fp"
                    | "to_fp_unsigned"
                    | "fp.to_ubv"
                    | "fp.to_sbv"
            ) {
                self.features.floating_point = true;
            }
            if matches!(symbol.0.as_str(), "map" | "as-array") {
                self.features.array_extensions.push(symbol.0.clone());
            }
            if symbol
                .0
                .strip_prefix("bv")
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|c| c.is_ascii_digit()))
            {
                self.features.bitvectors = true;
            }
        }
        Ok(id)
    }

    fn process_term(&mut self, term: Term) -> Result<Term, Self::Error> {
        match &term {
            Term::Application {
                qual_identifier, ..
            } if qual_identifier.get_name() == "to_real" => self.features.reals = true,
            Term::Application {
                qual_identifier, ..
            } if qual_identifier.get_name() == "to_int" => self.features.integers = true,
            Term::Application {
                qual_identifier, ..
            } if matches!(
                qual_identifier.get_name().as_str(),
                "*" | "/" | "div" | "mod"
            ) =>
            {
                self.features.nonlinear_arithmetic = true;
                self.features.reals |= qual_identifier.get_name() == "/";
            }
            Term::Forall { .. } => self.features.forall += 1,
            Term::Exists { .. } => self.features.exists += 1,
            Term::Lambda { .. } => self.features.lambdas += 1,
            Term::Constant(Constant::Hexadecimal(_) | Constant::Binary(_)) => {
                self.features.bitvectors = true
            }
            Term::Constant(Constant::Numeral(_)) => self.features.integers = true,
            Term::Constant(Constant::Decimal(_)) => self.features.reals = true,
            Term::Constant(Constant::String(_)) => self.features.strings = true,
            _ => {}
        }
        Ok(term)
    }

    fn process_command(&mut self, command: Command) -> Result<Command, Self::Error> {
        self.features.sort_aliases |= matches!(command, Command::DefineSort { .. });
        Ok(command)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn analyze(source: &str) -> TheoryFeatures {
        let commands = crate::CommandStream::new(source.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        TheoryFeatures::analyze(&commands)
    }

    #[test]
    fn detects_nested_arrays_and_binders_in_definitions_and_axioms() {
        let features = analyze("(declare-sort node 0)
            (define-sort Table () (Array node (Array (_ BitVec 8) Bool)))
            (define-fun helper () Bool (forall ((a (Array Int Bool))) (exists ((i Int)) (select a i))))
            (assert (forall ((n node)) true))");
        assert_eq!(features.array_sorts.len(), 3);
        assert_eq!((features.forall, features.exists), (2, 1));
        assert!(features.integers && features.bitvectors && features.sort_aliases);
    }

    #[test]
    fn names_and_logic_headers_do_not_imply_theories() {
        let features = analyze(
            "(set-logic AUFLIA) (declare-sort Array_Int_Int 0)
            (declare-fun bv_name () Bool) (assert bv_name)",
        );
        assert!(!features.has_arrays() && !features.bitvectors && !features.integers);
        assert!(!features.has_quantifiers());
    }

    #[test]
    fn theory_literals_need_no_declarations() {
        let features = analyze(
            "(assert (= (_ bv0 8) (_ bv1 8)))
            (assert (= 1 2))",
        );
        assert!(features.bitvectors && features.integers);
    }
}
