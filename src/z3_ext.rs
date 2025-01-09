use std::cmp;

use anyhow::anyhow;
use itertools::Itertools;

pub trait ModelExt {
    fn dump_sorted(&self) -> anyhow::Result<String>;

    /// Return an iterator over `z3::FuncDecl`s that is sorted by frame numbers (if
    /// applicable)
    fn sorted_iter(&self) -> impl Iterator<Item = z3::FuncDecl>;
}

impl ModelExt for z3::Model<'_> {
    fn dump_sorted(&self) -> anyhow::Result<String> {
        let mut b = String::new();
        for func_decl in self.iter().sorted_by(func_decl_cmp) {
            if func_decl.arity() == 0 {
                // VARIABLE
                // Apply no arguments to the constant so we can call get_const_interp.
                let func_decl_ast = func_decl.apply(&[]);
                let var_name = func_decl.name();
                let value = self.get_const_interp(&func_decl_ast).ok_or(anyhow!(
                    "Could not find interpretation for variable: {func_decl}"
                ))?;
                b.push_str(&format!("{var_name} -> {value}\n"));
            } else {
                // FUNCTION DEF
                let interpretation = self
                    .get_func_interp(&func_decl)
                    .ok_or(anyhow!("No function interpretation for: {func_decl}"))?;
                // b.push_str(&format!("{interpretation}\n"))
                for entry in interpretation.get_entries() {
                    let function_call = format!(
                        "{} {}",
                        func_decl.name(),
                        entry
                            .get_args()
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(" ")
                    );
                    let value = entry.get_value().to_string();
                    b.push_str(&format!("{function_call} -> {value}\n"));
                }
                b.push_str(&format!(
                    "{} else -> {}\n",
                    func_decl.name(),
                    interpretation.get_else()
                ))
            }
        }
        // let model_string = format!("{model}");
        Ok(b)
    }

    fn sorted_iter(&self) -> impl Iterator<Item = z3::FuncDecl> {
        self.iter().map(FuncDeclOrd).sorted().map(|x| x.0)
    }
}

pub struct FuncDeclOrd<'ctx>(pub z3::FuncDecl<'ctx>);

impl PartialOrd for FuncDeclOrd<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FuncDeclOrd<'_> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let arity_cmp = self.0.arity().cmp(&other.0.arity());
        if !matches!(arity_cmp, cmp::Ordering::Equal) {
            return self.0.name().cmp(&other.0.name());
        }

        let self_name = self.0.name();
        let other_name = other.0.name();
        let self_parts = self_name.split_once("@");
        let other_parts = other_name.split_once("@");

        match (self_parts, other_parts) {
            (None, None) => cmp::Ordering::Equal,
            (Some(_), None) => cmp::Ordering::Greater,
            (None, Some(_)) => cmp::Ordering::Less,
            (Some((av, an)), Some((bv, bn))) => match av.cmp(bv) {
                cmp::Ordering::Equal => {
                    let au32 = an.parse::<u32>().unwrap();
                    let bu32 = bn.parse::<u32>().unwrap();
                    au32.cmp(&bu32)
                }
                x @ (cmp::Ordering::Less | cmp::Ordering::Greater) => x,
            },
        }
    }
}

impl PartialEq for FuncDeclOrd<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.name() == other.0.name()
    }
}

impl Eq for FuncDeclOrd<'_> {}

fn func_decl_cmp(a: &z3::FuncDecl, b: &z3::FuncDecl) -> cmp::Ordering {
    let arity_cmp = a.arity().cmp(&b.arity());
    if !matches!(arity_cmp, cmp::Ordering::Equal) {
        return a.name().cmp(&b.name());
    }

    let a_name = a.name();
    let b_name = b.name();
    let a_parts = a_name.split_once("@");
    let b_parts = b_name.split_once("@");

    match (a_parts, b_parts) {
        (None, None) => cmp::Ordering::Equal,
        (Some(_), None) => cmp::Ordering::Greater,
        (None, Some(_)) => cmp::Ordering::Less,
        (Some((av, an)), Some((bv, bn))) => match av.cmp(bv) {
            cmp::Ordering::Equal => {
                let au32 = an.parse::<u32>().unwrap();
                let bu32 = bn.parse::<u32>().unwrap();
                au32.cmp(&bu32)
            }
            x @ (cmp::Ordering::Less | cmp::Ordering::Greater) => x,
        },
    }
}
