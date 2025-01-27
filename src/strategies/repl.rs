use std::iter;

use dialoguer::{
    theme::{ColorfulTheme, SimpleTheme},
    MultiSelect, Select,
};
use egg::{Language, Searcher};
use itertools::Itertools;
use rustyline::{
    completion::Completer, error::ReadlineError, highlight::MatchingBracketHighlighter,
    history::History, validate::MatchingBracketValidator, Editor, Helper,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter, Validator};
use smt2parser::vmt::VMTModel;

use crate::{
    array_axioms::{not_equal, ArrayExpr, ArrayLanguage, ArrayPattern, ConditionalSearcher},
    strategies::{AbstractRefinementState, ProofStrategyExt},
};

pub struct Repl;

enum Action {
    Continue,
    Filter,
    Custom,
    Query,
}

const ACTIONS: &[Action] = &[
    Action::Continue,
    Action::Filter,
    Action::Custom,
    Action::Query,
];

impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Action::Continue => write!(f, "Continue as normal"),
            Action::Filter => write!(f, "Filter instantiations"),
            Action::Custom => write!(f, "Enter custom instantiations"),
            Action::Query => write!(f, "Query egraph"),
        }
    }
}

#[derive(Helper, Completer, Hinter, Validator, Highlighter, Default)]
struct ReplHelper {
    #[rustyline(Completer)]
    completer: CommandCompleter,
    #[rustyline(Highlighter)]
    highlighter: MatchingBracketHighlighter,
    #[rustyline(Validator)]
    validator: MatchingBracketValidator,
    #[rustyline(Hinter)]
    hinter: (),
}

#[derive(Default)]
struct CommandCompleter;

impl Completer for CommandCompleter {
    type Candidate = String;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        ctx: &rustyline::Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Self::Candidate>)> {
        let _ = (line, pos, ctx);
        let commands = [
            ":exit",
            ":eclass",
            ":axiom read-after-write",
            ":axiom write-does-not-overwrite",
            ":insts",
        ];
        Ok((
            0,
            commands
                .iter()
                .filter(|cand| cand.starts_with(line))
                .map(ToString::to_string)
                .collect(),
        ))
    }
}

impl ProofStrategyExt<AbstractRefinementState> for Repl {
    #[allow(clippy::print_stdout)]
    fn finish(
        &mut self,
        _model: &mut VMTModel,
        state: &mut AbstractRefinementState,
    ) -> anyhow::Result<()> {
        println!("Found instantiations:");
        for (i, inst) in state.instantiations.iter().enumerate() {
            let index_str = format!("[{i}] ");
            let spacing = format!("\n{}", iter::repeat_n(" ", index_str.len()).join(""));
            println!("{index_str}{}", inst.pretty(80).split("\n").join(&spacing))
        }

        let mut rl = Editor::new()?;
        rl.set_helper(Some(ReplHelper::default()));

        let action = Select::with_theme(&ColorfulTheme::default())
            .with_prompt("What should we do?")
            .items(ACTIONS)
            .default(0)
            .interact()
            .unwrap();

        match ACTIONS[action] {
            Action::Continue => Ok(()),
            Action::Filter => {
                if state.instantiations.is_empty() {
                    return Ok(());
                }

                let selection = MultiSelect::with_theme(&SimpleTheme)
                    .with_prompt("Pick instantiations")
                    .items_checked(
                        &state
                            .instantiations
                            .iter()
                            .map(|x| (x.clone(), true))
                            .collect_vec(),
                    )
                    .interact()
                    .unwrap();

                // replace instantiations with instantiations from selection
                state.instantiations = selection
                    .into_iter()
                    .map(|i| state.instantiations[i].clone())
                    .collect();

                Ok(())
            }
            Action::Custom => todo!(),
            Action::Query => loop {
                match egraph_repl(&mut rl, state) {
                    Ok(cont) if !cont => break Ok(()),
                    Ok(_) => (),
                    Err(err) => {
                        println!("{err}");
                    }
                }
            },
        }
    }
}

#[allow(clippy::print_stdout)]
fn egraph_repl<H, I>(
    rl: &mut rustyline::Editor<H, I>,
    state: &AbstractRefinementState,
) -> anyhow::Result<bool>
where
    H: Helper,
    I: History,
{
    match rl.readline("query> ") {
        Ok(query) if query.starts_with(":") => {
            let parts: Vec<_> = query.split_whitespace().collect();
            match parts.as_slice() {
                [":exit" | ":quit" | ":q"] => Ok(false),
                [":eclass", id] => {
                    let parsed_id: usize = id.parse()?;
                    let nodes = state.egraph[egg::Id::from(parsed_id)]
                        .nodes
                        .iter()
                        .map(|node| {
                            if node.is_leaf() {
                                format!("{node}")
                            } else {
                                format!("({node} {})", node.children().iter().join(" "))
                            }
                        })
                        .join(", ");
                    println!("[{nodes}]");
                    Ok(true)
                }
                [":axiom", "read-after-write"] => {
                    let parsed: ArrayPattern =
                        "(Read-Int-Int (Write-Int-Int ?a ?idx ?val) ?idx)".parse()?;
                    for m in egg::Pattern::new(parsed).search(&state.egraph) {
                        println!(" {}: {:?}", m.eclass, m.substs);
                    }
                    Ok(true)
                }
                [":axiom", "write-does-not-overwrite"] => {
                    let searcher = ConditionalSearcher::new(
                        "(Read-Int-Int (Write-Int-Int ?a ?idx ?val) ?c)"
                            .parse::<egg::Pattern<ArrayLanguage>>()
                            .unwrap(),
                        not_equal("?idx", "?c"),
                    );
                    for m in searcher.search(&state.egraph) {
                        println!(" {}: {:?}", m.eclass, m.substs);
                    }
                    Ok(true)
                }
                [":insts" | ":instantiations"] => {
                    println!("Found instantiations:");
                    for (i, inst) in state.instantiations.iter().enumerate() {
                        let index_str = format!("[{i}] ");
                        let spacing =
                            format!("\n{}", iter::repeat_n(" ", index_str.len()).join(""));
                        println!("{index_str}{}", inst.pretty(80).split("\n").join(&spacing))
                    }
                    Ok(true)
                }
                x => {
                    println!("Unknown command: {x:?}");
                    Ok(true)
                }
            }
        }
        Ok(query) => {
            if query.contains("?") {
                let parsed: ArrayPattern = query.parse()?;
                for m in egg::Pattern::new(parsed).search(&state.egraph) {
                    println!(" {}: {:?}", m.eclass, m.substs);
                }
            } else {
                let parsed: ArrayExpr = query.parse()?;
                println!("{:?}", state.egraph.lookup_expr(&parsed));
            }
            Ok(true)
        }
        Err(ReadlineError::Eof | ReadlineError::Interrupted) => Ok(false),
        Err(msg) => {
            println!("error: {msg}");
            Ok(true)
        }
    }
}
