# Yardbird architecture for benchmark investigations

Yardbird is a Rust CEGAR verifier for VMT transition systems. src/main.rs selects
VMT or SMT-LIB execution; src/lib.rs defines CLI options and constructs strategies.
The investigator currently accepts array VMT benchmarks only.

src/driver.rs orchestrates BMC depth and refinement loops. It unrolls the transition
system, asks the solver about the negated property, and dispatches to the strategy.
UNSAT completes a bounded depth. SAT can trigger abstraction refinement or a
concrete counterexample check; successful bounded exploration is not an unbounded
proof. The default inner refinement budget is 250. Cooperative timeout checkpoints
occur between high-level actions. Controlled loop errors retain partial profiling.

src/vmt_bmc_session.rs owns incremental solver state, assertions and frame-indexed
instantiations. src/problem_context.rs is the strategy-facing interface; src/solver/
provides backends and property-check modes. smt2parser/src/vmt/bmc.rs handles frame
indexing. Solver unknown, no progress and refinement exhaustion are inconclusive.

src/strategies/array_abstract.rs builds a model-derived e-graph, finds violated
axiom/binder instances, ranks them, and installs selected constraints. Native array
operations are abstracted into uninterpreted functions. src/theories/array/ holds
array axioms, e-graph admission policies, quantified search, candidate generation,
term extraction and complete-instantiation ranking. Cost factories live under
src/cost_functions/array/. Candidate-winners-per-group bounds selected instances;
term cost and whole-instance ranker are separate tuning dimensions.

src/quantifier_abstraction.rs lowers input binders and coordinates their search.
Matching can page through substitutions and stop at explicit search-work limits.
Model filtering happens before expensive ranked grounding. Source-first or
cone-first admission widens to full admission when needed. Profiles can separate
matching, model preparation/filtering, extraction, grounding and solver cost.

src/strategies/array_concrete.rs delegates native arrays directly to the solver.
A large concrete/abstract gap may indicate refinement overhead, poor batch choices,
or an abstraction/search bottleneck; it does not by itself establish which cause.

src/profiling.rs defines the raw profiler schema. src/instantiation_provenance.rs
and src/training/ carry additional decision/instance provenance. The investigator
uses --profile, not database training or full decision logging. Garden is the
existing matrix benchmark runner; the investigator is a separate Python harness
for experiment lineage, compressed profiles and bounded agent investigation.
