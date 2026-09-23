# Yardbird architecture for benchmark investigations

Yardbird is a Rust CEGAR verifier for VMT transition systems. src/main.rs selects
VMT or SMT-LIB execution; src/lib.rs defines CLI options and constructs strategies.
The investigator currently accepts array VMT benchmarks only.

src/driver.rs orchestrates BMC depth and refinement loops. It unrolls the transition
system, asks the solver about the negated property, and dispatches to the strategy.
UNSAT completes a bounded depth. SAT can trigger abstraction refinement or a
concrete counterexample check; successful bounded exploration is not an unbounded
proof. The abstract strategy continues searching without a fixed refinement-step cap.
Cooperative timeout checkpoints
occur between high-level actions. Controlled loop errors retain partial profiling.

src/vmt_bmc_session.rs owns incremental solver state, assertions and frame-indexed
instantiations. src/problem_context.rs is the strategy-facing interface; src/solver/
provides backends and property-check modes. smt2parser/src/vmt/bmc.rs handles frame
indexing. Solver unknown, no progress and refinement exhaustion are inconclusive.

src/strategies/abstract.rs coordinates one model-equivalence graph, policy work,
and selected constraints. Native array operations are abstracted into uninterpreted
functions. src/theories/array/ owns array axioms, structural grounding, write-site
indexes and refinement. src/theories/quantifiers/ owns binder lowering, dependency
search, violation plans, paging, and refinement. Shared matching, representative
extraction and candidate construction live in src/rule_matching/; shared terms
live in src/terms/.

src/policy/effort.rs chooses work and allowances. Term-cost factories and heuristics
live under src/policy/term_selection/, while src/policy/instance_selection.rs owns
whole-instance ranking and batch selection. Candidate-winners-per-group sets the
initial allowance, which effort policy can widen. src/instance_installation/ owns
BMC placement, replay, assertion tracking, and frame-specific provenance.

Matching can page through substitutions and stop at explicit search-work limits.
Model filtering happens before expensive ranked grounding. Source-first or
cone-first admission widens to full admission when needed. Profiles can separate
matching, model preparation/filtering, extraction, grounding and solver cost.

src/strategies/array_concrete.rs delegates native arrays directly to the solver.
A large concrete/abstract gap may indicate refinement overhead, poor batch choices,
or an abstraction/search bottleneck; it does not by itself establish which cause.

src/profiling.rs defines the raw profiler schema. src/rule_matching/provenance.rs
and src/training/ carry additional decision/instance provenance. The investigator
uses --profile, not database training or full decision logging. Garden is the
existing matrix benchmark runner; the investigator is a separate Python harness
for experiment lineage, compressed profiles and bounded agent investigation.
