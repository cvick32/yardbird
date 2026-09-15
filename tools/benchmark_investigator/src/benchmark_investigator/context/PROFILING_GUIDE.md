# Profiling guide

Raw profile.json is canonical. summary.json and summary.md are deterministic.
The raw result includes run_progress, solver_statistics, instantiation totals,
driver records, refinement/cost records, and per-check solver records. A failed
process can still emit a useful profile; the exit code alone does not describe it.

Timers are nested and overlap: driver.strategy_sat includes refinement work;
refinement timers may include other refinement timers. Namespace prefixes preserve
their origin. Percentages use measured subprocess wall time, not the sum of all
timers. Do not add overlapping timers or interpret their percentages as a partition.
Solver timing_ns is converted to seconds; solver.raw_check excludes model capture,
property handling and statistics collection. Run-level solver_statistics may also
include concrete validation. Per-check totals describe the checks actually logged.
Statistic deltas are aggregated; gauge values such as memory or maxima are not
necessarily meaningful when summed. Consult run_statistics and individual checks.

Current matching and grounding timers are rule_matching_total and
rule_grounding_total. Older profiles may use rule_search_total. Continuations
available means another page can be searched; budget_exhausted means a work limit
was reached. Neither indicates logical completeness. Array rules and input binders
share matching, grounding and ranking machinery. Model filtering removes satisfied
matches before expensive representative extraction.

Depth summaries join records by zero-based depth. A refinement step may have
multiple cost records as the e-graph admission policy widens. E-graph sizes are
observed snapshots, not a lifetime memory measurement. Peak sizes and per-event
growth are diagnostics. Instances added counts indexed solver assertions, which
can differ from unique abstract formulas or selected candidates.

Profiles with quantifier_provenance join input-binder rule names to a run-level
source dictionary. Each source records the parsed formula before binder scoping,
its enclosing normalized VMT command, expression path, parent, and scoped variables.
Generated rules record helper/witness names and lowered-variable mappings. Property
Herbrand witnesses remain mapped even when no input-binder rule is generated.
These are structural locations, not input-file line numbers. Do not assume one
source quantifier produces exactly one rule, or that IDs are stable across edits.

Per-refinement quantifier_work records are keyed by rule and phase. They expose
matching, filtering, construction, evaluation and instantiation costs, plus cache
hits, filtered candidates, selected candidates and actual installation counts.
Model-evaluation time includes backend translation and conversion; filter time
contains construction/evaluation time. Counters for returned matches can include
prefix re-examination; they do not count unique bindings. Installation counters
are separate from selection and distinguish abstract instances from indexed assertions.
Older profiles without the dictionary remain explicitly unavailable.

ANALYZE_PROFILE can select overview, depth, refinement, timing, rules, quantifiers,
egraph, solver or events. Filter by depth/refinement and, for rule views, rule name. Quantifier views also accept a source ID in the rule filter.
Large responses explicitly truncate and ask for a narrower query.
