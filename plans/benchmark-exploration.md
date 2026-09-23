# Implementation plan: Yardbird benchmark investigation agent

The core design should be a **benchmark investigation harness**, not a general-purpose coding-agent system. Every benchmark gets a logical agent with 15 Yardbird executions, but all agents share one pinned Yardbird binary, one Z3 installation, one source checkout, and a bounded execution pool.

The agent's job is to use CLI experimentation plus profiling and read-only source inspection to answer:

> Why is this benchmark expensive, what configuration behaves best, and what code-level change is most likely to improve it?

The individual configurations are evidence toward that answer.

## 1. Campaign architecture

I would build this as a Python tool living alongside Yardbird, roughly:

```text
tools/benchmark_investigator/
    cli.py
    models.py
    campaign.py
    scheduler.py
    runner.py
    summarizer.py
    profile_query.py
    agent.py
    codex_backend.py
    source_access.py
    findings.py
```

The overall flow is:

```text
                       Campaign Manager
                              │
                  ┌───────────┴───────────┐
                  │  ~40 Benchmark States │
                  └───────────┬───────────┘
                              │
                    agent requests RUN
                              │
                              ▼
                        Shared Run Queue
                              │
                    ┌─────────┴─────────┐
                    │ N execution slots │
                    └─────────┬─────────┘
                              │
                              ▼
                     Shared Yardbird Binary
                              │
                         --profile JSON
                              │
                  ┌───────────┴───────────┐
                  ▼                       ▼
             raw profile             summarizer
                                          │
                                    summary.json
                                          │
                                          ▼
                                    benchmark agent
                                          │
                         RUN / ANALYZE / INSPECT / FINISH
```

Crucially, there are **40 logical agents, not 40 continuously running processes**.

An agent invocation ends whenever it decides on its next action. If it chooses `RUN`, the orchestrator queues the experiment and Codex is no longer active while Yardbird spends up to five minutes running.

That keeps LLM usage concentrated on reasoning rather than waiting.

---

# 2. Build Yardbird once

Because Phase 1 does not permit code changes, we can eliminate almost all of the worktree/build problem.

At campaign startup:

```bash
cargo build --release
```

Then every experiment invokes the same binary directly:

```bash
target/release/yardbird ...
```

not:

```bash
cargo run --release ...
```

The campaign records:

```text
Yardbird git SHA
Yardbird binary hash
Z3 version
host identifier
campaign configuration
```

All benchmark agents inspect the same source checkout read-only.

There should be **no worktrees at all in Phase 1**.

---

# 3. Benchmark execution policy

Each benchmark gets exactly **15 Yardbird executions**.

Runs 1 and 2 are mandatory:

| Run  | Configuration               |
| ---- | --------------------------- |
| 1    | Canonical abstract baseline |
| 2    | Concrete reference          |
| 3–15 | Agent-selected experiments  |

The canonical baseline will be:

```bash
--strategy abstract
--cost-function protocol-bmc
--egraph-builder source-then-full
--candidate-winners-per-group 20
--instantiation-ranker prefer-source
--property-check-mode assumptions
--profile
-d 20
```

I'm assuming `protocol-bmc` is the literal CLI value because that is what the help output lists, despite us referring conversationally to "protocol-bmc-cost."

The concrete reference is:

```bash
--strategy concrete
--profile
-d 20
```

with any applicable property-check setting kept consistent.

Every execution gets:

```text
target depth:       20
wall-clock timeout: 300 seconds
```

The agent cannot modify the strategy during adaptive tuning. `concrete` is a diagnostic/reference run rather than part of the optimization space.

---

# 4. Allowed adaptive search space

Only these five dimensions are tunable:

```text
cost_function
egraph_builder
candidate_winners_per_group
instantiation_ranker
property_check_mode
```

Domains:

```yaml
cost_function:
  - bmc-cost
  - protocol-bmc
  - ast-size
  - adaptive-cost
  - split-cost
  - prefer-read
  - prefer-write
  - prefer-constants
  - index-aware
  - generated
  # logistic-regression only if ranker model is configured

egraph_builder:
  - full
  - source-then-full
  - cone-then-full

candidate_winners_per_group:
  - 1
  - 2
  - 5
  - 10
  - 20
  - 50

instantiation_ranker:
  - term-cost
  - prefer-source

property_check_mode:
  - scoped
  - assumptions
  - refinement-assumptions
```

Every adaptive `RUN` identifies a `parent_run_id`.

The orchestrator resolves the proposed patch against that parent and rejects it if more than **three of the five dimensions change**.

For example:

```json
{
  "parent_run_id": "german-r04-8a13c2",
  "config_patch": {
    "cost_function": "index-aware",
    "candidate_winners_per_group": 5,
    "egraph_builder": "cone-then-full"
  }
}
```

is legal.

Changing a candidate-winner value from 1 to 50 still counts as changing one dimension.

---

# 5. Run ranking

We should avoid inventing one artificial numeric score. Use a lexicographic ordering.

For runs that finish or reach depth 20:

```text
1. lower wall-clock time
2. lower solver time
```

For timed-out runs:

```text
1. deepest completed BMC depth
2. current depth/refinement progress
3. lower accumulated solver time
4. other diagnostics
```

Instantiation count is recorded but is not a primary optimization objective.

A concrete run that does:

```text
concrete: 4 seconds, depth 20
abstract: timeout, depth 12
```

should automatically receive a prominent diagnostic flag:

```text
LARGE_CONCRETE_ABSTRACT_GAP
```

That is exactly the kind of benchmark we want to investigate further.

---

# 6. Yardbird profiling changes

This is the first Yardbird-side implementation task.

The current profile data is already extremely rich. It has run-level instantiations/refinement counts, detailed driver timing, e-graph/rule-search information, and solver-check statistics.  The refinement profiling already includes timing categories, candidate filtering, e-graph sizes, substitutions, generated/selected candidates, and per-rule breakdowns. 

We should therefore **extend the profiler rather than redesign it**.

The important missing timeout behavior is that Yardbird needs to terminate gracefully enough to serialize useful state.

I would add an internal option roughly equivalent to:

```text
--wall-timeout-secs 300
```

rather than relying exclusively on `timeout(1)` killing the process.

When the deadline expires, the result should include:

```json
{
  "termination_reason": "timeout",
  "elapsed_wall_secs": 300.001,
  "deepest_completed_depth": 11,
  "current_depth": 12,
  "current_refinement_step": 7
}
```

Then Yardbird exits normally and writes its profile.

The orchestrator should still impose an external safety kill, perhaps around 310 seconds, in case Yardbird gets stuck somewhere that does not observe the cooperative timeout.

We may also need a small profiling addition for **per-quantifier instantiation counts**. The existing profile exposes quantifier-related rule names and used instances, but I would rather have an explicit aggregation than make the summarizer reverse-engineer quantifier names from strings.

---

# 7. Artifact layout

Every run gets its own immutable directory.

For example:

```text
campaigns/
└── 2026-09-yardbird-investigation/
    ├── campaign.json
    ├── campaign.sqlite
    ├── context/
    │   ├── YARDBIRD_ARCHITECTURE.md
    │   ├── EXPERIMENT_PROTOCOL.md
    │   └── PROFILING_GUIDE.md
    │
    ├── benchmarks/
    │   └── german/
    │       ├── benchmark.json
    │       ├── runs/
    │       │   ├── german-r01-a83f01/
    │       │   │   ├── action.json
    │       │   │   ├── config.json
    │       │   │   ├── stdout.log
    │       │   │   ├── stderr.log
    │       │   │   ├── profile.json
    │       │   │   ├── summary.json
    │       │   │   └── summary.md
    │       │   └── ...
    │       │
    │       ├── agent-events.jsonl
    │       └── FINDINGS-german.md
    │
    └── FINDINGS/
        ├── FINDINGS-german.md
        └── ...
```

The filesystem holds the large artifacts.

SQLite holds searchable metadata and relationships.

---

# 8. Run lineage and auditability

Every run needs a stable ID and parent.

The database record should look conceptually like:

```text
run_id
benchmark_id
ordinal
parent_run_id

strategy
cost_function
egraph_builder
candidate_winners_per_group
instantiation_ranker
property_check_mode

agent_hypothesis
agent_rationale
expected_signal

started_at
finished_at
wall_time
termination_reason

completed_depth
current_depth
current_refinement_step

solver_time
profile_path
summary_path
```

That gives us an actual **experiment tree**.

We should deliberately store the agent's concise hypothesis and explanation, rather than trying to preserve hidden model chain-of-thought.

Example:

```text
Hypothesis:
cone-then-full may reduce e-graph construction overhead because
the profile shows rapid admission of unrelated terms after depth 8.

Expected signal:
lower egraph_build time and fewer nodes without losing depth progress.
```

That is much more useful later anyway.

---

# 9. Compressed profile schema

`summary.json` should be deterministic: generated by code, not by the LLM.

I would organize it roughly as:

```json
{
  "outcome": {},
  "progress": {},
  "timing": {},
  "depths": [],
  "refinement": {},
  "solver": {},
  "egraph": {},
  "rules": [],
  "quantifiers": [],
  "events": []
}
```

### Outcome

```text
termination reason
wall time
proof/counterexample status
target depth
deepest completed depth
current refinement
```

### Per-depth information

For each depth:

```text
number of refinement iterations
time spent
solver time
instances added
e-graph growth
candidate counts
```

This lets the agent see things like:

```text
depth 0–6: one refinement/depth
depth 7:   three refinements
depth 8:   nine refinements
depth 9:   two refinements
```

without reading thousands of lines.

### Timing

Aggregate **every profiling timing category** across the run:

```text
driver_step_total
strategy_sat
strategy_unsat
check_solver
check_capture_model
egraph_build
extractor_init
rule_search_total
instantiation_total
input_binder_prepare
...
```

For each:

```text
total
percentage of measured time
max single event
depth/refinement where max occurred
```

### Rules

Aggregate per rule:

```text
search time
apply time
search calls
apply calls
matches
substitutions
substitutions explored
candidates generated
candidates selected
```

Then rank by:

```text
total time
substitutions explored
candidate generation
```

### Quantifiers

Per quantified input binder:

```text
matches
instantiations proposed
instantiations selected
model-filtered
depth distribution
```

### E-graph

Track:

```text
classes
nodes
newly admitted subterms
rule-search rounds
growth by depth
peak size
largest single growth event
```

### Solver

Aggregate:

```text
solver time
number of checks
SAT checks
UNSAT checks
conflicts
decisions
propagations
restarts
rlimit
max individual check time
```

The profile already records individual solver checks with depth/refinement, result, assertions, timing, and statistic deltas, so these aggregates can remain entirely deterministic. 

### Important events

Keep a small set such as:

```text
5 slowest driver steps
5 slowest solver checks
5 largest e-graph expansions
5 largest candidate explosions
5 refinement steps producing most instantiations
```

That gives the agent specific places to investigate.

---

# 10. Agent-facing `summary.md`

The JSON is for machines. We should also create a concise text representation for Codex.

Something like:

```text
RUN german-r07
Config:
  cost=index-aware
  egraph=cone-then-full
  winners=5
  ranker=prefer-source
  property=assumptions

Outcome:
  TIMEOUT 300.0s
  completed depth: 14
  current: depth 15 refinement 3
  baseline completed depth: 10

Timing:
  strategy_sat       231.2s
  egraph_build        28.1s
  extractor_init      16.7s
  solver              11.4s

Growth:
  depth 12: 3 refinements
  depth 13: 6
  depth 14: 11
  depth 15: 4+ before timeout

Dominant rules:
  write-does-not-overwrite  61% rule time
  read-after-write          29%

Quantifiers:
  q_4: 48% selected instances
  q_1: 31%

EGraph:
  peak nodes: 18,302
  growth accelerates at depth 13

Notable events:
  depth 14/ref 7: 42.1s strategy_sat
  depth 15/ref 2: +3,819 egraph nodes
```

That is what the agent should see by default.

---

# 11. Profile drill-down API

Raw profiles remain on disk and are never automatically put into context.

The agent gets an explicit action:

```text
ANALYZE_PROFILE
```

with structured arguments such as:

```json
{
  "action": "ANALYZE_PROFILE",
  "run_id": "german-r07",
  "view": "refinement",
  "filters": {
    "depth": 14,
    "refinement_step": 7
  },
  "question": "Why was this refinement much slower than neighboring steps?"
}
```

Possible views:

```text
overview
depth
refinement
timing
rules
quantifiers
egraph
solver
events
```

The profile-query layer extracts only the relevant material and feeds that back to Codex.

This should substantially reduce token use.

---

# 12. Agent action protocol

The agent should not control a shell directly for experiments.

Define an enum:

```text
RUN
ANALYZE_PROFILE
INSPECT_SOURCE
FINISH
```

### `RUN`

Requires:

```text
parent_run_id
config_patch
hypothesis
expected_signal
rationale
```

The orchestrator validates the configuration.

### `ANALYZE_PROFILE`

Requires:

```text
run_id
view
optional filters
question
```

### `INSPECT_SOURCE`

Read-only.

For example:

```json
{
  "action": "INSPECT_SOURCE",
  "mode": "search",
  "query": "strategy_sat",
  "reason": "Determine which operations dominate the timing category"
}
```

or:

```json
{
  "action": "INSPECT_SOURCE",
  "mode": "read",
  "path": "src/...",
  "start_line": 200,
  "end_line": 320
}
```

Paths must resolve inside the pinned Yardbird checkout.

### `FINISH`

The agent indicates it has enough evidence.

The orchestrator then asks it for the final findings document.

All responses should validate against a Pydantic model before execution.

---

# 13. Agent context

You will provide:

```text
YARDBIRD_ARCHITECTURE.md
```

I would create two additional static documents.

`EXPERIMENT_PROTOCOL.md` explains:

```text
goal
15-run budget
300s/run
depth-20 target
five tunable knobs
three-knob change limit
baseline
concrete reference
ranking objective
available actions
what constitutes a useful finding
```

`PROFILING_GUIDE.md` explains what the major profile categories mean.

The dynamic context for each invocation should contain only:

```text
benchmark name/path
runs remaining
baseline result
concrete result
compact table of all experiments
best-performing configurations
agent's previously recorded hypotheses/findings
result of the most recent requested action
```

Do not repeatedly inject every prior profile.

---

# 14. Agent search behavior

After the first two runs, I would **not prescribe a rigid optimizer**.

The prompt should explicitly tell the agent it is conducting an investigation.

It can:

```text
try a parameter change
compare profiles
inspect implementation
form a hypothesis
try a three-way interaction
return to an earlier branch
spend a turn analyzing without running anything
```

The important constraint is that only `RUN` consumes one of its 15 execution slots.

This lets an agent spend meaningful reasoning time between expensive experiments without sacrificing benchmark executions.

---

# 15. Scheduler and resource isolation

We can postpone the exact concurrency number as discussed.

Campaign config should simply expose:

```yaml
scheduler:
  max_parallel_runs: 8
  cpus_per_run: 4
  memory_per_run_gb: 8
```

Those numbers are placeholders.

The scheduler:

```text
accepts jobs from benchmark agents
queues them
assigns a worker slot
assigns a CPU set
runs Yardbird
returns results
```

The initial implementation can use `asyncio` plus a semaphore.

Later we can enforce CPU affinity/cgroups without changing the agent architecture.

One additional rule I would add: **never run two confirmation/timing-sensitive executions for the same benchmark concurrently.**

---

# 16. Codex integration

Wrap Codex behind:

```python
class AgentBackend:
    def decide(self, context: AgentContext) -> AgentAction:
        ...
```

Initial implementation:

```text
CodexCLIBackend
model/reasoning profile: Astra High
```

Treat the exact Codex model selector as configuration rather than hardcoding it into campaign logic.

Codex should run with:

```text
read access:
  Yardbird source
  architecture docs
  benchmark summaries
  requested profile slices

write access:
  ideally only its response/output area

no authority:
  edit Yardbird
  execute arbitrary experimental configs
  bypass experiment validation
```

The orchestrator remains authoritative.

---

# 17. Final findings document

Each benchmark must terminate by producing:

```text
FINDINGS-{benchmark-name}.md
```

Keep these deliberately compact—ideally around 1–3 pages, not a transcript.

I would use this template:

```markdown
# Findings: german

## Executive summary

Short explanation of why this benchmark behaves the way it does.

## Baseline behavior

- abstract baseline:
- concrete reference:
- most important contrast:

## Best configuration

CLI configuration and resulting progress/runtime.

## Profiling diagnosis

The 3–5 most important observations from the profile.

## Parameter sensitivity

Which settings materially helped or hurt and likely why.

## Primary implementation recommendation

One concrete Yardbird code-level recommendation.

Explain:
- suspected bottleneck
- relevant subsystem/files
- why the profile supports it
- which benchmarks/patterns it may generalize to

## Confidence / unresolved questions

What the agent believes strongly and what remains uncertain.
```

No run-by-run diary.

No giant tables.

The evidence remains available through run IDs if we want to drill down later.

---

# 18. Cross-benchmark synthesis

Once all ~40 reports exist:

```text
FINDINGS-*.md
        │
        ▼
large-context synthesis agent
        │
        ▼
SYNTHESIS.md
```

Its job is to identify recurring implementation recommendations, benchmark clusters, configuration patterns, concrete-vs-abstract gaps, and likely high-leverage general changes.

For example:

```text
14/40 benchmarks:
  e-graph admission dominates
  → likely common optimization

9/40:
  write-does-not-overwrite search explosion
  → likely pruning opportunity

6/40:
  concrete dramatically outperforms abstract
  → abstraction path deserves investigation

4/40:
  Z3 itself dominates
  → lower priority for Yardbird-side optimization
```

Only after that synthesis would I return to the original idea of making code changes.

---

# 19. Implementation order

I would build this in eight stages.

### Stage 1 — Timeout-safe Yardbird profiles

Add cooperative wall-clock timeout and progress fields.

**Acceptance criterion:** killing a 300-second run produces a valid profile containing completed depth and current refinement step.

### Stage 2 — Single-run harness

Implement:

```bash
investigator run <benchmark> <config>
```

It creates the run directory, invokes the prebuilt binary, times it, and saves all artifacts.

**Acceptance criterion:** one command produces reproducible `config.json`, `profile.json`, stdout/stderr, and run metadata.

### Stage 3 — Profile summarizer

Use the uploaded profile as an initial test fixture.

Generate:

```text
summary.json
summary.md
```

**Acceptance criterion:** we can inspect a profile without needing the original 6,000-line file.

### Stage 4 — Profile query system

Implement selective drill-down into:

```text
depths
refinements
rules
quantifiers
solver
egraph
events
```

### Stage 5 — Campaign database and scheduler

Implement benchmark states, run queue, run budget, lineage, and concurrency limits.

At this point we can already manually launch a 40-benchmark campaign without any agents.

### Stage 6 — Agent protocol

Implement the four action types, validation, three-parameter-change rule, context generation, and experiment history.

Use a fake/mock agent initially.

### Stage 7 — Codex backend

Connect Codex CLI/Astra High.

Run a single benchmark end-to-end:

```text
baseline
concrete
adaptive experiments
profile analysis
source inspection
FINDINGS.md
```

### Stage 8 — Pilot and scale

First:

```text
3 representative benchmarks
```

I would choose:

```text
one relatively easy
one 300s timeout
one with a major concrete/abstract discrepancy
```

Tune the summarizer and prompt based on those results.

Then scale to all ~40.

---

# 20. What I would *not* build yet

I would deliberately defer:

```text
Git worktrees
agent-written code changes
Docker-per-agent
distributed execution
web UI
complex hyperparameter algorithms
automatic patch synthesis
heavy resumability infrastructure
confirmation-run machinery
```

None of those are necessary to answer the research question.

The first version can be a CLI plus SQLite plus files.

---

# 21. Biggest implementation risk

The most important risk is not Codex or scheduling. It's **whether the compressed profiler exposes enough causal information for the agent to distinguish symptoms from causes**.

For that reason, I would expect `summarizer.py` and `PROFILING_GUIDE.md` to evolve significantly during the three-benchmark pilot.

That's fine. The raw profiles remain canonical, so we can change the summary representation without rerunning experiments.

---

## Final clarifications

I don't think I need any additional answers from you before implementation.

There are three minor implementation details that can be resolved directly from the Yardbird code rather than through more Q&A:

* exactly how `--profile` currently gets serialized/output;
* whether explicit per-quantifier counts already exist somewhere in the profile internals;
* the exact Codex CLI selector corresponding to your desired **Astra High** configuration.

The only input I'd need from you before starting the agent portion is the `YARDBIRD_ARCHITECTURE.md` document you said you can create. Everything before that—timeout support, runner, profile summarizer, storage, query system, and scheduler—can be built independently.
