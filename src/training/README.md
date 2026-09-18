# Policy observations

Use `--profile --json-output` to inspect policy work without a database. Use a
build with `--features training` and `--train` to persist observations through the
existing training logger. `--train` automatically enables profiling and candidate
capture; it does not require an additional `--profile` flag. Supply the database
URL through `YARDBIRD_DATABASE_URL` or `--database-url`.

For a bounded VMT experiment:

```sh
cargo run --features training --release -- \
  -f examples/array/array_copy.vmt -d 3 \
  --train --training-run-version policy-experiment-1 \
  --wall-timeout-secs 60 --json-output
```

Migration `007_policy_trace` runs with the existing training migrations. The
policy observation format currently has schema version 1.

| Table | Observations |
| --- | --- |
| `effort_decisions` | Offered and chosen symbolic operations, parent/page links, model and graph versions, pending selections, allowances, choice/work time, work report and stop reason |
| `effort_candidates` | Candidate identities and selection at each decision; optional link to an existing abstract-instantiation row |
| `policy_installations` | Installation attempts, including normalization failure, materialization and deduplication results |
| `policy_solver_checks` | Refinement-query SAT/UNSAT/UNKNOWN, assertion counts, solver settings, timings and statistics |
| `policy_run_outcomes` | Termination, progress, totals and input-quantifier source provenance |

Every row belongs to a benchmark. Decision, check, model and graph indices are
local to that run. Match identities use symbolic formulas, signed alternatives,
bindings and source provenance; transient operation handles and e-class IDs are
not used as persistent effort identities. A candidate rejected before retention
can have a null abstract-instantiation database link; its symbolic details remain
in the decision's JSON record.

A decision links to the check whose model it examined and the next observed
check, if any. Installation attempts use the same check links. Multiple empty
passes can share one preceding check. An action at timeout can have no subsequent
check. Actual installation results distinguish a selected candidate from an
assertion added to the solver. Guarded-read installation attempts have a symbolic
term but no abstract candidate ID.

Read decision rows in `decision_index` order. Enclosing decisions precede their
binder pages; page rows point to `parent_decision_index`. Operation timings include
nested pages and page-choice time, so do not sum parent and child durations.
`choice_elapsed_secs` records the policy call separately. Search reports separate
matcher output examined, including prefix replay and lookahead, from fresh page
substitutions passed to grounding. These counters do not measure every internal
matching operation.

The trace records observed sequencing and accumulated solver context. A next
UNSAT check is not evidence that the preceding action would have succeeded first,
or that it deserves all proof credit. Compare alternate orderings in separate
runs. No reward function is assigned here.

Cooperative timeouts and refinement failures retain partial traces. The logger
persists at run finalization; killing the process before finalization cannot flush
its in-memory observations. Ordinary runs without profiling, training or solver
capture leave detailed tracing disabled.
