# Training Data Collection Scripts

Scripts for collecting training data for learning cost functions.

## Quick Start

```bash
# 1. Set up database and build
./scripts/setup-training.sh

# 2. Create database (if needed)
createdb yardbird_training

# 3. Update .env with your database URL
echo "YARDBIRD_DATABASE_URL=postgres://user:pass@localhost/yardbird_training" > .env

# 4. Run training data collection
./scripts/run-training.sh
```

## Scripts

### `setup-training.sh`
One-time setup script that:
- Creates `.env` file template
- Builds yardbird with training feature
- Builds garden
- Prints database setup instructions

### `run-training.sh`
Runs yardbird on all benchmarks with `--train` flag to collect training data.
The script now assigns one shared `TRAINING_RUN_VERSION` to the whole batch so
all benchmark rows land under the same logical training campaign.

**Options (via environment variables):**
```bash
# Examples directory (default: examples/array)
EXAMPLES_DIR=examples/list ./scripts/run-training.sh

# BMC depth (default: 10)
DEPTH=15 ./scripts/run-training.sh

# Timeout per benchmark in seconds (default: 60)
TIMEOUT=120 ./scripts/run-training.sh

# Strategy (default: abstract)
STRATEGY=concrete ./scripts/run-training.sh

# Cost functions to run (default: all)
COST_FUNCTIONS="bmc-cost ast-size" ./scripts/run-training.sh

# Stable training campaign identifier (default: generated timestamp)
TRAINING_RUN_VERSION=paper-baseline-v1 ./scripts/run-training.sh
```

## Quantified policy comparisons

`explore_quantified_policies.py` runs the same VMT inputs and bounds sequentially,
with an external timeout and atomically saved partial depth progress. Metadata
includes commands, input and binary hashes, source hashes, and the source revision.
Keep profiled diagnostics separate from timing comparisons.

The retained variants are:

| Variant | Configuration |
| --- | --- |
| `guided4096` | Existing guided search; supplement scheduling and 4,096 trace work |
| `guided4096-exact` | Scheduled exact grounding; retains the ring-leader depth gain despite other regressions |
| `guided4096-captures` | Prefer intact source capture tuples |
| `guided4096-frontiers` | Also reserve work for demanded read indices |
| `guided4096-read-support` | Also use read-index QIs and complete array-read equations |
| `guided4096-proved-prefix` | Also retain proved properties at their original frames |
| `guided4096-proved-instances` | Also instantiate certified universal properties, at most 512 per depth |
| `guided4096-split-properties` | Also prove top-level property conjuncts separately |
| `z3-assuming` | Native Z3 arrays and quantifiers, with property assumptions |

All the listed Yardbird variants explicitly use `--theory array,quantifiers`.
`guided4096-read-support` replaces the earlier support/read-binder/complete-read
switch combinations. Removed experiments remain documented in the findings;
their old commands require their archived binaries and source snapshots.

For the 30-case encoded protocol suite:

```bash
rg --files examples/distributed_protocols -g '*.encoding.vmt' | sort > /tmp/protocol-inputs.txt
python3 scripts/explore_quantified_policies.py \
  --inputs /tmp/protocol-inputs.txt --input-root . \
  --variants guided4096 guided4096-split-properties z3-assuming \
  --depth 20 --timeout-secs 500 --external-grace-secs 0 \
  --output benchmark_results/quantified-comparison
python3 scripts/compare_quantified_depths.py benchmark_results/quantified-comparison
```

For Tomasulo, use a manifest containing only
`examples/distributed_protocols/tomasulo/tomasulo.encoding.vmt`.
Build with `cargo build --release --no-default-features`; pass `--binary PATH`
if the binary is outside `target/release/yardbird`.

The runner alternates variant order across cases and flushes each result to
`results.jsonl`. `status.json` identifies the active case. `--resume` skips recorded
runs and rejects changed binaries, source hashes, inputs, or settings. A directory
lock prevents concurrent writers. Interrupted unrecorded attempts are archived
before retrying. Output directories must otherwise be new.

The comparison writes `completed-depths.csv`, `depth-coverage.csv`, and
`depth-comparison.json`, including paired depth wins and coverage at intermediate
time budgets. Depth 20 means checks 0–19, not an unbounded proof. Every property
clause must pass for a depth to count. Started checks receive no credit; timeout
and unknown outcomes retain completed prefixes. Completions after the wall budget
are excluded. Incomplete or inconsistent cohorts are rejected.

Matching historical flags on new code does not reproduce the historical commit.
Keep the revision, source snapshot, input encoding, build flags, and limits with
any comparison. Broad-suite results for ordinary guided search do not establish
broad-suite performance for the newer Tomasulo configuration.

## Database Schema

The training data is stored in tables centered on benchmarks plus a top-level
training run grouping:

- **training_runs**: One row per collection campaign / version id
- **benchmarks**: Metadata about each run (name, cost function, success, timing)
- **decisions**: Each instantiation decision point (axiom, depth, slot)
- **candidates**: Terms considered for each decision with features
- **core_appearances**: Terms that appeared in the unsat core (ground truth)

## Querying Training Data

```sql
-- Count benchmarks
SELECT tr.run_version, b.cost_function, COUNT(*),
       SUM(CASE WHEN success THEN 1 ELSE 0 END) as successes
FROM benchmarks b
LEFT JOIN training_runs tr ON tr.id = b.training_run_id
GROUP BY tr.run_version, b.cost_function;

-- Get decisions with chosen terms
SELECT b.name, d.axiom_name, c.term, c.current_cost
FROM benchmarks b
JOIN decisions d ON d.benchmark_id = b.id
JOIN candidates c ON c.decision_id = d.id
WHERE c.was_chosen = true
LIMIT 10;

-- Find terms that appeared in unsat cores
SELECT c.term, COUNT(*) as appearances
FROM core_appearances ca
JOIN candidates c ON c.term_hash = ca.term_hash
GROUP BY c.term
ORDER BY appearances DESC
LIMIT 20;
```
