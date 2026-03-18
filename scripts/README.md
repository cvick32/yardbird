# Training Data Collection Scripts

Scripts for collecting training data for learning cost functions.

## Quick Start

```bash
# 1. Set up database and build
./scripts/setup-training.sh

# 2. Create database (if needed)
createdb yardbird_training
psql -d yardbird_training -f src/training/migrations/001_initial.sql

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
```

## Database Schema

The training data is stored in four tables:

- **benchmarks**: Metadata about each run (name, cost function, success, timing)
- **decisions**: Each instantiation decision point (axiom, depth, slot)
- **candidates**: Terms considered for each decision with features
- **core_appearances**: Terms that appeared in the unsat core (ground truth)

## Querying Training Data

```sql
-- Count benchmarks
SELECT cost_function, COUNT(*),
       SUM(CASE WHEN success THEN 1 ELSE 0 END) as successes
FROM benchmarks
GROUP BY cost_function;

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
