# Paper Graphics

Generate TikZ plots and statistics from Yardbird benchmark results.

## Exploratory Analysis

Generate the same reusable analysis exports used by `main_eval.py --generate-report`
without compiling the PDF workbook:

```bash
paper-graphics/.venv/bin/python paper-graphics/analyze.py \
  benchmark_results/main_eval/<run-id>/raw/**/*.json \
  --output-dir /tmp/yardbird-analysis
```

The output includes structured JSON, a Markdown summary, strategy and baseline
summary CSVs, normalized benchmark results, and per-benchmark comparison
classifications. Use `--baseline <strategy-id>` to override the default concrete
baseline and `--runtime-tie-pct <percent>` to change the default 5% tie band.

## TikZ Generator

```bash
python3 comparison_figure_generator.py <json_files...> [options]
```

### Arguments

- `json_files` - One or more benchmark JSON result files

### Options

**Output Types:**

- `--scatter` - Generate TikZ scatter plot
- `--tikz-table` - Generate LaTeX table
- `--table` - Print human-readable comparison table
- `--all` - Generate all graphics (default)

**Analysis:**

- `--instantiations` - Compute axiom instantiation statistics
- `--bmc-depth N` - BMC depth for instantiation calculation (default: 50)

**Strategy Selection:**

- `--strategy1 NAME` - First strategy for comparison (default: concrete)
- `--strategy2 NAME` - Second strategy for comparison (default: abstract)

**Output:**

- `--output-dir DIR` - Output directory for generated files (default: .)

### Examples

```bash
# Basic usage with multiple benchmark files
python3 comparison_figure_generator.py results1.json results2.json

# Runtime analysis only
python3 comparison_figure_generator.py results.json --scatter

# Detailed comparison with instantiation analysis
python3 comparison_figure_generator.py abstract.json concrete.json --table --instantiations

# Custom strategy comparison
python3 comparison_figure_generator.py results.json --strategy1 concrete --strategy2 interpolation
```

### Output Files

- `runtime_scatter.tikz` - Runtime comparison scatter plot
- `runtime_cactus_plot.tex` - Runtime cactus plot across all strategies
- `instantiation_cactus_plot.tex` - Axiom instantiation cactus plot
- `conflict_cactus_plot.tex` - Total solver conflicts cactus plot
- `results_table.tikz` - LaTeX table of results

**LaTeX Requirements:** `pgfplots`, `longtable`, `booktabs`

## Instantiation evaluation tables

Generate TeX tables directly from a four-way instantiation `main_eval` manifest
(or one or more Garden JSON files):

```bash
paper-graphics/.venv/bin/python paper-graphics/guided_tables.py \
  benchmark_results/main_eval/<run-id>/run.json \
  --output-dir benchmark_results/main_eval/<run-id>/report/guided_tables
```

The output includes `evaluation_summary.tex`, `runtime_details.tex`,
`instantiation_stats.tex`, and `api_usage.tex`, plus exact values in
`table_data.json`, `summary.csv`, and `benchmarks.csv`. Load `booktabs` and
`\input{...}` the desired fragments. They use full-width `table*` environments
for two-column papers. Compile `preview.tex` from the output directory to
inspect all tables together. Regular main_eval report generation automatically
exports these tables and adds their contents to the workbook for compatible
instantiation configurations.

Cost totals use embedded Garden `api_usage`; detailed JSONL supplies proposal
validation counts without billing the same calls twice. Missing logs leave
validation counters unknown (except confirmed zero-call runs). Installed
schemas count distinct `used_instances` within each benchmark; indexed
assertions use `total_instantiations_added`. These are separate from validated
proposals and successful guidance episodes. Timed-out runs often lack final
installation counters, so totals include explicit coverage and `*` markers.
Unknown charges are not zero. Spending excludes AWS compute, and runtime sums
are not the parallel AWS job duration. Common-solve medians use the intersection
of solved benchmarks across all displayed methods. Missing cores are reported
as missing evidence, never zero core utilization. The generator makes no solver
or model calls and rejects duplicate method/benchmark trials.
