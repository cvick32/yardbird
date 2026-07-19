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
- `results_table.tikz` - LaTeX table of results

**LaTeX Requirements:** `pgfplots`, `longtable`, `booktabs`
