# Paper Graphics

Generate TikZ plots and statistics from Yardbird benchmark results.

## TikZ Generator

```bash
python3 tikz_generator.py <json_files...> [options]
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
python3 tikz_generator.py results1.json results2.json

# Runtime analysis only
python3 tikz_generator.py results.json --scatter

# Detailed comparison with instantiation analysis
python3 tikz_generator.py abstract.json concrete.json --table --instantiations

# Custom strategy comparison
python3 tikz_generator.py results.json --strategy1 concrete --strategy2 interpolation
```

### Output Files

- `runtime_scatter.tikz` - Runtime comparison scatter plot
- `results_table.tikz` - LaTeX table of results

**LaTeX Requirements:** `pgfplots`, `longtable`, `booktabs`
