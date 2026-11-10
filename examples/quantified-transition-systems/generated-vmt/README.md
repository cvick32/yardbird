# Generated VMT companions

**455 VMT files**, generated offline and intended for version control and
semantic review. Original benchmarks remain in the parent collection unchanged.
Yardbird needs no translation code to read these files.

| Input family | Outputs |
| --- | ---: |
| mypyvy | 124 |
| Cubicle | 162 |
| MCMT (Lambda semantics profile) | 111 |
| IvyBench action VMT companions | 54 |
| Ivy-only multisig models | 4 |
| **Total** | **455** |

These are file counts, including duplicates and property variants. The 54
IvyBench VMT outputs also serve 54 original Ivy and 54 legacy PYV companions;
they are not counted again. The manifest explicitly records that route.

- [manifest.json](manifest.json): exact source/output/converter hashes, frontend,
  notes, counts, aliases, and **17 unsupported inputs** with reasons.
- [vmt-inputs.txt](vmt-inputs.txt): generated paths relative to this directory.
- [Validation results](VALIDATION.md): parsing, semantic tests, and bounded runs.
- [Converter documentation](../../../tools/benchmark_translation/README.md):
  regeneration, encoding choices, and semantic limitations.

From the repository root:

```sh
python -m tools.benchmark_translation
python -m tools.benchmark_translation --check
target/release/yardbird \
  -f examples/quantified-transition-systems/generated-vmt/cubicle/examples/bakery.cub.vmt \
  -s concrete -d 3 --json-output
```

To run every generated input with both concrete and abstract strategies:

```sh
python3 scripts/run_quantified_benchmarks.py
```

This runs sequentially with `-d 5` (states 0–4), a ten-second timeout per run,
and incremental JSONL results under `benchmark_results/`. Python enforces an
external timeout even if Yardbird's cooperative timeout is delayed. Use
`--filter bakery.cub.vmt` for a subset or `--output PATH` for a new results file.

Each output keeps the complete source suffix (`.cub.vmt`, `.pyv.vmt`, `.in.vmt`,
`.ivy.vmt`, or `.vmt.vmt`) and starts with its source path and SHA-256. Named
action helpers expose the disjuncts of the complete transition relation.
Generation is deterministic; the check command verifies bytes without writing.

**Audit caveats:** MCMT follows the pinned Lambda interpretation, including
its Int treatment of nat/subrange types. Unbounded process sorts admit infinite
domains. Translation/typechecking and shallow BMC are not equivalence proofs.
`cubicle/examples/distrib_channels.cub.vmt` preserves a contradictory upstream
initializer and is flagged as unsuitable for meaningful safety success counts.
