# Pinned mypyvy frontend

Files under `mypyvy/` are byte-for-byte copies from
[`wilcoxjay/mypyvy` at `cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f`](https://github.com/wilcoxjay/mypyvy/tree/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f).
`parser.py`, `syntax.py`, `typechecker.py`, `utils.py`, and `ply/` come from
upstream `src/`; `LICENSE` comes from the repository root.

The custom PLY frontend supplies filename/column tracking and cannot be replaced
by the ordinary PyPI PLY package. mypyvy's MIT license is retained; PLY's BSD
license is embedded in `lex.py` and `yacc.py`. The converter manifest records
individual file hashes. Parser tables and bytecode caches are not vendored.

Our adapter initializes upstream options, disables parser-table writes, and
normalizes the empty modifies-list representation before invoking its frame
helper. No upstream source edits are needed.
