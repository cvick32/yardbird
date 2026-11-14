# Quantified transition-system benchmark collections

Full upstream collections imported on 2026-10-31 for later conversion,
execution, and curation: **688 candidate source files plus 37 support files**.
This expands the original 12-input selection by **676 candidate files**.
All original sources are preserved byte-for-byte. Alternate formats, unsafe
variants, property variants, and exact duplicates remain in the collection.

**Generated companions are now available:** [generated-vmt/](generated-vmt/README.md)
contains 455 offline-generated VMT files for mypyvy, Cubicle, MCMT, and Ivy.
Use its [input list](generated-vmt/vmt-inputs.txt) for Yardbird runs, and its
[manifest](generated-vmt/manifest.json) for source/output hashes and 17 explicit
unsupported cases. The original inventory below continues to describe the
unchanged imported sources; generated files are counted separately.

These are source-file counts, not independent algorithm counts. There are 669
distinct candidate file contents by SHA-256; semantic overlap is larger.
Quantified transition content and suitability have not been reviewed for every
input. No Yardbird execution results are claimed by this import.

## Contents

| Collection | Candidate files | Included formats and scope |
| --- | ---: | --- |
| [mypyvy](mypyvy/examples/) | 126 | All recursive `.pyv` examples, including instrumentation and unsafe variants |
| [Cubicle](cubicle/examples/) | 173 | 128 Cubicle, 18 MCMT, 14 Murphi, 12 Undip, and 1 SMV source |
| [IvyBench](ivybench/) | 171 | 58 Ivy, 54 mypyvy, 54 VMT, and 5 original TLA sources |
| [Veil](veil/Examples/) | 59 | All example models, including tutorials; `SCPTheory.lean` is counted as support |
| [Lambda CADE 2021](lambda/benchmarks/) | 159 | 42 MCMT + 43 Cubicle protocol files, 57 DynArch MCMT files, 17 railway VMT properties |
| **Total** | **688** | **71 VMT; 617 other-format candidates** |

The complete example directories are retained, including accompanying traces,
certificates, scripts, documentation, and upstream licenses. Importing a script
does not execute it. Implementation binaries and solver libraries from the
upstream archives are not included.

## Starting an evaluation

[vmt-inputs.txt](vmt-inputs.txt) lists the 71 VMT paths, relative to this directory,
so a first runner can select them without traversing the other formats. VMT
syntax alone does not establish compatibility with Yardbird's supported dialect
or theories; these files have not yet been run.

[manifest.json](manifest.json) records the format, source collection, original
path, size, SHA-256, pinned revision or archive checksum, and execution/conversion
status of each file. `benchmarks` contains candidate model files and
`support_files` contains the accompanying material. Existing source-inspection
annotations from the first batch are preserved; the remaining candidates are
marked `unreviewed`.

For curation, use `source_group` to select upstream subdirectories,
`format_variant_group` to associate known IvyBench/Lambda alternate formats,
and `identical_to` / `exact_duplicate_groups` to identify byte-identical inputs.
These fields do not claim semantic equivalence between differently encoded
systems. No candidates have been removed on the basis of duplication.

The railway files share one transition system with 17 property cases. The
upstream [CADE 2021 paper, Table 4](https://es-static.fbk.eu/people/griggio/papers/cade21extended.pdf)
reports `_0` safe and `_2` unsafe; those two previously recorded outcomes remain
in the manifest. Other expected outcomes remain unspecified until independently
checked; names containing `safe`, `unsafe`, or `buggy` are not treated as results.

When converting models, retain the upstream sources and distinguish original
safety properties from supplied strengthening invariants. Veil models require
the matching upstream Veil library and Lean toolchain; this is a source corpus,
not a standalone Lean project.

## Provenance and completeness

All files selected from GitHub snapshots were verified against the pinned Git
tree's blob hashes. The Lambda archive was verified against the SHA-256 recorded
in the research note. Every file in the original first batch was checked for
byte-for-byte preservation before expanding the collection.

Upstream licenses are retained for [mypyvy](mypyvy/LICENSE),
[Cubicle](cubicle/LICENSE), and [Veil](veil/LICENSE). No license file was found
in the pinned IvyBench tree or Lambda archive; their provenance is recorded
without assigning another project's license. Each collection's upstream README
is also retained.

The larger TOCL 2024 Lambda/UPDRIA artifact was not imported: both the
[paper-linked Drive URL](https://drive.google.com/file/d/1_lIUa_Y-yKAhj5bXnX1hLEovFmP3Jos9/view)
and the alternate spelling found in the thesis returned HTTP 404 on 2026-10-31.
This acquisition gap is recorded in `unavailable_sources`. The full accessible
CADE 2021 benchmark collection is included.

See the [research note](../../plans/quantified-transition-benchmark-research.md)
for source selection and earlier inventory counts. Its first-batch recommendation
is superseded by this complete-collection import.
