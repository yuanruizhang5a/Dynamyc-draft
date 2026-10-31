<!-- SPDX-License-Identifier: GPL-3.0-only -->
# Dynamyc-draft

A Rocq formalization of first-order labelled process logic (LPL), a generic
cyclic-proof framework, and finite abstract state machines (ASMs). The development
connects checked finite proof graphs to semantic soundness certificates. It also
includes executable examples, benchmark runners, and two LaTeX reference manuals.

The Rocq library namespace is `CyclistRocq` (retained from the original project).
This checkout builds independently; commands below run from its root.

## Repository layout

| Path | Contents |
| --- | --- |
| `Cyclic/` | Generic relations, cyclic proof graphs, progress witnesses and soundness framework |
| `LPL/` | Many-sorted signatures, syntax, finite-trace semantics, rules, local generation and certification |
| `LPL/Benchmarks/` | Logical examples, cyclic certificates and negative checks |
| `LPL/ASM/` | Finite machines, one-layer unfolding and continuation proofs |
| `LPL/ASM/Cases/`, `LPL/ASM/Benchmarks/` | Machine declarations and checked examples |
| `LPL/tex/`, `LPL/ASM/tex/` | Reference manual sources and source-reference checks |
| `_CoqProject`, `Makefile` | Standalone library mapping and build entry points |

See the [LPL guide](LPL/README.md) and [ASM guide](LPL/ASM/README.md) for APIs,
semantic conventions, examples and scope. Historical plans, validation reports
and timestamped benchmark logs remain available beside the sources.

## Requirements

- Rocq **9.1.0**, including its standard library and `rocq makefile` / `rocq check`.
- GNU Make and Python 3; GNU `timeout` for benchmark runners.
- A TeX installation with `pdflatex` and the packages used by the manuals.
  `latexmk` is optional for continuous preview.

Ensure these commands are on `PATH`; activate the appropriate opam environment
if Rocq was installed with opam.

## Build

```sh
make                 # all Rocq sources, benchmarks, quickstart, and both manuals
make proofs          # only Rocq sources
make manuals         # only manuals and their source-reference checks
make -B proofs       # force recompilation, including copied .vo files
make kernel-check    # independently check compiled proof objects
```

`rocq makefile` generates `Makefile.rocq` and its dependency metadata from
`_CoqProject`. Add new `.v` files to `_CoqProject` when extending the library.
PDF outputs are `LPL/tex/lpl.pdf` and `LPL/ASM/tex/asm.pdf`; their TeX build
artifacts and compilation logs are kept in each manual's `build/` directory.

The manuals check source hashes and declaration links. After reviewing source
changes against the manuals, refresh their snapshots explicitly:

```sh
python3 LPL/tex/check_manual.py --refresh
python3 LPL/ASM/tex/check_manual.py --refresh
make manuals
```

The historical manuscript `LPL/Theory/20260926-Types-by-AI.tex` is separate
from the reference manuals. A draft PDF was produced in `build/theory/`, but
its referenced `logic20260609.bib` is absent from this checkout, so citations
cannot be resolved until that bibliography is supplied.

## Benchmarks

```sh
make lpl-benchmarks
make lpl-asm-benchmarks
```

The runners build common dependencies, compile individual proof units with a
600-second timeout, and record timings, source hashes and assumptions. ASM
benchmark runs also request an independent kernel check. New runs write
reports and timestamped logs; existing reports describe their recorded source
versions and should not be read as validation of later edits.

Useful compatibility targets include `lpl`, `lpl-common`, `lpl-asm`,
`lpl-asm-common`, `lpl-asm-unfold-common` and `lpl-asm-unfold-benchmarks`.

## Remove redundant artifacts

The executable text file previews its selections by default:

```sh
./remove-redundant-files.txt
./remove-redundant-files.txt --apply
# Alternatively: python3 remove-redundant-files.txt --apply
```

It selects Rocq compilation products, Python caches, manual build directories,
generated root build makefiles, and Windows `:Zone.Identifier` metadata.
`--apply` moves them into `~/Garbage`, adding numeric suffixes on collisions.
No files are permanently deleted. Repository-relative names are encoded in the
destination names so the original locations can be identified when restoring.
Run cleanup while builds are stopped, then use `make` to rebuild.

Source files, project plans, benchmark evidence and final manual PDFs are
preserved. Unreferenced research notes are retained because they may contain
unique work. The older `LPL/ASM/remove-obsolete-files.txt` handles only retired
compiler-suite artifacts; it is not the general cleanup command.

## Scope

The examples include assignments, branching, countdowns, closed cycles and
rejected malformed proof graphs. Local rule generation does not implement
complete automated proof search. Finite-trace and finite-depth claims do not
assert infinite-run fairness or termination. See the component guides and
recorded `Print Assumptions` output for each theorem's assumptions.

## License

Copyright (c) Dynamyc-draft contributors.
Each contributor retains copyright in their respective contributions.

All human-maintained repository source files—including Rocq, Python, LaTeX,
styles, build configuration, cleanup scripts and written documentation—are
licensed under the **GNU General Public License, version 3 only**
(`GPL-3.0-only`). See [LICENSE](LICENSE) for the complete license text.

You may use, modify and redistribute the covered material, including for
commercial purposes, subject to GPLv3. When conveying modified versions,
preserve required notices, identify changes, and license the covered work
under GPLv3. When conveying compiled forms, provide the corresponding source
as required by the license. Private modifications need not be published.
The material is provided without warranty; see LICENSE for details.

Generated compilation products, PDFs, logs, benchmark reports and source
snapshot/index files do not receive added license headers. Their applicable
licensing depends on their content and any covered source material they
incorporate; generation does not remove GPL obligations.
