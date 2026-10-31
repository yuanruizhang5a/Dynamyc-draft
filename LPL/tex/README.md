<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# The LPL mathematical reference

Read [lpl.pdf](lpl.pdf) or start from [lpl.tex](lpl.tex). This manual follows the
modular mathematical presentation of `iris/tex`, with independent LPL notation
and no dependency on Iris. All manual sources, tooling, and outputs stay here.

The reference describes the current many-sorted, nine-primitive-formula
development: syntax and purity, models, sequential/parallel updates, labels,
finite executions, temporal and modal semantics, guarded sequents, the complete
supported rule catalog, counterexample ranks, local generation, cyclic
certification, and worked examples. The examples distinguish actual cyclic
certificates from direct semantic invariant proofs.

## Build

```sh
cd Rocq-copy/LPL/tex
make
```

Requirements: Python 3, Make, pdfLaTeX, and the standard LaTeX packages listed in
[setup.tex](setup.tex). No bibliography processor, network access, custom font
download, shell escape, or Iris package is required. The build uses three
pdfLaTeX passes and keeps auxiliaries plus `compile.log` in `build/`; it copies
the final PDF to `lpl.pdf`, where its relative source-file links resolve.

In environments where the default `pdflatex` selects MiKTeX with an unwritable
user configuration but TeX Live is available, use:

```sh
make PDFLATEX=/usr/bin/pdflatex
```

An optional `make loop` uses `latexmk` for continuous preview. There is no
deleting cleanup target. Existing source files and parent theory files are
not modified by the build.

## Source correspondence

Every `\rocq{file}{declaration}` reference is checked against a declaration in
the local Rocq sources. [DECLARATIONS.md](DECLARATIONS.md) lists those names with
source-line links. [sources.json](sources.json) records SHA-256 hashes for the
seven core LPL modules, all benchmark units, and the two generic cyclic modules.

```sh
make check
```

This also checks section inclusion, duplicate labels, missing cross-references,
unfinished text markers, and snapshot consistency. It does **not** verify the
mathematical equivalence of the exposition to a theorem, nor recompile Rocq.
The parent project's existing build and validation reports cover that work.

After changing the theory, review the corresponding definitions, theorem
hypotheses, exact ordered rule premises, admissibility, tags, and rank claims.
Then explicitly update the recorded source snapshot and rebuild:

```sh
make refresh
make
```

## Layout

| File | Contents |
| --- | --- |
| `lpl.tex` | Master document, abstract, reading guide, contents |
| `setup.tex`, `lpl.sty` | Typography, theorem environments, reusable notation |
| `overview.tex` | Scope and conventions |
| `signature.tex`, `syntax.tex` | Signatures, models, primitive grammar, sorting, substitution |
| `updates.tex`, `traces.tex` | Updates, labels, worlds, finite executions |
| `semantics.tex`, `sequents.tex` | Formula semantics, temporal laws, guarded judgments |
| `rules.tex` | Supported inference rules and side conditions |
| `progress.tex` | Counterexample histories, minima, and trace obligations |
| `certification.tex` | Generators, graph checks, witness, soundness argument |
| `examples.tex` | Scalar assignment, actual cycle, guarded loop, heap model, boundaries |
| `source-map.tex` | Source map and principal theorem lookup |

The manual uses local source references rather than a research bibliography.
It makes no completeness or automatic proof-search claim, and does not import
unimplemented rules from the older manuscript.
