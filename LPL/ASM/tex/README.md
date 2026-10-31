<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# The ASM code reference

This reference documents [revise-2.md](../revise-2.md): proposition-only
state descriptions, one-step `unfold_at`, local semantic properties and
checked cyclic continuation proofs. Five benchmark units use declarations
in `Cases/` and shared helpers in `Support.v`.

Read [asm.pdf](asm.pdf) or start from [asm.tex](asm.tex). Separate sections,
local notation, checked declaration links and a reviewed source snapshot
connect the exposition to the active implementation. The snapshot includes the active theory, `Cases/` and `Benchmarks/`.
Benchmark run logs are retained under `../benchmarks-log/`.

## Build

```sh
cd Rocq-copy/LPL/ASM/tex
make
```

Requirements: Python 3, Make, pdfLaTeX and the standard LaTeX packages listed
in [setup.tex](setup.tex), including TikZ and listings. No bibliography,
network access, shell escape, downloaded fonts, or Iris dependency is needed.
The default build follows the LPL manual's three-pass pdfLaTeX build. It
retains auxiliaries and `compile.log` in `build/` and copies the final PDF to
`asm.pdf` so its relative file links resolve correctly.

If `pdflatex` defaults to MiKTeX with an unwritable user configuration while
TeX Live is installed, select TeX Live explicitly:

```sh
make PDFLATEX=/usr/bin/pdflatex
```

Optional `make latexmk` uses latexmk's automatic multi-pass build; `make loop`
enables continuous preview. Both accept `PDFLATEX=...` and `LATEXMK=...`.
There is no deleting clean target.

## Check source correspondence

```sh
make check
make check-rocq
```

The first command checks all literal `\rocq{file}{declaration}` links, section
inclusions, labels, cross-references, unfinished text markers, the declaration
index and the source snapshot. [DECLARATIONS.md](DECLARATIONS.md) links names
to source lines; [sources.json](sources.json) records the ASM files and their
LPL/kernel dependencies. The benchmark report JSON and runner are separately
hashed as evidence artifacts, so a new recorded run also triggers review.

The second command compiles [quickstart.v](quickstart.v), the small machine
example printed in the manual, against the shared LPL kernel. Compiler output
is retained in `build/quickstart.log`. This is separate from LaTeX compilation;
the manual build does not rerun the benchmark suite or modify its reports.

Hash equality and declaration existence detect drift; they do not prove that
prose is mathematically equivalent to Rocq. After changing the theory or
measurement evidence, review the affected definitions, hypotheses, output
shapes and measurements, then explicitly update the snapshot:

```sh
make refresh
make
```

To rerun the existing proofs independently, use the commands in
[ASM/README.md](../README.md), including the runner's `--kernel-check` option.

## Layout

| File | Contents |
| --- | --- |
| `asm.tex` | Master document, abstract, reading guide and contents |
| `setup.tex`, `asm.sty` | Typography, theorem environments, code listings, diagrams and notation |
| `overview.tex` | Scope, control states versus valuations, proof boundaries |
| `foundations.tex` | Inherited LPL types, traces, programs, stutters and observations |
| `declarations.tex` | State descriptions, transition constructors and finite machine record |
| `compiler.tex` | Finite outgoing choice and exact one-step equation |
| `typing.tex` | Boolean checks and well-formedness preservation proof |
| `properties.tex` | Local safety, source observations and endpoint predicates |
| `examples.tex` | Five worked benchmark units, timings and assumptions |
| `local-proofs.tex` | Local unfolding, contract rules, cyclic progress and all-depth soundness |
| `usage.tex`, `quickstart.v` | Interface guide and compilable example |
| `source-map.tex` | Module responsibilities, theorem lookup and maintenance |
| `check_manual.py` | Source references, snapshot and LaTeX structure checks |
