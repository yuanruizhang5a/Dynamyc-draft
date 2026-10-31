<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# LPL implementation validation

## Current revision: primitive formulas with direct rule recognition (2026-10-22)

The [requested revision](revise-261022-2-plan.md) and the user's direct-dispatch
correction are implemented. The [verification record](PRIMITIVE_VALIDATION.json)
links the source baseline, fresh timed build, independent kernel check and audits.

- **18/18 benchmark units pass**, each with the unchanged 600-second limit.
  Slowest: `Signatures`, 6.417 seconds.
  [Timed report](BENCHMARK_RESULTS.md), [source-hash manifest](BENCHMARK_RESULTS.json).
- **Independent kernel check passes**, exit 0, 28.711 seconds.
  It checks primitive syntax, generation, shared dependencies, quantifiers,
  nested programs, heap/update proofs and the tag-renaming cycle.
  [Command and timing](validation-logs/20261022T075019721767Z/KernelCheck.json),
  [output](validation-logs/20261022T075019721767Z/KernelCheck.txt).
- **The intermediate formula-decomposition type and all its helpers are removed**.
  The existing `right_at` and `left_at` generators concatenate independent
  matches on primitive formulas, retaining every overlapping rule choice and
  existing named request. PrimitiveSyntax checks all three overlapping Boolean
  schemes and explicit requests on both sides; RuleCoverage retains its 50
  exact premise-list checks.
  [Focused benchmark](Benchmarks/PrimitiveSyntax.v),
  [primitive/direct-pattern audit](validation-logs/20261022T075019721767Z/PrimitiveAudit.json).
- **All 13 generic Cyclic files and all 75 protected files are unchanged**.
  All 27 LPL source hashes match the fresh successful benchmark run. No admitted
  proofs, project axioms, disabled guard checking or FirstOrder/LTL/SMTCoq
  imports occur. No removed view identifiers remain in executable LPL sources.
  `git diff --check` passes; `make -n lpl` has no pending build.
  [Source audit](validation-logs/20261022T075019721767Z/SourceAudit.json).
- **Existing LTL and FirstOrder regressions passed**, respectively 2.286 and
  135.607 seconds in the preceding run. Their results are retained because
  neither imports LPL and all protected sources remain unchanged.
  [Commands, timings and logs](validation-logs/20261022T071507219167Z/Regressions.json).

The formula type still has exactly nine primitive constructors, and all six
requested derived operators are definitions. Typed structures, substitution,
updates, manual proofs, ranks and real cyclic certificates remain checked.
Every formula remains false on an empty trace; derived semantic equivalences
retain their nonempty-trace premises. The [theory note](Theory/revise-261022-2-primitives.md)
explains direct recognition and the reading order.

`Print Assumptions` output remains in the benchmark logs. The revision uses
the existing standard-library classical principles and introduces no project
axiom or external library.

The [saved readability audit](revise-261022-2-readability.json) records the earlier
formatting pass, before this correction. Its code-token equality claims apply
to that pass. The subsequent removal and direct-generator changes are
substantive edits verified by the current build and kernel check. The
[preceding verification record](validation-logs/20261022T071507219167Z/PRIMITIVE_VALIDATION.json)
and its report are archived with that run's original source hashes.

Reproduce the affected checks from `Rocq-copy/`:

```sh
make lpl-benchmarks
timeout --signal=KILL 600s rocq check -silent -Q . CyclistRocq CyclistRocq.LPL.Syntax CyclistRocq.LPL.Benchmarks.PrimitiveSyntax CyclistRocq.LPL.Benchmarks.CyclicTags CyclistRocq.LPL.Benchmarks.Quantifiers CyclistRocq.LPL.Benchmarks.NestedProgram CyclistRocq.LPL.Benchmarks.UserStructures CyclistRocq.LPL.Benchmarks.UpdateAlgebra
```

## Historical validation: typed structures and label updates (2026-10-22)

The [saved revision plan](revise-261022-plan.md) is implemented. The saved
[verification record](REVISION_VALIDATION.json) links the exact commands, logs,
source hashes, kernel check and regressions. Earlier results below are historical.

- **17/17 benchmark units pass**, with the unchanged 600-second limit.
  Slowest: `Signatures`, 7.291 seconds.
  [Timed report](validation-logs/20261022T031202920183Z/BENCHMARK_RESULTS.md), [source-hash manifest](validation-logs/20261022T031202920183Z/BENCHMARK_RESULTS.json).
- **Independent kernel check passes**, exit 0, 31.251 seconds.
  It checks the shared syntax/semantics/rule/certification dependencies, the real
  tag-renaming cycle, quantifiers, nested programs, heap structures and update
  conversions. [Command and timing](validation-logs/20261022T031202920183Z/KernelCheck.json), [output](validation-logs/20261022T031202920183Z/KernelCheck.txt).
- **Existing LTL and FirstOrder regressions pass**, respectively
  2.208 and 133.823 seconds.
  [Commands, timings and logs](validation-logs/20261022T031202920183Z/Regressions.json).
- **All 13 Cyclic files retain their exact bytes**, with no added or missing
  files. All 75 protected files in the baseline remain unchanged.
  All 26 current LPL source hashes match the benchmark manifest.
  No admitted proofs, project-defined axioms, disabled guard checking or
  FirstOrder/LTL/SMTCoq imports occur. `git diff --check` passes, and
  `make -n lpl` reports no pending build. [Source audit](validation-logs/20261022T031202920183Z/SourceAudit.json).

### New evidence

| Obligation | Evidence |
| --- | --- |
| Typed signature/model interface and independent sort checks | `term_sortedb_spec`, `formula_program_sortedb_spec`, `update_wfb_spec`, `judgment_wfb_spec`; UserStructures positive/negative cases |
| Typed capture-avoiding substitution | `subst_term_wfb`, `subst_fo_wfb`, `subst_fo_wf`; a conflicting Boolean binder is renamed while substituting an integer expression |
| Genuine quantification over each declared carrier | `eval_term_sorted_coincidence`, `fol_sorted_coincidence`, `all_carrier`, `ex_carrier`, `all_trace_carrier`, `ex_trace_carrier` |
| No well-formed function-application fallback | `eval_function_no_fallback` |
| Sequential and snapshot-parallel updates | `parallel_append`, `parallel_last_write`, `parallel_frame`, `apply_update_frame`, `apply_then_associative`; integer and heterogeneous heap computations |
| Freshness through both update forms | `switch_parallel`, `switch_transformation`, `switch_update`; nested target/RHS eigenvariable rejection |
| Explicit trace-preserving update rules | `rewrite_state_sound`, `rewrite_update_label_sound`, `rewrite_update_left/right`; all four laws, both sides, invalid selectors, preserved tag/rank and no artificial progress |
| User-defined function-valued heap | Proved store/read laws, a six-node generated assignment certificate and a two-node heap-quantifier certificate in UserStructures |
| Cyclic compatibility | Existing 11/12-node Cyclic/CyclicTags certificates now include a typed parallel-update initial label |

The implementation uses an internal product-of-carriers value envelope to
reuse total substitution and reversible countermodel transport in one kernel.
The public model meanings are typed, equality observes its declared carrier,
and the carrier/coincidence theorems establish the pure-FOL correspondence.
The [extension note](Theory/revise-261022-extension.md) explains this refinement
and maps it to the supplied KeY source. No second legacy kernel is maintained.

`Print Assumptions` output is preserved in the benchmark logs. The concrete
certificate theorems use the same standard-library classical description,
excluded-middle and functional-extensionality principles as before; no new
project soundness axiom is introduced. The carrier-correspondence theorem
printed by UserStructures is closed under the global context.

Reproduce the build and kernel check from `Rocq-copy/`:

```sh
make lpl-benchmarks
timeout --signal=KILL 600s rocq check -silent -Q . CyclistRocq CyclistRocq.LPL.Syntax CyclistRocq.LPL.Benchmarks.CyclicTags CyclistRocq.LPL.Benchmarks.Quantifiers CyclistRocq.LPL.Benchmarks.NestedProgram CyclistRocq.LPL.Benchmarks.UserStructures CyclistRocq.LPL.Benchmarks.UpdateAlgebra
```

## Historical validation: original single-sort implementation (2026-10-16)

The implementation follows D1–D4 and all eight implementation stages in
[IMPLEMENTATION_PLAN.md](IMPLEMENTATION_PLAN.md). The final syntax audit adds
explicit reflection for the FOL grammar and well-formedness predicates, plus
proofs that capture-avoiding and sorted label substitutions preserve their
syntax invariants. The API and semantic conventions are in [README.md](README.md).

## Learner comments

All 24 `.v` files now include reading guides and explanations of their central
definitions, proof strategies, module connections and benchmark steps. A
[comment audit](validation-logs/20261016T172216122771Z/CommentAudit.json) compares
each file with its version before annotation, removing nested comments and
preserving quoted strings: all code-token sequences are unchanged. It also
confirms that every current source hash matches the new successful benchmark
run and all 13 `Cyclic/` files retain their original bytes.

The benchmark build below was rerun after annotation. The independent kernel,
existing-theory regression and initial scope records are preserved from the
implementation verification; the comment update changes no definitions or
proof terms.

## Proof obligations

| Obligation | Implemented evidence |
| --- | --- |
| Arbitrary signatures and models | `Signature.v`, `Semantics.v`; independent Boolean and integer instances and an abstract-model functor in `Benchmarks/Signatures.v` |
| Recursive pure-FOL quantifier bodies, arities, labels and tags | `pureb_spec`, `term_wfb_spec`, `formula_program_wfb_spec`, `judgment_wfb_spec` in `Syntax.v` |
| Capture avoidance and substitution preservation | `subst_fo_correct` in `Semantics.v`; `subst_fo_wf`, `subst_fo_pure`, and sorted label-substitution preservation in `Syntax.v` |
| Assignments, tests and context freshness | Exact assignment/test semantic laws and `switch_semantics` in `Semantics.v`; the mutual freshness proof includes program assignments, test guards and bound variables |
| Both label-variable sorts | `eval_world_substitution`, `eval_world_label_substitution`, `eval_trace_label_substitution`; no world-to-trace substitution |
| Append labels and nonempty assertions | Label unit/length laws, `label_nonemptyb_spec`, `valid_admissible`, `false_sequent` in `Semantics.v` |
| Mathematical counterexample minima | `minimum_spec`, `false_minimum_exists` in `Progress.v`, using summed trace lengths |
| Trace transport and progress | `sequence_nonincrease`, `choice_nonincrease`, `star_nonincrease`, `assignment_decrease`, `test_decrease`, `suffix_decrease`, `dual_suffix_decrease`, and switch transport in `Progress.v` |
| All rule families and checked local generation | `Rules.v`, `RuleGeneration.v`; 50 exact premise-shape checks in `Benchmarks/RuleCoverage.v` |
| Certification through the unchanged framework | `raw_check_sound` in `Certification.v`, constructing a certificate and applying `certificate_sound` |
| Manual acyclic and cyclic certificates | Six-node assignment-change proof, 11-node star cycle, 12-node star cycle with explicit tag renaming; explicit graph scripts and witnesses |
| Complex all-visited-state invariants | `CounterLoop.v` and `NestedProgram.v`, proved for arbitrary finite iterations by semantic induction |

The star certificates preserve a first-state observation. The two complex
all-visited-state examples are direct semantic proofs, not cyclic certificates.
These proof modes are recorded separately in the benchmark report. Star does
not require an execution to reach a loop exit.

## Timed benchmark build

Run from `Rocq-copy/`:

```sh
make lpl
make lpl-benchmarks
```

All **15/15** isolated units passed after annotation in run
`20261016T172216122771Z`. Every unit used the unchanged 600-second limit;
the slowest took 6.953 seconds. [BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md)
contains individual commands, timings, logs and assumptions. Its JSON includes
hashes of all 24 LPL source files, including common dependencies. A final
`make -n lpl` reported that the build was current.

The one development timeout and the auxiliary proof simplification that fixed
it are documented in the report; the cyclic certificate was retained.

## Independent kernel check

The implementation was also checked independently before annotation with:

```sh
timeout --signal=KILL 600s rocq check -silent -Q . CyclistRocq \
  CyclistRocq.LPL.Syntax \
  CyclistRocq.LPL.Benchmarks.CyclicTags \
  CyclistRocq.LPL.Benchmarks.Quantifiers \
  CyclistRocq.LPL.Benchmarks.NestedProgram
```

The check **passed with exit 0 in 26.082 seconds**. It checks the new syntax
lemmas, shared rule/progress/certification
dependencies, cyclic certificate, quantifier proof, and arbitrary-predicate
invariant. The [machine record](validation-logs/20261016T165938090755Z/KernelCheck.json)
preserves its command, exit status and elapsed time; the silent compiler
output is retained beside it.

## Existing-theory regressions

Both regressions passed after build integration, with a 600-second limit:

| Command from `Rocq-copy/` | Seconds | Exit |
| --- | ---: | ---: |
| `timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LTL/Examples.v` | 2.266 | 0 |
| `timeout --signal=KILL 600s rocq compile -Q . CyclistRocq FirstOrder/Search.v` | 134.589 | 0 |

The commands, timings and retained output paths are in
[Regressions.json](validation-logs/20261016T165938090755Z/Regressions.json).
The final additional changes affect LPL syntax proofs and documentation;
neither regression imports LPL.

## Initial scope and assumptions audit

The [source audit](validation-logs/20261016T165938090755Z/SourceAudit.json)
compares against the preserved [baseline](validation-logs/20261016T165938090755Z/Baseline.json):

- All **13 files** in `Cyclic/`, including generated artifacts, match exactly;
  the directory contains no additional files.
- All **29 pre-existing non-LPL `.v` sources** retain their original bytes.
- All 24 initial LPL source hashes matched that implementation benchmark run;
  the comment audit above records the current sources.
- No admitted proofs, project-defined axioms, custom tactics, external-library
  imports, or project FirstOrder/LTL imports occur in LPL sources.
- `git diff --check` passes. Changes outside `LPL/` are the explicit build-file
  entries and top-level usage documentation.

`Print Assumptions` in the final benchmark logs reports only these
standard-library principles across the audited exported theorems and rule
kernels:

- `Classical_Prop.classic`
- `Description.constructive_definite_description`
- `ClassicalEpsilon.constructive_indefinite_description`
- `FunctionalExtensionality.functional_extensionality_dep`

Abstract signatures, model interpretations and the arbitrary benchmark
predicate remain explicit module parameters; they supply no constructor laws,
predicate decision procedures or unproved soundness statements. The finite
framework witness remains conservative, as described in the plan; acceptance
of every manuscript preproof and proof-search completeness are outside scope.
