<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# Abstract state machines in LPL

This development implements [revise-2.md](revise-2.md). An ASM is a finite
control graph with proposition-only state descriptions, LPL transition
instructions and an initial control state. Deductions open one state at a
time with `unfold_at` and use checked continuation backlinks for cycles.
All execution claims use the existing LPL `program_holds` semantics.

The [code reference](tex/asm.pdf) and [its sources](tex/README.md) explain the
interface, soundness arguments and examples.

## Build and verify

From the repository root, with Rocq 9.1, Python 3 and GNU `timeout` on `PATH`:

```sh
make lpl-asm
make lpl-asm-benchmarks
python3 LPL/ASM/run_unfold_benchmarks.py --kernel-check
```

`make lpl` and `make all` include the ASM development. The aliases
`lpl-asm-unfold` and `lpl-asm-unfold-benchmarks` build and measure the same
suite. Every benchmark compilation has a hard 600-second timeout.
[UNFOLD_BENCHMARK_RESULTS.md](UNFOLD_BENCHMARK_RESULTS.md) and its JSON
companion record timings, graphs, assumptions, source hashes, an audit of
active Rocq sources and the independent kernel check. Logs are retained.

## Declare a machine

Instantiate `MakeASM MySignature MyKernel` for syntax or
`MakeASMProperties MySignature MyKernel` for the local semantic lemmas.
Use the same `KERNEL MySignature` instance as your LPL rules/checker.

| Field | User supplies |
| --- | --- |
| `ASM_STATE` | Type of control states |
| `state_eq_dec` | Decidable equality of control states |
| `states` | Finite enumeration |
| `states_complete`, `states_unique` | Completeness and absence of duplicates |
| `description` | Propositions asserted at each state |
| `transitions` | Finite list of directed, LPL-labelled edges |
| `initial` | Initial control state |

A description has one field: `propositions : list formula`. Lists represent
finite sets; duplicates do not change truth. For example:

```coq
StateDescription [nonnegative; Equal x (inc one)]
```

This asserts both formulas in the current valuation. The empty description
is `StateDescription []` and asserts `Truth`. There is no variable/value
field. Equalities are ordinary propositions; assignments occur in transition
instructions. Contradictory descriptions pass syntax checking but block
observation.

Construct edges using:

```coq
unconditional source target variable term
conditional source target guard body
guarded source target guard
Transition source target arbitrary_LPL_program
```

These respectively carry `Assign variable term`, `Seq (Test guard) body`,
`Test guard`, or the supplied LPL program. Multiple outgoing edges form
nondeterministic choice, with no priority or exhaustiveness requirement.

## Open one layer

```coq
unfold_at m continuation q : program
```

This observes the conjunction of `q`'s propositions, then chooses among
`instruction e ; continuation (target e)` for edges from `q`. Only this
outgoing layer is opened. If there are no outgoing edges, the suffix is
`Test Falsity`. `unfold_at` does not itself add a stopping branch.
`terminal_states` lists states with no outgoing edges, even if some listed
edges elsewhere have false guards.

`asm_wfb` checks well-sorted pure descriptions and well-formed transition
instructions. It does not decide satisfiability or reachability.

| Theorem | Guarantee |
| --- | --- |
| `unfold_at_wf` | A checked machine and well-formed continuations yield a well-formed layer |
| `unfold_at_safe` | Safe edge instructions and continuations yield an all-state safe layer |
| `unfold_at_source_observed` | A successful layer starts in its declared source description |

The whole-machine regular-program compiler and its compiler-specific
properties have been removed from the active theory.

## Prove cyclic contracts

`MakeContinuations` takes a specification with a machine, selected endpoints,
an invariant, a syntax-check proof and local instruction-safety proofs.
Its finite proof contexts are `Call`, `Atom`, `Then` and `Branch`; plugging
programs into calls gives ordinary LPL programs. The builder opens calls
with `unfold_at`, decomposes sequence/choice, closes checked local leaves,
and uses actual `Graph.AddBacklink` commands for identical repeated calls.

`approx depth q` interprets calls at arbitrary finite observation depth.
Depth zero permits a selected endpoint observation; a successor opens one
layer with preceding-depth continuations and also allows stopping at a
selected endpoint. These approximants justify sound progress of proof goals.
The exported `accepted_safe`, `accepted_post` and `approx_checked` theorems
quantify over **every** depth. The builder's fuel bounds proof construction
only; an exhausted graph is rejected.

The continuation theory is an instance of the generic cyclic framework,
separate from LPL's labelled-sequent instance. Framework and LPL semantics
are unchanged. Tests retain their actual `[s;s]` stutters, including the
single observation used when stopping. `post` reads the final valuation;
a pure formula directly under LPL `Box` instead reads the first valuation.
No infinite-run or fairness interpretation is introduced.

## Files and examples

| File | Contents |
| --- | --- |
| `Syntax.v` | Proposition-only descriptions, machines, one-step unfolding and syntax checks |
| `Properties.v` | LPL safety helpers, local unfolding properties and endpoint predicates |
| `Support.v` | Shared integer model and local execution/arithmetic helpers |
| `Cases/` | Machine declarations |
| `Continuations.v` | Continuation contexts, cyclic builder and all-depth soundness |
| `GraphCertification.v` | Generic raw-check/certificate reflection |
| `Benchmarks/` | Five checked proof units |
| `run_unfold_benchmarks.py` | Standalone timed runner, active-source audit and kernel check |

The examples cover straight-line assignments (final 2), nondeterministic
and guarded branches, a countdown (final 0 for any natural-valued input),
a closed two-state cycle (arbitrary rounds and no terminal execution),
and positive/negative validation. Positive execution witnesses accompany
the safety claims. Validation includes malformed terms, impure or
cross-sort propositions, cross-sort assignments, missing edges, contradictory
observations, stalled backlinks and builder exhaustion.

Proof assumptions are recorded in the logs: standard-library classical
principles and, for closed-cycle valuation equality, functional
extensionality. There are no admitted proofs or new soundness axioms.

## Benchmark layout and logs

`Benchmarks/` contains the active continuation proof suite. Timed runs write
logs to timestamped directories under `benchmarks-log/`; existing logs are
preserved there. The runner and reports link to these directory names.

The former compiler-based suite has already been retired. The legacy
`remove-obsolete-files.txt` command only handles any remaining compiler
runner, reports, logs and Python cache; it preserves the active benchmark
suite and its logs.
