<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# Proofs by local unfolding and backlinks

This is the ASM benchmark suite for [revise-2.md](../revise-2.md).
Machine declarations in `Cases/` contain only propositions. Shared integer
execution and safety helpers are in `ASM/Support.v`. Deductions use
`unfold_at`, regular-program contract rules and checked continuation backlinks.

`import_machine` transports the generative record wrappers into the proof
functor. It reuses the control type, enumeration, equality decision, initial
state, formulas and instructions. `imported_description` and `imported_edges`
prove preservation of the descriptions and ordered labelled edges.

From `Rocq-copy/`:

```sh
make lpl-asm-unfold
make lpl-asm-unfold-benchmarks
python3 LPL/ASM/run_unfold_benchmarks.py --kernel-check
```

Every benchmark compilation has the unchanged 600-second limit. Results,
proof-graph sizes, backlink counts, assumptions and kernel-check output are
recorded in [UNFOLD_BENCHMARK_RESULTS.md](../UNFOLD_BENCHMARK_RESULTS.md) and
its JSON companion. Logs are retained under `../benchmarks-log/`.

## Proof workflow

`Continuations.v` adds proof-level fragments: `Call q`, `Atom p`, `Then a b`
and `Branch a b`. These are **proof contexts**, not new LPL program
constructors. Substituting ordinary programs for calls yields an ordinary
LPL program.

The graph builder follows this workflow:

1. Open a `Call q` with its proved `ASM.unfold_at` rule. Its expansion is
   the current state's observation followed by the current outgoing choice
   of `instruction ; Call target`. A selected endpoint also permits stopping.
2. Apply proved sequence and choice rules to the regular fragment. Sequence
   creates a safety obligation for its prefix and a continuing contract
   obligation for its suffix.
3. Close local observation/instruction leaves with syntax-checked,
   model-proved safety facts. The guarded decrement uses the existing local
   test/assignment arithmetic proof, not a theorem about a compiled machine.
4. On reaching an already-seen identical call goal, execute an actual
   `Graph.AddBacklink` command. Otherwise expand that call when it is visited.
5. Submit the graph and routing witness to the unchanged cyclic framework's
   structural, relational-progress and witness checks. `raw_check_sound`
   constructs a certificate and uses `certificate_sound`.

The countdown graph has a self-returning call backlink. The closed cycle
has a backlink after visiting both control states. A graph consisting only
of two matching, nonprogressing backlinks is explicitly rejected.

These rules are semantic contract rules for ordinary LPL sequence, choice
and instructions. Continuation goals instantiate the **generic** cyclic
framework separately from LPL's labelled-sequent instance. This suite does
not claim that its graphs have the type of the labelled-sequent graphs in
`LPL/Certification.v`. The generic framework and LPL kernel are unchanged.

## Meaning and sound progress

A call is interpreted at an arbitrary natural depth using `approx depth q`:
zero permits only a selected endpoint observation; a successor opens exactly
one `unfold_at` layer with the preceding-depth continuations. The depth exists to interpret proof
goals and justify progress, not to restrict proofs to a chosen finite cutoff.
The exported graph theorems quantify over **every** depth.

Worlds contain that depth and an ordinary LPL execution trace. A false call
cannot occur at depth zero because its stop observation has the proved
contract. Opening a false call at successor depth therefore yields a false
expanded goal at strictly smaller depth. Sequence/choice decomposition and
backlinks preserve the depth. The finite witness potential decreases between
unfoldings. These facts are proved in every rule record; merely matching
judgments cannot justify a backlink cycle.

`build 100 ...` bounds the amount of **proof construction work**, independently
of semantic depth. A graph left open by exhaustion is rejected. The accepted
graphs prove both all-state invariant preservation and the final selected
description, for every finite depth, through certificate soundness.

Stopping executes one endpoint observation, so an isolated terminal call
has trace `[s;s]`. All actual LPL stutters are retained. No separate ASM
execution relation or infinite-run/fairness semantics is added.

## Cases and claims

| Unit | Main evidence |
| --- | --- |
| StraightLine | Acyclic checked graph, all-depth safety, concrete two-assignment run, final 2, rejected initial value |
| Branching | Checked graphs for both machines, both nondeterministic outcomes, complementary guarded executions, failed guard, safety |
| Counter | Checked cyclic graph with a real backlink; safety, Box/Always, final 0; complete run for every natural-valued input |
| Cycle | Prefix and terminal cyclic graphs; arbitrary finite rounds; prefix safety; no terminal executions |
| Validation | Checked dead-end/contradictory/disconnected graphs, exact stutter, syntax and sort rejection, stalled-cycle and builder-exhaustion rejection |

`GraphCertification.v` adapts LPL's generic raw-check reflection proof to an
arbitrary checkable theory; it does not alter `Cyclic/`. New proof rules
provide both validity and false-successor/progress arguments. The exported
proof assumptions are the standard-library classical principles and, for
closed-cycle valuation equality, functional extensionality; there are no
admitted proofs or project-defined soundness axioms.
