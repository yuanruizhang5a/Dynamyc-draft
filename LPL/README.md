<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# First-order labelled process logic

LPL implements the agreed G3FOPL syntax, semantics, rule kernels, local
generation, and certification bridge using Rocq 9.1 and its standard library.
The [primitive-formula revision](revise-261022-2-implementation.md) keeps nine
primitive constructors and defines the remaining operators as abbreviations.
The [earlier 2026-10-22 revision](revise-261022-plan.md) adds user-declared sorts, typed
functions/predicates, and reusable sequential/parallel label updates. The
controlling trace and quantifier decisions remain D1–D4 in the
[original plan](IMPLEMENTATION_PLAN.md).
The generic `Cyclic/` directory is unchanged.

[ASM/](ASM/README.md) defines finite abstract state machines and compiles their
state assertions, assignments, guarded branches and cycles into this same LPL
kernel. It includes proved execution, invariant and endpoint benchmarks with
an independent ten-minute timeout per unit (`make lpl-asm-benchmarks`).

## Build and verify

From the repository root:

```sh
make lpl                 # dependencies and all benchmark units
make lpl-benchmarks      # rerun each benchmark under timeout 600s, write report
```

[BENCHMARK_RESULTS.md](BENCHMARK_RESULTS.md) records commands, actual timings,
exit statuses, coverage, graph sizes, assumptions, and the development timeout.
The accompanying JSON records source hashes; linked compiler logs preserve
`Print Assumptions` output. The runner never increases the ten-minute limit
or deletes files. `make all` also includes the LPL development.
[VALIDATION.md](VALIDATION.md) records the independent kernel check, existing
LTL/FirstOrder regressions, and the immutable-directory/source audit.

## Files

| File | Responsibility |
| --- | --- |
| `Signature.v` | Many-sorted finitary signatures and a unit-sort adapter; decidable name equality |
| `Syntax.v` | Terms, named binding, all Boolean connectives, quantifiers, programs, labels, occurrences, reflected sort/arity/purity/tag checks, capture-avoiding FOL substitution and preservation proofs |
| `Semantics.v` | Arbitrary nonempty models, shallow FOL and LPL meanings, updates, finite execution traces, guarded sequents, substitution and freshness proofs |
| `Progress.v` | Execution/counterexample sequences, mathematical minima of summed trace lengths, rank transport and descent, framework instance |
| `Rules.v` | Proof-backed axioms and rules, context routing, structural rules, manual pure terminal boundary |
| `RuleGeneration.v` | Finite local scans, concrete requests, reflected checks, successful-result guarantees |
| `Certification.v` | Structural/witness reflection and `raw_check_sound` through `certificate_sound` |
| `Benchmarks/` | Explicit scripts, witnesses, pure proofs, semantic examples and negative checks |

## Instantiate one shared kernel

Rocq functor applications generate distinct inductive types. Create one kernel
and pass that same module to generation and certification:

```coq
From CyclistRocq.LPL Require Import Signature Rules RuleGeneration Certification.

Module MyKernel.
  Module Core := MakeRules MySignature.
  Module Model <: Core.Pr.Sem.INTERPRETATION.
    Definition interpretation := Core.Pr.Sem.Model
      Carrier inhabitant_for_each_sort typed_functions typed_predicates.
  End Model.
  Include Core.ForModel Model.
End MyKernel.

Module G := MakeRuleGeneration MySignature MyKernel.
Module C := MakeCertification MySignature MyKernel.
```

`MySignature` supplies `sort`, its equality decision, symbol types and their
equality decisions, `function_arguments`, `function_result`, and
`predicate_arguments`. Arity is derived from the argument profile. Constants
have an empty argument profile. Sorts need not be enumerable.

`Carrier : MySignature.sort -> Type` supplies any nonempty carrier per sort;
`inhabitant_for_each_sort` witnesses that nonemptiness. Function meanings have
type `forall f, arguments Carrier (function_arguments f) -> Carrier (function_result f)`;
predicate meanings consume the corresponding typed arguments and return `Prop`.
`arguments` uses nested products, ending in `unit`. No decision procedure for
semantic equality or predicate truth is required. Functions have no implicit
injectivity or constructor-disjointness laws.

[UserStructures.v](Benchmarks/UserStructures.v) is a complete example with
integer, Boolean, and function-valued heap carriers, typed read/store functions,
model-proved store laws, typed quantification and certified heap assignment.
Users prove structure laws in Rocq and pass the resulting shallow proofs to
`close_atoms` or `close_pure`. Declaring a symbol supplies its profile, without
adding an axiom or an unchecked proof rule.

`LiftSingleSorted` adapts the former arity-only signature using the unit sort.
`single_sorted_model` builds a model when all carriers are the same type;
[Support.v](Benchmarks/Support.v) gives the migrated integer example.

## Primitive formulas and derived operators

`formula` has exactly nine constructors: `Truth`, `Pred`, `EqualAt`, `Neg`,
`Conj`, `All`, `First`, `Suffix`, and `Box`. The other public operators expand
into that same syntax:

| Operator | Primitive expansion |
| --- | --- |
| `Falsity` | `Neg Truth` |
| `Disj a b` | `Neg (Conj (Neg a) (Neg b))` |
| `Impl a b` | `Neg (Conj a (Neg b))` |
| `Ex x a` | `Neg (All x (Neg a))` |
| `DualSuffix a b` | `Neg (Suffix (Neg a) (Neg b))` |
| `Diamond p a` | `Neg (Box p (Neg a))` |

`Equal`, `Next`, `Eventually`, and `Always` remain convenience definitions.
Syntax equality identifies each abbreviation with its expansion. Structural
recursion, capture-avoiding substitution, typing, and interpretation operate
on primitives only. The pure-FOL grammar likewise has primitive introduction
constructors, with `PureFalsity`, `PureDisj`, `PureImpl`, and `PureEx` supplied
as derived proof helpers.

For semantic proofs, use `fol_disj`, `fol_impl`, `fol_ex`, `falsity_holds`,
`disj_holds`, `impl_holds`, `ex_holds`, `diamond_holds`, and the existing
`dual_suffix_dual`/`dual_suffix_step` laws. The classical laws recover the
previous meanings; their nonempty-trace premises matter, since every formula
remains false on `[]`. `empty_trace_false` states that boundary uniformly.

Named derived rules remain available through the existing request API.
`right_at` and `left_at` match primitive formulas directly and concatenate
independent matches for derived expansions. For example `Disj a b` is also
`Impl (Neg a) b`, and both have a primitive negation root. All three matches
run, so explicit `Or.R`, `Impl.R`, and `Not.R` requests remain available.
The public generator still checks every returned conclusion and premise.
There is no intermediate formula representation; pattern matching uses the
primitive constructors directly.

[PrimitiveSyntax.v](Benchmarks/PrimitiveSyntax.v) checks the nine-constructor
boundary, alias expansion, overlapping rule selection, typed capture avoidance,
empty traces, and legal occurrence tags. The [theory note](Theory/revise-261022-2-primitives.md)
explains the refactor and its preservation obligations.

## Variables and updates

Program variables are `(sort, nat)` pairs; two equal numeric names at different
sorts are distinct variables. `Var`, `All`, `Ex`, and `Assign` take these pairs.
`Equal a b` creates a sort-annotated equality; cross-sort equality is rejected.
The underlying constructor for pattern matching is `EqualAt sort a b`.
The full syntax boundary checks argument sorts, assignment sorts, pure bodies,
nonempty labels and tag uniqueness. Quantifier requests check the replacement
or eigenvariable sort even for a vacuous binder. Capture avoidance preserves
the sort of every renamed binder.

```coq
Skip                         (* identity state transformation *)
Put x t                      (* evaluate t in the input state, then write x *)
Then u v                     (* execute u, then evaluate v in the result *)
Parallel [(x,t); (y,r)]       (* all RHSs read the same input state *)
Base world_name              (* state expression *)
Apply u previous_state       (* transformation applied to a state expression *)
```

Parallel writes commit in list order; the rightmost duplicate target wins.
`Parallel []` is identity. Parallel lists contain elementary assignments;
compose larger transformations with `Then`. Mutable heaps and records are
values stored in typed variables and manipulated through pure functions.

`apply_update M u s` transforms a state. `eval_state M w U` interprets a rooted
state expression. `AssignUpdate x t U` abbreviates `Apply (Put x t) U`, and the
old evaluator spelling `eval_update` is an alias of `eval_state`; neither adds
a second semantics. Each `StateLabel U` denotes one state. To retain intermediate
program states, use separate components joined by `Join`.

Internally `domain M := forall ty, Carrier ty` packages one component per sort.
Evaluation observes the component named by the term profile. Theorems
`eval_term_sorted_coincidence`, `fol_sorted_coincidence`, `all_carrier`, and
`ex_carrier` prove that unused components do not affect well-sorted FOL meaning
and that quantifiers range over exactly their declared carrier.
`eval_function_no_fallback` excludes malformed-arity fallback in a well-formed
application. This representation preserves total evaluation and reversible
countermodel transport without requiring heterogeneous semantic equality.

## Semantic conventions

* `Join` evaluates by list append, retaining repeated boundary states and
  allowing successive different states. `Empty` evaluates to `[]` and remains
  a two-sided unit. Every asserted **complete** label must be nonempty.
* Program execution composition overlaps one matching endpoint. It is separate
  from label append. Assignments and tests produce two-state traces; tests
  evaluate their guard on that stutter. Star zero is the successful true test,
  so every finite unfolding includes its final stutter.
* `denote` guards the sequent implication with assertion admissibility. No
  default state interprets an empty assertion. Boolean nonemptiness reflection,
  admissible-world validity, and false-sequent extraction are proved.
* Named `All` and `Ex` bodies must recursively be pure FOL. `formula_wfb` rejects
  any program modality or temporal operator inside either body. Modalities and
  temporal operators outside a quantified formula remain permitted.
* Quantification writes one uniform value to every trace state. `pure_head`
  proves agreement with ordinary FOL at the first state. `subst_fo` renames
  conflicting binders and has a proved semantic substitution law. The raw
  substitution helper is accompanied by its explicit capture condition.
  `pureb_spec` relates recognition to an inductive FOL grammar;
  `judgment_wfb_spec` specifies arities, recursively pure quantifier bodies,
  label checks, and tag uniqueness. `subst_fo_wf` and `subst_fo_pure` prove
  preservation under capture-avoiding substitution.
* Eigenvariable checks inspect contexts, principal formulas **and labels**,
  including assignment targets and terms in nested sequential/parallel updates. Fresh-variable
  semantic/rank transport is proved by an invertible state transformation.

Only succedent boxes, suffixes and the expanded dual-suffix form can carry
occurrence tags. Since aliases are definitions, the primitive spelling
`Neg (Suffix (Neg a) (Neg b))` has the same tag eligibility as `DualSuffix a b`.
Tags are unique within a well-formed judgment. Ranks use the manuscript's
minimum counterexample measure, the **sum of component-trace lengths**.
The fallback for an empty counterexample set or absent tag is zero; existence
and minimum-specification proofs exclude that fallback for false admissible
trace elements.

## Rules and local generation

Every concrete rule requires well-formed source/premise syntax. Each record
contains ordinary soundness and one countermodel step respecting every pair
on its selected edge. Choice/star selection uses a minimum counterexample;
assignment/test and continuing suffix/dual-suffix edges have proved strict
descent. The first suffix-right premise has no recursive principal pair.
Star unfolding and backlinks provide no progress by themselves.

The rule families are:

| Family | Public names used in requests |
| --- | --- |
| Assignment/test/sequence/choice/star | `B.Assign`, `B.Test`, `B.Seq`, `B.Choice`, `B.Star`, and corresponding `D.*`, each with `.L`/`.R` |
| Trace | `At.L/R`, `First.L/R`, `Suffix.L/R`, `DualSuffix.L/R`, singleton suffix-left axiom |
| Boolean | `Not.L/R`, `And.L/R`, `Or.L/R`, `Impl.L/R` |
| Quantifiers | `All.L/R`, `Ex.L/R` |
| Structural | `Wk.L/R`, `Exchange`, `Cut`, `Sub.World`, `Sub.Trace`, `Backlink.exact`, `Backlink.tags` |

The [expansion catalog](RULE_EXPANSIONS.md) fixes ordered premise lists. Both
left box-choice and left box-star have **two** premises. Weakening has **one
context-only** premise and is never an axiom.

```coq
G.generate_axiom j                       (* option axiom_instance *)
G.generate_rules j                       (* list rule_instance *)
G.generate_requested j request           (* option rule_instance *)
```

`generate_rules` scans eligible positions without choosing a proof strategy.
It stops at the pure terminal shape. Concrete `Local side index name` requests
select one finite local scheme. `Instantiate` supplies a quantifier term;
`Eigen` supplies an eigenvariable of the binder’s sort; `SubstituteWorld`, `SubstituteTrace`, `Cut`,
`ExchangeAdjacent`, `BacklinkExact`, and `BacklinkTags` supply explicit choices.
Backlink tag renamings are finite lists of pairs, checked against the supplied
companion. Successful-result theorems establish the input conclusion,
well-formed premises, and valid edge endpoints/progress inclusion.

Rules match the catalog's literal label constructors. Assignment/test steps
expose a final `Join sigma (StateLabel U)`; temporal steps expose an initial
state update. `RotateLabels` and `UnitLabels` let the caller explicitly present
equivalent label parentheses/units at a chosen path. Their one-premise schemes
and preservation proofs are documented in the catalog. They do not run a
normalization search. `RewriteUpdate side index label_path state_depth law`
rewrites one chosen occurrence, using `UpdateSkip`, `UpdateSequence`,
`UpdateParallelEmpty`, or `UpdateParallelSingleton`. Invalid paths, depths,
positions or laws return `None`. Successful rewrites preserve every trace tag
and its rank, and advertise no progressing pair. Failed requests mean that a verified instance was not
generated, not that the goal is false.

There is no proof-search loop, unification, automatic witness selection,
backlink discovery, solver integration, or project FirstOrder/LTL import.

## Manual proofs and certificates

`close_atoms` implements the atom/equality-at-update terminal boundary.
`close_pure` is the separately justified compound-pure extension. Both require
shape evidence and a caller-supplied shallow proof; generators do not synthesize
predicate truth or pure proof terms.

[AssignmentChange.v](Benchmarks/AssignmentChange.v) is a six-node generated
acyclic proof that an assignment changes the next-state value. Its pure leaves
are discharged with ordinary Rocq proofs. [Cyclic.v](Benchmarks/Cyclic.v) and
[CyclicTags.v](Benchmarks/CyclicTags.v) are actual 11/12-node star cycles with
backlinks and explicit tag/potential witnesses. Their exported validity follows
from `raw_check_sound`, which constructs the semantic certificate and applies
the unchanged framework's `certificate_sound`.

The cyclic examples preserve a first-state observation. The guarded decrement
loop and nested program benchmarks separately prove invariants at **every
visited state**, for all finite iteration counts, by semantic induction. Those
two complex examples are direct semantic proofs, not cyclic certificates; no
claim that a star execution must reach its loop exit is made.

The framework's witness can follow at most one tag per node and is conservative.
Acceptance of every manuscript preproof is not claimed. Negative graphs test
actual structural/tag failures and a closed nonprogressing cycle using proved
local rule records. Object-level occurrence uniqueness is checked by LPL;
it is not attributed to the generic checker.

## Assumptions and scope

There are no admitted proofs or project-defined soundness axioms. The reported
standard-library principles are classical excluded middle, definite and
indefinite description, and functional extensionality. Explicit abstract
signature/model parameters carry no constructor or predicate-induction laws.
The [mathematical extension note](Theory/revise-261022-extension.md) records
the local KeY source correspondence and the internal typed-value representation.

Completeness, proof search, acceptance of all pathwise manuscript traces,
automatic pure-FOL reasoning, and changes to the OCaml prover are outside scope.
