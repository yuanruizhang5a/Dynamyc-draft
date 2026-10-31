<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# Many-sorted LPL and reusable label updates

The [second revision](revise-261022-2-primitives.md) subsequently reduces formulas
to primitive constructors; the sorted-model and update design here remains.

This is the mathematical companion to the 2026-10-22 implementation plan.
The original LaTeX manuscript is preserved. D1–D4 still govern trace
concatenation, pure quantifier bodies, eigenvariable freshness and nonempty
assertion labels.

## Reference to the local KeY source

The design was checked against the supplied `key/` checkout:

| KeY source (relative to `key/`) | Role in this revision |
| --- | --- |
| `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/DeclarationBuilder.java` | Declared sorts are vocabulary entries. This revision uses flat sorts; KeY's inheritance/aliases are outside scope. |
| `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/FunctionPredicateBuilder.java` | Functions and predicates have declared argument/result profiles. |
| `key.ncore/src/main/java/org/key_project/logic/op/AbstractSortedOperator.java` | Argument sorts and result sorts accompany an operator; arity follows the profile. |
| `key.core/src/main/java/de/uka/ilkd/key/logic/op/ElementaryUpdate.java` | Elementary writes target program variables. |
| `key.core/src/main/java/de/uka/ilkd/key/logic/op/UpdateJunctor.java` | Skip and parallel composition are separate update expressions. |
| `key.core/src/main/java/de/uka/ilkd/key/logic/op/UpdateApplication.java` | Update application is distinct from the update itself. LPL applies it to rooted state expressions in labels. |
| `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/DropEffectlessElementariesCondition.java` | Parallel writes are inspected from right to left, retaining the rightmost relevant write. |
| `key.core/src/main/resources/de/uka/ilkd/key/proof/rules/updateRules.key` | Explicit update algebra; sequential application must account for changed RHS evaluation. |

These are conceptual references, without a Java dependency or a `.key` parser.
KeY's general update application to terms/formulas is not copied indiscriminately
to temporal formulas: LPL's existing updates name states within trace labels.

## Sorted language and models

A signature supplies a type of sorts with decidable name equality, function
symbols with finite input-sort profiles and one output sort, and predicate
symbols with finite input-sort profiles. Variables are pairs `(sort, name)`.
Equality compares terms at one explicitly recorded sort. Typing rejects a term
whose arguments disagree with the profile, an assignment across sorts, and an
equality across sorts. Quantifier bodies remain pure FOL, recursively.

A model supplies a nonempty carrier `D(s)` per sort and typed interpretations
of functions and predicates. Argument lists are heterogeneous nested products.
Predicate meanings are arbitrary Rocq propositions. Declaration does not imply
injectivity, constructor disjointness, induction, or decidability of truth.
User structures, such as records and heaps, are ordinary choices of carrier;
their laws are proved in Rocq and used at the manual pure-proof boundary.

### Internal value representation

The kernel uses an envelope `V = forall s, D(s)` and states `variable -> V`.
A variable of sort `s` observes component `s`. A function reads its arguments
at their declared sorts, computes a value of its result sort, and injects it
into an envelope, filling unused components with the supplied inhabitants.
Sort-annotated equality compares only its recorded component, never envelopes
or values of different sorts.

This representation is an implementation refinement of the plan: the public
model is genuinely many-sorted, while total internal values allow the existing
substitution and reversible countermodel proofs to be reused. There is one
kernel. No second untyped or legacy prover is maintained.

`eval_term_sorted_coincidence` and `fol_sorted_coincidence` prove invariance
under changes to unused components. `eval_function_no_fallback` proves that
well-formed function applications always supply their typed argument tuple.
`all_carrier` and `ex_carrier` prove that the envelope-based quantifiers are
equivalent to quantifying directly over `D(sort(x))`: any component value has
an envelope representative, and the pure body cannot distinguish representatives
with the same observed component. Together with `pure_head`, these laws give
the ordinary many-sorted FOL interpretation at the first trace state.

Capture-avoiding substitution changes names while retaining binder sorts.
Its typing-preservation theorem requires the replacement's sort to equal the
substituted variable's sort. Rule constructors and generators enforce this
condition, including vacuous binders.

## State expressions and update algebra

Let `A(U,s)` interpret a reusable update and `E(w,e)` interpret a rooted state
expression:

- `A(Skip,s) = s`.
- `A(Put(x,t),s) = s[x := eval(s,t)]`.
- `A(Then(U,V),s) = A(V,A(U,s))`.
- `A(Parallel([(x1,t1),...,(xn,tn)]),s)` evaluates every `ti` in `s`, then
  writes the results in list order. The rightmost repeated target wins.
- `E(w,Base(i)) = w.world_mapping(i)`.
- `E(w,Apply(U,e)) = A(U,E(w,e))`.

Parallel lists consist of elementary writes. Larger sequential transformations
use `Then`. With initial `x=1,y=2`, parallel `x:=y,y:=x` produces `2,1`;
sequential composition produces `2,2`. Flattening those forms without accounting
for RHS evaluation would be unsound.

`StateLabel(e)` denotes the singleton `[E(w,e)]`. Applying a sequential update
inside that expression still denotes a single final state. Program assignments
continue to produce a pre/post trace, and explicit joined label components
retain intermediate states. Label concatenation is ordinary append; program
execution composition overlaps one common endpoint. Tests and star-zero retain
their two-state stutters. No default state is introduced for an empty label.

The explicit update rewrites are:

```text
Apply(Skip,e)                  -> e
Apply(Then(U,V),e)             -> Apply(V,Apply(U,e))
Apply(Parallel([]),e)          -> e
Apply(Parallel([(x,t)]),e)     -> Apply(Put(x,t),e)
```

A request selects the occurrence, label-tree path and state-expression depth.
An inapplicable request fails. `rewrite_state_sound` and
`rewrite_update_label_sound` prove equality of the interpreted states/traces.
The generated one-premise rules preserve tag ranks and claim no progress.

## Cyclic obligations and limits

The generic framework remains unchanged. The LPL rank is still the mathematical
minimum of summed counterexample-history trace lengths. Typing adds no rank
component. Assignment/test and temporal descent remain the existing semantic
obligations. Reversible variable switching transports both sequential and
snapshot-parallel updates when the switched variable is absent from their
complete read/write variable set. Freshness includes update targets and RHSs.

Every generated rule checks its source and premises; manual terminal closures
require the same full well-formedness evidence. Certification still constructs
a certificate and applies the framework's `certificate_sound` theorem.

This revision supplies flat sort declarations, fixed function/predicate
interpretations and variable updates. Subtyping, object-language datatype
principles, mutable function locations, a declaration parser, proof search and
external solvers remain outside the confirmed scope.
