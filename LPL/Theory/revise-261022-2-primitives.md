<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# Primitive formula representation

This note accompanies `revise-261022-2-plan.md`. The original manuscript and
the sorted-model/update design remain preserved.

## One formula language

The mutually inductive formula/program language now has these formula cases:

```text
A ::= Truth | Pred(p, terms) | EqualAt(sort, term, term)
    | Neg(A) | Conj(A,A) | All(variable,A)
    | First(A) | Suffix(A,A) | Box(program,A)
```

The public derived operators are definitions:

```text
Falsity          = Neg Truth
Disj A B         = Neg (Conj (Neg A) (Neg B))
Impl A B         = Neg (Conj A (Neg B))
Ex x A           = Neg (All x (Neg A))
DualSuffix A B   = Neg (Suffix (Neg A) (Neg B))
Diamond p A      = Neg (Box p (Neg A))
```

Consequently an abbreviation and its expansion are definitionally equal.
There is no normalization proof or second semantic interpreter between them.
`Equal`, `Next`, `Eventually`, and `Always` remain derived conveniences.

Every structural recursion and induction now follows the primitive language:
well-formedness and sorting, variable collection, named substitution,
capture avoidance, pure-FOL recognition, shallow interpretation, freshness
transport and semantic coincidence. Repeated Boolean/existential induction
branches have been removed. The public derived pure-formula introduction names
are proof definitions over the primitive `pure_formula` constructors.

## Semantic preservation

The primitive trace interpreter still makes every formula false on an empty
trace. Primitive negation therefore agrees with ordinary logical negation
only on nonempty traces. The relevant abbreviation laws retain that guard;
`empty_trace_false` states the unconditional empty-trace fact.

`fol_disj`, `fol_impl`, and `fol_ex` recover the usual FOL operations.
`disj_holds`, `impl_holds`, `ex_holds`, and `diamond_holds` recover the former
nonempty-trace meanings, including existential execution witnesses for a
diamond and uniform trace-state writes for an existential quantifier.
`falsity_holds` rules out falsity at any trace. `diamond_dual` and
`dual_suffix_dual` now follow directly from primitive negation.

These are classical equivalences using the already permitted standard-library
classical logic. No project axiom or extra external library is introduced.
The typed substitution and carrier-quantification theorems, all proof-rule
soundness/countermodel fields and the certification theorem are rechecked.

## Direct derived-rule recognition

A derived formula can match several rule patterns. For example,
`Disj A B = Impl (Neg A) B`, and both expansions have a primitive Neg root.
Selecting only the first matching pattern would hide valid requested rules
and could change existing proof scripts.

`right_at` and `left_at` operate directly on `occurrence_formula`. Each
concatenates a primitive-constructor match with independent matches for
expanded disjunction, implication, dual suffix and diamond. The left generator
also matches the expanded existential; right existential instantiation uses
the existing explicit request branch. Matching an abbreviation never prevents
another applicable primitive or derived rule from being generated.

There is no intermediate syntax or shared decomposition interface. Existing
rule builders retain their semantic proofs and the verification boundary
checks the exact source, every premise, sorting, occurrence tags and edge
metadata. Explicit rule names and quantifier requests retain their interfaces.
The generator may return several valid schemes for an expanded formula;
no proof-search strategy or exclusive spelling priority is imposed.

## Trace annotations and cyclic preservation

Primitive Box and Suffix occurrences keep their original trace eligibility.
The exact expanded dual suffix `Neg (Suffix (Neg A) (Neg B))` is also eligible,
so a surface abbreviation and its primitive spelling cannot differ in tag
policy. Arbitrary negative suffixes and derived diamonds remain untraceable.

The rank construction is unchanged. Only a primitive Box root recursively
extends a counterexample history. A derived diamond or dual suffix has a Neg
root, so it still receives the former non-box singleton history. The existing
strict-descent proofs and real cyclic/tag-renaming certificates remain checked
against the byte-for-byte unchanged generic Cyclic framework.

## Reading and verification

Read Syntax's primitive grammar and abbreviation definitions; then the
primitive interpreters and derived semantic laws in Semantics. Rules uses
these laws for named derived schemes. RuleGeneration matches the primitive
syntax directly; Certification continues to verify the resulting judgments.

The new PrimitiveSyntax benchmark covers definitional expansions, overlapping
rule names, same-sort capture avoidance under the defined existential,
nonempty/empty-trace behavior and trace-tag policy. The existing benchmark
suite retains its exact premise checks, heap structures, updates and real
cyclic certificates. The full verification record is linked from VALIDATION.md.
