<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# LPL revision: typed structures and label updates

## Summary and feasibility
The extension is feasible within the existing framework. LPL already parameterizes functions and predicates over a signature; add multiple sorts, typed interpretations, and reusable update expressions. The local KeY implementation supplies the reference: typed declarations, elementary/parallel updates, and update application. Preserve the cyclic framework.

This plan is saved before changing theory code. Record baseline hashes and verification results.

## Typed signatures and user-defined structures
- Extend SIGNATURE with sorts and decidable equality, function argument/result sorts, and predicate argument sorts; derive arities.
- Program variables carry a sort and natural-number name. Quantifiers and assignments use them; world/trace names and tags retain their roles.
- Retain executable raw syntax with reflected typing checks, including vacuous quantifier requests.
- Models provide a nonempty carrier per sort, heterogeneous function arguments, and Prop-valued predicates. No semantic equality or truth decision is required.
- Totalize rejected raw terms with per-sort inhabitants; prove well-sorted evaluation uses no fallback.
- Users declare structures in Rocq signature/model modules and prove model laws for manual pure leaves.
- Migrate existing clients to one generalized kernel, with unit-sort adapters and construction helpers, without a second legacy implementation.

## Updates, labels, and proof integration
update ::= Skip | Put(variable,term) | Then(update,update) | Parallel(list of assignments)
state_expr ::= Base(world_name) | Apply(update,state_expr)
StateLabel contains a state expression. AssignUpdate abbreviates Apply(Put(...),...).
Skip preserves the state. Put evaluates its RHS before writing. Then evaluates its second update after its first. Parallel evaluates all RHSs in the original state and commits in list order, so the rightmost duplicate target wins. Its elements are elementary assignments.
- Applied updates denote one state; label components retain intermediate execution states.
- Preserve D1-D4: append labels, overlapping execution composition, nonempty complete labels, recursively pure FOL quantifier bodies.
- Extend typed substitution, same-sort fresh names, freshness including all update targets/RHSs, and the reversible eigenvariable state-switch proofs.
- Prove update identity, sequencing, snapshot, overwrite, frame, and substitution laws.
- Adapt every rule's soundness, countermodel step, rank transport/decrease, generation guarantees, and certification. Update algebra never contributes progress.
- Add explicit RewriteUpdate requests selecting side, occurrence, label path, state depth, and law: skip, sequence, empty parallel, singleton parallel. Inapplicable requests fail; successful rules preserve traces and have one nonprogressing premise.

## Verification and completion
- Migrate all benchmarks and retain existing semantic/certificate coverage.
- Test heterogeneous signatures and reject cross-sort applications, equality, assignments, instantiations, eigenvariables, including vacuous binders.
- Test parallel swaps versus sequence, duplicate targets, identity/empty/nested updates, frame properties, explicit intermediate labels.
- Add integer/Boolean/heap structures with function-valued heap carriers, proved read/store laws, typed quantification, assignment, pure proofs, and generated certification.
- Retain actual cyclic and tag-renaming certificates and exercise typed update labels.
- Run all benchmarks with 600-second limits, independent kernel checking, and FirstOrder/LTL regressions; record actual hashes, timings, assumptions, and coverage.
- Audit admitted proofs, soundness axioms, unchecked boundaries, stale assumptions, redundant definitions; consolidate in place and preserve historical artifacts.
- Update docs, rule catalog, build/report integration. Add Theory/revise-261022-extension.md. Mark superseded sections of the original implementation plan while preserving D1-D4.
- Keep Cyclic, reference KeY, and FirstOrder/LTL sources unchanged.

## Confirmed assumptions
Flat sorts; no subtyping or object-language datatype declarations. Fixed function/predicate interpretations; mutable structures live in typed variables. Rocq module declaration interface; no parser, proof search, solver, or unchecked rule extension. Preserve the LaTeX manuscript and add a mathematical extension note.

## Implementation record

Implemented and verified. [VALIDATION.md](VALIDATION.md) and
[REVISION_VALIDATION.json](REVISION_VALIDATION.json) record the final evidence.
All 17 benchmarks, independent kernel checking and FirstOrder/LTL regressions
pass. The complete Cyclic directory is byte-for-byte unchanged.

The one representation refinement is a product-of-carriers envelope inside
the single shared kernel. The public model interface remains many-sorted;
sorted coincidence and carrier-quantifier laws prove its FOL correspondence.
See [the mathematical extension note](Theory/revise-261022-extension.md).
