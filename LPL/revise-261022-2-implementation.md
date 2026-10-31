<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
# Primitive formula revision

Implement [revise-261022-2-plan.md](revise-261022-2-plan.md).

Keep Truth, Pred, EqualAt, Neg, Conj, All, First, Suffix and Box as constructors.
Define Falsity = Neg Truth; Disj a b = Neg (Conj (Neg a) (Neg b));
Impl a b = Neg (Conj a (Neg b)); Ex x a = Neg (All x (Neg a));
DualSuffix a b = Neg (Suffix (Neg a) (Neg b));
Diamond p a = Neg (Box p (Neg a)).

Interpret and structurally recurse only over primitives. Prove the familiar
semantic laws for abbreviations on nonempty traces and preserve the empty-trace
convention. Keep derived rule names and explicit requests through independent pattern
matches directly in the existing generators. Primitive and derived patterns
may overlap, so concatenate all applicable matches without giving one
spelling exclusive precedence. Add no intermediate formula representation.
Retain pure FOL restrictions, sorted signatures/updates, occurrence tags,
rank obligations, manual proofs and certified cycles. Keep Cyclic unchanged.

Refine reading guides, remove repeated derived structural proof branches,
explain dispatch and update documentation. Run the existing suite plus focused
primitive/abbreviation and overlapping-dispatch checks, independent kernel
checking, regressions, source/hash/assumption audits and git diff --check.

## Completion

Implemented the primitive grammar and all six definitions, removed derived
structural-recursion branches, and proved semantic compatibility laws with
the existing empty-trace convention. Independent direct matches preserve overlapping
primitive and derived requests. Sorted models, capture avoidance, update
rules, progress obligations and cyclic certificates remain checked.

Added the PrimitiveSyntax regression and build integration. Refined reading
guides, proof interfaces and formatting throughout LPL; the final formatting
pass preserves all code-token sequences. Updated the README, rule catalog and
primitive-representation theory note.

All 18 timed benchmark units, independent kernel checking and both existing
LTL/FirstOrder regressions pass. All 13 generic Cyclic files and 75 protected
files retain their baseline bytes. The source and readability audits pass.
See [VALIDATION.md](VALIDATION.md) and
[PRIMITIVE_VALIDATION.json](PRIMITIVE_VALIDATION.json) for commands and evidence.

## Direct-dispatch correction

Following the user's instruction, removed the intermediate formula-decomposition
type and its recognition/reconstruction helpers from Syntax. Updated the
existing left/right generators directly: primitive and derived pattern matches
are independent and their candidate lists are concatenated. The existing rule
builders, ordering and final checks are retained. Added left-side overlap and
explicit-request regressions alongside the existing right-side tests.

Prefer direct changes to the existing code. Introducing a custom abstraction
requires the user's approval and is reserved for cases where a direct change
is not possible.

The corrected implementation passes a fresh 18-unit benchmark run
`20261022T074825943600Z` and independent kernel checking (exit 0,
28.711 seconds). Its audit confirms removal of every view identifier
from executable sources, unchanged protected/Cyclic files and matching source
hashes. Existing unrelated-theory regression results are retained with their
original commands and logs; their sources are unchanged.
