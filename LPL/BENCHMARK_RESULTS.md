# LPL benchmark results

UTC run: `20261022T074825943600Z`. **18/18 units passed.**

```text
The Rocq Prover, version 9.1.0
compiled with OCaml 4.14.1
```

Common dependencies: `make lpl-common`, exit 0, 0.003s.
Every isolated benchmark uses `timeout --signal=KILL 600s`; the limit is never increased.

| Unit | Seconds | Exit | Evidence | Compiler output / assumptions |
| --- | ---: | ---: | --- | --- |
| PrimitiveSyntax | 0.716 | 0 | nine-constructor syntax, definitional aliases, independent primitive/derived pattern matches on both sides, typed capture avoidance, tags and empty-trace semantics | [log](benchmark-logs/20261022T074825943600Z/PrimitiveSyntax.txt) |
| Labels | 0.475 | 0 | D1/D4, units, differing states, overlap; 1-node certificate | [log](benchmark-logs/20261022T074825943600Z/Labels.txt) |
| Signatures | 6.417 | 0 | arbitrary models and independent Boolean signature; leaf certificates | [log](benchmark-logs/20261022T074825943600Z/Signatures.txt) |
| Updates | 0.431 | 0 | identity, changed/dependent assignments, intermediate states; pure certificate | [log](benchmark-logs/20261022T074825943600Z/Updates.txt) |
| UserStructures | 2.851 | 0 | integer/Boolean/function-valued heap sorts, typing/freshness rejection, carrier quantification, snapshot writes; 6-node heap assignment and 2-node heap-quantifier certificates | [log](benchmark-logs/20261022T074825943600Z/UserStructures.txt) |
| UpdateAlgebra | 0.558 | 0 | snapshot swap versus sequence, duplicate/frame/nested writes, all rewrite laws and invalid selectors; 3-node generated conversion certificate | [log](benchmark-logs/20261022T074825943600Z/UpdateAlgebra.txt) |
| Tests | 0.535 | 0 | successful/failed and trace-sensitive tests; 2-node certificate | [log](benchmark-logs/20261022T074825943600Z/Tests.txt) |
| RegularPrograms | 0.474 | 0 | sequence, choice, zero/one/nested finite iteration; semantic validity | [log](benchmark-logs/20261022T074825943600Z/RegularPrograms.txt) |
| Booleans | 0.509 | 0 | mixed modal Boolean formula; 3-node certificate | [log](benchmark-logs/20261022T074825943600Z/Booleans.txt) |
| Quantifiers | 0.521 | 0 | capture avoidance, shadowing, eigenvariables; 2-node certificate | [log](benchmark-logs/20261022T074825943600Z/Quantifiers.txt) |
| Temporal | 0.455 | 0 | immediate/postponed suffix, dual, first, next-at-end, sum measure; certificate | [log](benchmark-logs/20261022T074825943600Z/Temporal.txt) |
| AssignmentChange | 0.513 | 0 | changed next-state value; 6-node certificate, 1 distinct tag | [log](benchmark-logs/20261022T074825943600Z/AssignmentChange.txt) |
| RuleCoverage | 0.952 | 0 | 50 exact rule/request premise shapes, positive/negative syntax checks | [log](benchmark-logs/20261022T074825943600Z/RuleCoverage.txt) |
| CheckerNegative | 0.441 | 0 | open/dangling/mismatched graphs, absent tags, closed nonprogressing cycle | [log](benchmark-logs/20261022T074825943600Z/CheckerNegative.txt) |
| Cyclic | 0.742 | 0 | 11-node star cycle, real backlink, 1 distinct tag, explicit potential | [log](benchmark-logs/20261022T074825943600Z/Cyclic.txt) |
| CyclicTags | 0.883 | 0 | 12-node star cycle, explicit tag-renaming backlink, 2 distinct tags | [log](benchmark-logs/20261022T074825943600Z/CyclicTags.txt) |
| CounterLoop | 0.565 | 0 | guarded integer decrement loop, every visited state and finite stopping point | [log](benchmark-logs/20261022T074825943600Z/CounterLoop.txt) |
| NestedProgram | 2.790 | 0 | nested sequence/choice/star, arbitrary uninterpreted predicate of unchanged variable | [log](benchmark-logs/20261022T074825943600Z/NestedProgram.txt) |

## Commands

Commands ran from `Rocq-copy/`, after compiling common dependencies.

```sh
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/PrimitiveSyntax.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Labels.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Signatures.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Updates.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/UserStructures.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/UpdateAlgebra.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Tests.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/RegularPrograms.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Booleans.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Quantifiers.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Temporal.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/AssignmentChange.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/RuleCoverage.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/CheckerNegative.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/Cyclic.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/CyclicTags.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/CounterLoop.v
timeout --signal=KILL 600s rocq compile -Q . CyclistRocq LPL/Benchmarks/NestedProgram.v
```

## Scope and assumptions

Formulas have nine primitive constructors; Falsity, Disj, Impl, Ex, DualSuffix and Diamond are definitions. PrimitiveSyntax checks their expansions, independent overlapping primitive/derived rule matches, typed capture avoidance, occurrence tags and empty-trace semantics. All requested rule families remain available; generators return proof-backed records and check sorts, arities, pure bodies, labels, tags, conclusions, and edge endpoints. RuleCoverage retains its 50 exact premise-list checks; UserStructures and UpdateAlgebra cover heterogeneous typing, same-sort capture avoidance, vacuous-request rejection, snapshot updates and trace-preserving update rules. Pure goals stop at the caller-supplied proof boundary.

Cyclic and CyclicTags are actual star cycles with explicit finite tag/potential witnesses and a typed parallel-update initial label. They preserve a first-state observation. CounterLoop and NestedProgram separately prove properties of **every visited state**, over arbitrary finite iterations; these two complex invariants are direct semantic proofs, not cyclic graph certificates. No claim of mandatory loop exit is made.

Print Assumptions output is retained in the linked logs. The union for concrete exported theorems and representative rule/certification kernels consists only of standard-library classical excluded middle, definite/indefinite description, and functional extensionality. No project-defined soundness axioms or admitted proofs are used. Signature/model parameters in the abstract-model functors are explicit parameters, not soundness assumptions.

The framework witness is conservative: it chooses at most one tag per node. Acceptance of every manuscript preproof is not claimed. No proof search, witness discovery, external solver, or project FirstOrder/LTL imports are present.

## Development timeout and simplification

During the original single-sort implementation, an initial Cyclic.v run hit the 600-second limit (exit 137) while kernel conversion compared an entire proof-carrying backlink record in an auxiliary existential example. That auxiliary check was replaced with a Boolean check of the node payload and companion index. The real backlink, star graph, semantic rules, certificate, and validity theorem were retained. The final timed run is reported above. No expensive obligation was retried with a larger limit.

## Immutable framework

```text
Cyclic/Framework.v  b9f93e89931a196bb1d2f7649f240cb65920ed972fa02a2ae4af46a2e7a3ce02
Cyclic/Relations.v  85f1f25747e3eb661f24f50b6a9e6aae3cbcb173169bb7bfb6d06ac7addeb90f
```

The complete Cyclic directory also matched the pre-implementation file manifest during the implementation audit.

See [VALIDATION.md](VALIDATION.md) for the independent kernel check, existing-theory regressions, and source-scope audit.
