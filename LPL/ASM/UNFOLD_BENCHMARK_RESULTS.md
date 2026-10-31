# Local-unfolding benchmark results

UTC: `20261030T203159030112Z`. **5/5 passed.**

Each unit uses `timeout --signal=KILL 600s`. State descriptions contain only propositions.
Source audit: no whole-machine compiler declarations/calls or binding fields in active Rocq sources.

| Benchmark | Seconds | Exit | Evidence | Compiler / assumptions |
| --- | ---: | ---: | --- | --- |
| StraightLine | 1.037 | 0 | proposition-only machine; local unfold/sequence proof; checked acyclic graph; concrete run, all-depth safety, final 2, source rejection | [log](benchmarks-log/20261030T203159030112Z/StraightLine.txt) |
| Branching | 1.057 | 0 | unconditional and conditional machines; two checked graphs; both outcomes, guard rejection, all-depth safety | [log](benchmarks-log/20261030T203159030112Z/Branching.txt) |
| Counter | 1.502 | 0 | countdown; actual backlink and checked progress; all-depth safety and Box/Always; final zero; complete run for every natural input | [log](benchmarks-log/20261030T203159030112Z/Counter.txt) |
| Cycle | 2.103 | 0 | two-state cycle; prefix and terminal graphs with actual backlinks; arbitrary rounds; prefix safety; terminal impossibility | [log](benchmarks-log/20261030T203159030112Z/Cycle.txt) |
| Validation | 1.244 | 0 | positive/negative cases; terminal stutter, absent paths, contradictory description, sorts/arity/purity; stalled cycle and exhausted builder rejected | [log](benchmarks-log/20261030T203159030112Z/Validation.txt) |

## Checked proof graphs

| Graph | Nodes | Backlinks |
| --- | ---: | ---: |
| StraightLine | 16 | 0 |
| Nondeterministic | 20 | 0 |
| Conditional | 20 | 0 |
| Counter | 15 | 1 |
| PrefixCycle | 15 | 1 |
| TerminalCycle | 11 | 1 |
| Stopped | 6 | 0 |
| Contradictory | 6 | 0 |
| Disconnected | 4 | 0 |

[Common build](benchmarks-log/20261030T203159030112Z/common.txt): exit 0.

[Independent kernel check](benchmarks-log/20261030T203159030112Z/kernel-check.txt): exit 0, 34.262s.

## Proof scope

These are actual generic cyclic-framework graphs, with proof-carrying sequence/choice rules, a proved one-step `unfold_at` rule and exact backlink rules. The framework and LPL syntax/semantics are unchanged. The continuation-goal theory is a separate instance of that framework; it is not the labelled-sequent instance from LPL/Certification.v. Local instruction leaves carry the existing LPL semantic safety proofs (including the guarded decrement).

Calls are interpreted using arbitrary finite-depth LPL program approximants. Depth is quantified over every natural number, not fixed as a benchmark cutoff. Opening a call consumes one depth unit and therefore strictly decreases a false-goal rank. Sequence, choice and backlinks preserve that rank; the finite witness potential decreases between unfoldings. Certificate soundness, not an induction proof of the global invariant, yields the exported safety and endpoint claims.

The builder's value 100 bounds proof-construction work only; an exhausted graph is rejected. Terminal calls stop with one observation. The machines, invariants and arithmetic outcomes are tested with explicit execution witnesses for nonvacuity.

The assumption logs use only standard-library excluded middle, constructive indefinite description for counterexample selection, and functional extensionality for closed-cycle valuation equality. No admitted proofs or new project soundness axioms are used.

## Reproduce

```sh
# from Rocq-copy/
python3 LPL/ASM/run_unfold_benchmarks.py --kernel-check
```
