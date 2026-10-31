#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-only
# Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root.
"""Compile local-unfolding cyclic certificates, with a hard 600s per unit."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def run(command: list[str], log: Path) -> dict:
    start = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    elapsed = time.monotonic() - start
    log.write_text(result.stdout)
    if result.returncode:
        print(result.stdout, end="", flush=True)
    return {"command": command, "exit_status": result.returncode,
            "elapsed_seconds": elapsed, "log": str(log.relative_to(HERE))}


BENCHMARKS = {
    "StraightLine": "proposition-only machine; local unfold/sequence proof; checked acyclic graph; concrete run, all-depth safety, final 2, source rejection",
    "Branching": "unconditional and conditional machines; two checked graphs; both outcomes, guard rejection, all-depth safety",
    "Counter": "countdown; actual backlink and checked progress; all-depth safety and Box/Always; final zero; complete run for every natural input",
    "Cycle": "two-state cycle; prefix and terminal graphs with actual backlinks; arbitrary rounds; prefix safety; terminal impossibility",
    "Validation": "positive/negative cases; terminal stutter, absent paths, contradictory description, sorts/arity/purity; stalled cycle and exhausted builder rejected",
}


def rocq_code(text: str) -> str:
    """Ignore nested comments when auditing declarations and references."""
    pieces = re.split(r"(\(\*|\*\))", text)
    depth = 0
    code = []
    for piece in pieces:
        if piece == "(*":
            depth += 1
        elif piece == "*)" and depth:
            depth -= 1
        elif not depth:
            code.append(piece)
    return " ".join(code)


def audit_sources() -> dict:
    files = sorted(HERE.glob("*.v")) + sorted((HERE / "Cases").glob("*.v"))
    files += sorted((HERE / "Benchmarks").glob("*.v"))
    forbidden = re.compile(r"\b(?:encode|encode_to|encode_initial|encode_prefix|paths|route)\b")
    for path in files:
        code = rocq_code(path.read_text())
        if forbidden.search(code):
            raise SystemExit(f"Whole-graph compiler reference in {path.relative_to(ROOT)}")
        if re.search(r"\bbindings\b", code):
            raise SystemExit(f"Removed binding field in {path.relative_to(ROOT)}")
    return {"whole_graph_compiler_references": 0, "binding_fields": 0,
            "files": [str(p.relative_to(ROOT)) for p in files]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel-check", action="store_true")
    args = parser.parse_args()
    audit = audit_sources()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    logs = HERE / "benchmarks-log" / stamp
    logs.mkdir(parents=True, exist_ok=False)
    compiler = subprocess.run(["rocq", "--version"], cwd=ROOT, text=True,
                              stdout=subprocess.PIPE, check=True).stdout.strip()
    common = run(["make", "lpl-asm-unfold-common"], logs / "common.txt")
    if common["exit_status"]:
        return 1
    records = []
    for name, evidence in BENCHMARKS.items():
        source = f"LPL/ASM/Benchmarks/{name}.v"
        command = ["timeout", "--signal=KILL", "600s", "rocq", "compile",
                   "-Q", ".", "CyclistRocq", source]
        row = run(command, logs / f"{name}.txt")
        output = (logs / f"{name}.txt").read_text()
        row.update(benchmark=name, source=source, evidence=evidence,
                   graphs=[{"name": label, "nodes": int(nodes), "backlinks": int(links)}
                           for label, nodes, links in re.findall(r"GRAPH (\w+) (\d+) (\d+)", output)])
        records.append(row)
        print(f"{name}: exit {row['exit_status']}, {row['elapsed_seconds']:.3f}s, {row['graphs']}", flush=True)
    passed = sum(row["exit_status"] == 0 for row in records)
    kernel = None
    if args.kernel_check and passed == len(records):
        command = ["timeout", "--signal=KILL", "600s", "rocq", "check", "-silent", "-Q", ".", "CyclistRocq"]
        command += [f"CyclistRocq.LPL.ASM.Benchmarks.{name}" for name in BENCHMARKS]
        kernel = run(command, logs / "kernel-check.txt")
        print(f"Kernel check: exit {kernel['exit_status']}, {kernel['elapsed_seconds']:.3f}s", flush=True)
    sources = sorted(HERE.glob("*.v")) + sorted((HERE / "Cases").glob("*.v"))
    sources += sorted((HERE / "Benchmarks").glob("*.v"))
    sources += sorted(HERE.parent.glob("*.v"))
    sources += [ROOT / "LPL/Benchmarks/Support.v", ROOT / "Cyclic/Relations.v", ROOT / "Cyclic/Framework.v",
                ROOT / "Makefile", ROOT / "_CoqProject", Path(__file__).resolve()]
    manifest = {"run_utc": stamp, "compiler": compiler, "timeout_seconds": 600,
                "common": common, "audit": audit, "benchmarks": records, "kernel_check": kernel,
                "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in sources}}
    (HERE / "UNFOLD_BENCHMARK_RESULTS.json").write_text(json.dumps(manifest, indent=2) + "\n")
    lines = ["# Local-unfolding benchmark results", "", f"UTC: `{stamp}`. **{passed}/{len(records)} passed.**", "",
             "Each unit uses `timeout --signal=KILL 600s`. State descriptions contain only propositions.",
             "Source audit: no whole-machine compiler declarations/calls or binding fields in active Rocq sources.", "",
             "| Benchmark | Seconds | Exit | Evidence | Compiler / assumptions |",
             "| --- | ---: | ---: | --- | --- |"]
    for row in records:
        lines.append(f"| {row['benchmark']} | {row['elapsed_seconds']:.3f} | {row['exit_status']} | "
                     f"{row['evidence']} | [log]({row['log']}) |")
    lines += ["", "## Checked proof graphs", "", "| Graph | Nodes | Backlinks |", "| --- | ---: | ---: |"]
    for row in records:
        for g in row["graphs"]:
            lines.append(f"| {g['name']} | {g['nodes']} | {g['backlinks']} |")
    lines += ["", f"[Common build]({common['log']}): exit {common['exit_status']}.", ""]
    if kernel is not None:
        lines += [f"[Independent kernel check]({kernel['log']}): exit {kernel['exit_status']}, "
                  f"{kernel['elapsed_seconds']:.3f}s.", ""]
    lines += ["## Proof scope", "",
              "These are actual generic cyclic-framework graphs, with proof-carrying sequence/choice rules, "
              "a proved one-step `unfold_at` rule and exact backlink rules. The framework and LPL syntax/semantics "
              "are unchanged. The continuation-goal theory is a separate instance of that framework; it is not "
              "the labelled-sequent instance from LPL/Certification.v. Local instruction leaves carry the "
              "existing LPL semantic safety proofs (including the guarded decrement).", "",
              "Calls are interpreted using arbitrary finite-depth LPL program approximants. Depth is quantified "
              "over every natural number, not fixed as a benchmark cutoff. Opening a call consumes one depth "
              "unit and therefore strictly decreases a false-goal rank. Sequence, choice and backlinks preserve "
              "that rank; the finite witness potential decreases between unfoldings. Certificate soundness, "
              "not an induction proof of the global invariant, yields the exported safety and endpoint claims.", "",
              "The builder's value 100 bounds proof-construction work only; an exhausted graph is rejected. "
              "Terminal calls stop with one observation. "
              "The machines, invariants and arithmetic outcomes are tested with explicit execution witnesses for nonvacuity.", "",
              "The assumption logs use only standard-library excluded middle, constructive indefinite description "
              "for counterexample selection, and functional extensionality for closed-cycle valuation equality. "
              "No admitted proofs or new project soundness axioms are used.", "",
              "## Reproduce", "", "```sh", "# from Rocq-copy/",
              "python3 LPL/ASM/run_unfold_benchmarks.py --kernel-check", "```", ""]
    (HERE / "UNFOLD_BENCHMARK_RESULTS.md").write_text("\n".join(lines))
    return 0 if passed == len(records) and (kernel is None or kernel["exit_status"] == 0) else 1


if __name__ == "__main__":
    raise SystemExit(main())
