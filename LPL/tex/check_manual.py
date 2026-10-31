#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-only
# Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root.
"""Check this manual's local references and reviewed source snapshot.

These checks detect broken references and source drift. They do not prove
that a mathematical restatement is equivalent to its linked Rocq theorem.
Only --refresh writes the snapshot and declaration index.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
LPL = HERE.parent
ROCQ = LPL.parent
SNAPSHOT = HERE / "sources.json"
INDEX = HERE / "DECLARATIONS.md"
DECL = re.compile(
    r"(?:\b(?:Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Variant|"
    r"Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|Parameter|"
    r"Module(?:\s+Type)?(?:\s+(?:Export|Import))?)|^[ \t]*with)\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)


def uncomment_rocq(content: str) -> str:
    """Strip nested Rocq comments, retaining offsets and line numbers."""
    result: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(content):
        pair = content[i:i + 2]
        if not quoted and pair == "(*":
            depth += 1
            result.extend("  ")
            i += 2
        elif depth and pair == "*)":
            depth -= 1
            result.extend("  ")
            i += 2
        else:
            char = content[i]
            if not depth and char == '"':
                # Rocq escapes a quote inside a string by doubling it.
                if quoted and pair == '""':
                    result.extend("  ")
                    i += 2
                    continue
                quoted = not quoted
            result.append(char if char == "\n" or not (depth or quoted) else " ")
            i += 1
    return "".join(result)


def uncomment_tex(content: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", content)


def inspect_manual() -> tuple[dict, list[str]]:
    errors: list[str] = []
    files: dict[Path, str] = {}

    def visit(path: Path) -> None:
        path = path.resolve()
        if path in files:
            return
        if path.parent != HERE or not path.is_file():
            errors.append(f"Missing or external LaTeX input: {path}")
            return
        content = uncomment_tex(path.read_text())
        files[path] = content
        for name in re.findall(r"\\input\{([^}]+)\}", content):
            visit(HERE / (name if Path(name).suffix else name + ".tex"))

    visit(HERE / "lpl.tex")
    orphaned = set(HERE.glob("*.tex")) - set(files)
    errors.extend(f"Unreferenced section: {p.name}" for p in sorted(orphaned))

    labels: dict[str, str] = {}
    references: set[str] = set()
    links: set[tuple[str, str]] = set()
    for path, content in files.items():
        for label in re.findall(r"\\label\{([^}]+)\}", content):
            if label in labels:
                errors.append(f"Duplicate label {label} in {path.name} and {labels[label]}")
            labels[label] = path.name
        references.update(re.findall(r"\\(?:ref|eqref|pageref)\*?\{([^}]+)\}", content))
        links.update(re.findall(r"\\rocq\{([^}]+)\}\{([^}]+)\}", content))
        if re.search(r"\b(?:TODO|FIXME|TBD)\b|\[VERIFY\]", content):
            errors.append(f"Unfinished text marker in {path.name}")
    errors.extend(f"Undefined label: {name}" for name in sorted(references - set(labels)))

    # Record the complete implementation and benchmark corpus, not just files
    # linked in prose. This catches relevant changes without a renamed theorem.
    source_paths = set(LPL.glob("*.v")) | set((LPL / "Benchmarks").glob("*.v"))
    source_paths.update((ROCQ / "Cyclic").glob("*.v"))
    declarations: dict[Path, dict[str, int]] = {}
    hashes: dict[str, str] = {}
    for path in sorted(source_paths):
        path = path.resolve()
        hashes[str(path.relative_to(ROCQ))] = hashlib.sha256(path.read_bytes()).hexdigest()
        stripped = uncomment_rocq(path.read_text())
        names: dict[str, int] = {}
        for match in DECL.finditer(stripped):
            names.setdefault(match[1], stripped.count("\n", 0, match.start(1)) + 1)
        declarations[path] = names

    resolved_links: list[dict] = []
    for filename, name in sorted(links):
        path = (LPL / filename).resolve()
        if path not in declarations:
            errors.append(f"Missing or untracked source file: {filename}")
            continue
        line = declarations[path].get(name)
        if line is None:
            errors.append(f"Declaration not found: {filename}:{name}")
            continue
        resolved_links.append({"file": filename, "declaration": name, "line": line})

    return {
        "format_version": 1,
        "description": "Reviewed LPL reference source snapshot; SHA-256 of Rocq sources.",
        "files": hashes,
        "references": resolved_links,
    }, errors


def declaration_index(snapshot: dict) -> str:
    lines = [
        "# Rocq declaration index", "",
        "Generated by `python3 check_manual.py --refresh` after reviewing the manual.",
        "Paths are relative to this directory; line numbers identify the recorded snapshot.",
        "", "| Source | Declaration | Line |", "| --- | --- | ---: |",
    ]
    for item in snapshot["references"]:
        filename, name, line = item["file"], item["declaration"], item["line"]
        lines.append(f"| [{filename}](../{filename}#L{line}) | `{name}` | {line} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true",
                        help="Write reviewed source hashes and declaration links after content review.")
    args = parser.parse_args()
    snapshot, errors = inspect_manual()
    if errors:
        print("Manual checks failed:\n" + "\n".join(f"- {e}" for e in errors), file=sys.stderr)
        return 1

    if args.refresh:
        SNAPSHOT.write_text(json.dumps(snapshot, indent=2) + "\n")
        INDEX.write_text(declaration_index(snapshot))
    else:
        if not SNAPSHOT.is_file():
            print("Missing sources.json; review content and use --refresh.", file=sys.stderr)
            return 1
        recorded = json.loads(SNAPSHOT.read_text())
        if recorded != snapshot:
            old_hashes, new_hashes = recorded.get("files", {}), snapshot["files"]
            changed = sorted(name for name in old_hashes.keys() | new_hashes.keys()
                             if old_hashes.get(name) != new_hashes.get(name))
            details = ", ".join(changed) or "manual declaration references"
            print(f"Snapshot changed: {details}. Review the affected manual content, "
                  "then run with --refresh.", file=sys.stderr)
            return 1
        if not INDEX.is_file() or INDEX.read_text() != declaration_index(snapshot):
            print("Declaration index is stale; refresh it after review.", file=sys.stderr)
            return 1

    print(f"Manual checks passed: {len(snapshot['files'])} Rocq files, "
          f"{len(snapshot['references'])} distinct declaration links, "
          "all LaTeX inputs and cross-references resolved.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
