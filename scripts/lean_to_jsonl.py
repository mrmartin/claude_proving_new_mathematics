#!/usr/bin/env python3
"""
Convert the JSON output of `lake exe extract_names FormalConjectures/ErdosProblems`
into a one-record-per-line JSONL file with an added `problem_id` field
(extracted from the module name, e.g. `FormalConjectures.ErdosProblems.«399»` →
`399`) and an `erdosproblems_url` cross-link.

Usage:
  cd formal-conjectures && lake exe extract_names FormalConjectures/ErdosProblems > /tmp/out.json
  python3 scripts/lean_to_jsonl.py --input /tmp/out.json \
      --output catalogue/formal_conjectures_erdos.jsonl
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_INPUT = Path("/tmp/extract_erdos.json")
DEFAULT_OUTPUT = REPO_ROOT / "catalogue" / "formal_conjectures_erdos.jsonl"
ERDOS_DIR_PATTERN = re.compile(r"FormalConjectures\.ErdosProblems\.«(\d+)»")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    p.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = p.parse_args()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    obj = json.loads(args.input.read_text(encoding="utf-8"))
    problems = obj.get("problems", [])
    module_docs = obj.get("moduleDocstrings", {})

    written = 0
    skipped_no_id = 0
    with args.output.open("w", encoding="utf-8") as fh:
        for entry in problems:
            module = entry.get("module") or ""
            m = ERDOS_DIR_PATTERN.match(module)
            if m is None:
                skipped_no_id += 1
                continue
            problem_id = int(m.group(1))
            row = {
                "problem_id": problem_id,
                "theorem": entry.get("theorem"),
                "module": module,
                "category": entry.get("category"),
                "subjects": entry.get("subjects"),
                "statement": entry.get("statement"),
                "docstring": entry.get("docstring"),
                "formal_proof_kind": entry.get("formalProofKind"),
                "formal_proof_link": entry.get("formalProofLink"),
                "has_sorry_free_proof": entry.get("hasSorryFreeProof"),
                "module_docstring": module_docs.get(module),
                "erdosproblems_url": f"https://www.erdosproblems.com/{problem_id}",
                "lean_file": f"FormalConjectures/ErdosProblems/{problem_id}.lean",
            }
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            written += 1
    print(f"wrote {written} records to {args.output}", file=sys.stderr)
    if skipped_no_id:
        print(f"  skipped {skipped_no_id} declarations whose module is not under ErdosProblems", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
