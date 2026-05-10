#!/usr/bin/env python3
"""
Read catalogue/erdosproblems.jsonl and print a summary breakdown:
- Counts of exists / missing.
- Status label distribution.
- Formalised-in-formal-conjectures distribution.
- Cross-check against the local clone of formal-conjectures.
- Cross-reference against Subsets/FC100SolvedSet1.lean and FC100OpenSet1.lean
  (informally, by membership of the corresponding Lean file).

Use as: `python3 scripts/summarise_erdosproblems.py [--catalogue PATH]`.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CATALOGUE = REPO_ROOT / "catalogue" / "erdosproblems.jsonl"
LEAN_REPO_DIR = REPO_ROOT / "formal-conjectures"
LEAN_ERDOS_DIR = LEAN_REPO_DIR / "FormalConjectures" / "ErdosProblems"


def load(path: Path) -> list[dict]:
    rows = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--catalogue", type=Path, default=DEFAULT_CATALOGUE)
    args = p.parse_args()

    rows = load(args.catalogue)
    print(f"# Erdős-problems catalogue summary")
    print()
    print(f"records: {len(rows)}")
    exists = [r for r in rows if r.get("exists")]
    missing = [r for r in rows if not r.get("exists")]
    print(f"  exists: {len(exists)}")
    print(f"  missing (placeholder): {len(missing)}")
    print()

    # Status label distribution
    status_counts = collections.Counter(r.get("status_label") for r in exists)
    print("## Status label distribution (live records)")
    for label, count in status_counts.most_common():
        print(f"  {label or '<none>':<25} {count}")
    print()

    # Formalised-in-formal-conjectures
    formal_counts = collections.Counter(
        r.get("formalised_in_formal_conjectures") for r in exists
    )
    print("## Formalised in formal-conjectures (live records)")
    for label, count in formal_counts.most_common():
        print(f"  {str(label):<10} {count}")
    print()

    # Sanity: every formalised=True row should have a matching .lean file
    if LEAN_ERDOS_DIR.exists():
        lean_files = {int(p.stem): p for p in LEAN_ERDOS_DIR.glob("*.lean")
                      if p.stem.isdigit()}
        print(f"## Lean clone cross-check ({LEAN_ERDOS_DIR})")
        print(f"  .lean files under ErdosProblems/: {len(lean_files)}")
        formalised_yes = [r for r in exists
                          if r.get("formalised_in_formal_conjectures") is True]
        missing_lean = [r for r in formalised_yes if r["id"] not in lean_files]
        print(f"  scrape says 'formalised' but no local .lean: {len(missing_lean)}")
        if missing_lean[:3]:
            for r in missing_lean[:3]:
                print(f"    e.g. id={r['id']} url={r.get('formalised_url')}")
        # Reverse direction: .lean files exist that scrape didn't mark formalised
        scraped_yes_ids = {r["id"] for r in formalised_yes}
        unmarked = sorted(set(lean_files) - scraped_yes_ids)
        print(f"  local .lean files not flagged 'formalised' in scrape: {len(unmarked)}")
        if unmarked[:5]:
            print(f"    e.g. ids: {unmarked[:5]}")
        print()
    else:
        print(f"## Lean clone cross-check: skipped (no clone at {LEAN_ERDOS_DIR})")
        print()

    # Tag frequencies
    tag_counts = collections.Counter()
    for r in exists:
        for t in r.get("tags") or []:
            tag_counts[t] += 1
    print("## Top 20 tags")
    for tag, count in tag_counts.most_common(20):
        print(f"  {tag:<35} {count}")
    print()

    # Cross-ref with FC100SolvedSet1 and FC100OpenSet1
    benchmark_files = [
        ("FC100SolvedSet1", LEAN_REPO_DIR / "FormalConjectures/Subsets/FC100SolvedSet1.lean"),
        ("FC100OpenSet1",   LEAN_REPO_DIR / "FormalConjectures/Subsets/FC100OpenSet1.lean"),
    ]
    for name, fpath in benchmark_files:
        if not fpath.exists():
            print(f"## {name}: file missing at {fpath}; skipped")
            continue
        text = fpath.read_text(encoding="utf-8")
        ids = sorted({int(m.group(1)) for m in
                      re.finditer(r"Erdos(\d+)\.", text)})
        print(f"## {name}: {len(ids)} unique Erdős problem ids referenced")
        scraped_open = [i for i in ids if any(
            r.get("status_id") == "open" for r in exists if r["id"] == i)]
        scraped_solved = [i for i in ids if any(
            r.get("status_id") == "solved" for r in exists if r["id"] == i)]
        scraped_formalised = [i for i in ids if any(
            r.get("formalised_in_formal_conjectures") is True
            for r in exists if r["id"] == i)]
        print(f"  of which 'open' on erdosproblems.com: {len(scraped_open)}")
        print(f"  of which 'solved' on erdosproblems.com: {len(scraped_solved)}")
        print(f"  of which formalised (per scrape): {len(scraped_formalised)}")
        print()

    # Goal-2 candidate teaser. We want Erdős problems that:
    #   - have a local .lean file (statement is formalised in formal-conjectures)
    #   - are SOLVED informally (status_id == "solved" — covers
    #     PROVED / DISPROVED / SOLVED / FALSIFIABLE etc.)
    #   - do NOT carry the "(LEAN)" suffix on their status label
    #     (which would mean the page knows a Lean proof already exists,
    #     so the proof corpus is already covered)
    # The next slice (memo 0006) will further filter to those whose
    # .lean still contains naked sorries.
    if LEAN_ERDOS_DIR.exists():
        local_ids = {int(p.stem) for p in LEAN_ERDOS_DIR.glob("*.lean")
                     if p.stem.isdigit()}
        solved_local_no_lean = sorted(
            r["id"] for r in exists
            if r["id"] in local_ids
            and r.get("status_id") == "solved"
            and "(LEAN)" not in (r.get("status_label") or "")
        )
        solved_local_with_lean = sorted(
            r["id"] for r in exists
            if r["id"] in local_ids
            and r.get("status_id") == "solved"
            and "(LEAN)" in (r.get("status_label") or "")
        )
        print(f"## Goal-2 candidate pool (Erdős, statement formalised)")
        print(f"  SOLVED + statement formalised + page has NO known Lean proof: {len(solved_local_no_lean)}")
        print(f"    (these are immediate Goal-2 targets)")
        print(f"  SOLVED + statement formalised + page already cites a Lean proof: {len(solved_local_with_lean)}")
        print(f"    (skip — proof corpus already covered, look up the link)")
        if solved_local_no_lean[:10]:
            print(f"  first 10 candidate ids: {solved_local_no_lean[:10]}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
