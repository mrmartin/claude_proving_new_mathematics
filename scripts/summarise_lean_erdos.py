#!/usr/bin/env python3
"""
Summarise catalogue/formal_conjectures_erdos.jsonl and join it against
catalogue/erdosproblems.jsonl to produce a Goal-2 candidate shortlist.
"""

from __future__ import annotations

import collections
import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_JSONL = REPO_ROOT / "catalogue" / "formal_conjectures_erdos.jsonl"
WEB_JSONL = REPO_ROOT / "catalogue" / "erdosproblems.jsonl"


def load_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def main() -> int:
    decls = load_jsonl(LEAN_JSONL)
    web = {r["id"]: r for r in load_jsonl(WEB_JSONL) if r.get("exists")}

    print(f"declarations in Lean Erdős corpus: {len(decls)}")
    print(f"unique problem ids: {len({d['problem_id'] for d in decls})}")
    print()

    by_cat = collections.Counter(d["category"] for d in decls)
    print("## Category distribution (declaration-level)")
    for k, v in by_cat.most_common():
        print(f"  {k:<20} {v}")
    print()

    sorry_by_cat = collections.Counter(
        (d["category"], not d["has_sorry_free_proof"]) for d in decls
    )
    print("## Sorry status by category")
    print("  category              has_sorry  count")
    for (cat, has_sorry), count in sorted(sorry_by_cat.items()):
        print(f"  {cat:<20}  {str(has_sorry):<8}  {count}")
    print()

    # formal_proof annotations
    fp_kinds = collections.Counter(
        d.get("formal_proof_kind") for d in decls if d.get("formal_proof_kind")
    )
    print("## formal_proof annotations (declaration-level)")
    for k, v in fp_kinds.most_common():
        print(f"  {k:<25} {v}")
    print(f"  declarations without any formal_proof annotation: "
          f"{sum(1 for d in decls if not d.get('formal_proof_kind'))}")
    print()

    # Goal-2 candidate pool, declaration-level.
    # - has_sorry_free_proof == False (i.e. body still :sorry)
    # - no formal_proof annotation pointing elsewhere (those are "shipped")
    # - category "research solved" or "textbook" (informally known)
    # - erdosproblems.com page does not carry "(LEAN)" in its label
    goal2 = []
    for d in decls:
        if d.get("has_sorry_free_proof"):
            continue
        if d.get("formal_proof_kind"):
            continue
        cat = d.get("category", "")
        if cat not in {"research solved", "textbook"}:
            continue
        pid = d["problem_id"]
        web_row = web.get(pid)
        web_label = (web_row or {}).get("status_label") or ""
        if "(LEAN)" in web_label:
            # Page knows of a Lean proof somewhere — could still be missing
            # for *this* sub-claim but flag separately.
            continue
        goal2.append((pid, d["theorem"], cat, web_label or "?"))
    goal2.sort()

    print(f"## Goal-2 candidate declarations (Erdős): {len(goal2)}")
    print("  one row = one declaration whose body is `:= by sorry`,")
    print("  with no formal_proof annotation, in category research solved or textbook,")
    print("  whose erdosproblems.com page does not carry the (LEAN) suffix.")
    print()
    print("  pid    page-status      category          theorem")
    for pid, name, cat, web_label in goal2[:40]:
        print(f"  #{pid:<5} {web_label:<16} {cat:<17} {name}")
    if len(goal2) > 40:
        print(f"  ... ({len(goal2) - 40} more)")
    print()

    # Independent sanity: pages tagged (LEAN) vs declarations marked as
    # having a formal_proof using formal_conjectures annotation.
    lean_label_ids = {pid for pid, r in web.items()
                      if "(LEAN)" in (r.get("status_label") or "")}
    decls_with_link = collections.Counter(d["problem_id"] for d in decls
                                          if d.get("formal_proof_kind"))
    overlap = sum(1 for pid in lean_label_ids if pid in decls_with_link)
    print("## Cross-check: pages tagged (LEAN) ↔ declarations with a formal_proof annotation")
    print(f"  pages with (LEAN) label: {len(lean_label_ids)}")
    print(f"  problem ids with at least one declaration having a formal_proof annotation: "
          f"{len(decls_with_link)}")
    print(f"  intersection: {overlap}")

    # cambie sanity
    cambie = [d for d in decls if d["theorem"].endswith(".variants.cambie")]
    print()
    print("## Cambie sanity (we proved this, so has_sorry_free_proof should now be True locally)")
    for d in cambie:
        print(f"  {d['theorem']}: has_sorry_free_proof={d['has_sorry_free_proof']}, "
              f"category={d['category']}, formal_proof={d.get('formal_proof_kind')}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
