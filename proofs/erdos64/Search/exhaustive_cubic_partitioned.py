#!/usr/bin/env python3
"""
Partitioned variant of `exhaustive_cubic.py` for Phase 2 (push to n ≥ 22).

Same `geng res/mod` partition trick as `bipartite_girth6_partitioned.py`,
applied to the full cubic enumeration `geng -cd3 -D3`. M parallel geng
processes, each in its own Python child running per-graph DFS (for
`L ∈ {4, 8}`) and SAT (for `L ∈ {16, 32}`).

Run:
    python3 exhaustive_cubic_partitioned.py 22 --slices 48
    python3 exhaustive_cubic_partitioned.py 24 --slices 48

Expected wall-time at 48 slices (per geng-count growth):
- n=20: 41 301 graphs → ~10 s
- n=22: 7.3M graphs → 30 s – 30 min
- n=24: 118M graphs → 8 – 10 hr
- n=26: 2.1B graphs → infeasible without subclass filter
"""

from __future__ import annotations

import json
import multiprocessing as mp
import subprocess
import sys
import time
from pathlib import Path

import networkx as nx

from exhaustive_cubic import find_geng, has_cycle_of_length
from sat_cycle import has_cycle_of_length_sat_fast


def _check_one(g6: bytes, n: int) -> int | None:
    """Smallest k ≥ 2 with G has C_{2^k}, or None (candidate counterexample)."""
    G = nx.from_graph6_bytes(g6)
    # k ∈ {2, 3}: DFS short-circuits trivially.
    for k in (2, 3):
        L = 2 ** k
        if L > n:
            return None
        if has_cycle_of_length(G, L):
            return k
    # k ≥ 4: SAT.
    g6_str = g6.decode() if isinstance(g6, bytes) else g6
    for k in range(4, 8):
        L = 2 ** k
        if L > n:
            return None
        if has_cycle_of_length_sat_fast(g6_str, n, L):
            return k
    return None


def run_slice(args: tuple[int, int, int]) -> dict:
    """Process one geng slice `res/mod`."""
    n, res, mod = args
    geng = find_geng()
    cmd = [geng, "-cd3", "-D3", str(n), f"{res}/{mod}", "-q"]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL)
    if proc.stdout is None:
        raise RuntimeError("Popen stdout is None")

    total = 0
    candidates: list[str] = []
    for line in proc.stdout:
        g6 = line.strip()
        if not g6:
            continue
        total += 1
        k = _check_one(g6, n)
        if k is None:
            candidates.append(g6.decode())
    proc.wait()
    if proc.returncode != 0:
        raise RuntimeError(f"geng slice {res}/{mod} exited"
                           f" {proc.returncode}")
    return {
        "res": res,
        "mod": mod,
        "total": total,
        "candidates": candidates,
    }


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python3 exhaustive_cubic_partitioned.py <n>"
              " [--slices M]")
        return 2
    n = int(argv[1])
    slices = mp.cpu_count()
    if "--slices" in argv:
        slices = int(argv[argv.index("--slices") + 1])
    if n < 4 or n > 40:
        print(f"n must be in [4, 40] (got n={n})")
        return 2

    print(f"Phase 2 partitioned: exhaustive cubic at n={n}, slices={slices}")
    t0 = time.time()
    with mp.Pool(slices) as pool:
        slice_results = pool.map(run_slice,
                                  [(n, r, slices) for r in range(slices)])
    t1 = time.time()

    total = sum(s["total"] for s in slice_results)
    candidates: list[str] = []
    for s in slice_results:
        candidates.extend(s["candidates"])

    print(f"Done in {t1 - t0:.1f}s. total cubic graphs={total},"
          f" candidates={len(candidates)}.")

    results_dir = Path(__file__).parent / "results" / "cubic"
    results_dir.mkdir(parents=True, exist_ok=True)
    out = results_dir / f"n{n:02d}.json"
    out.write_text(json.dumps({
        "n": n,
        "geng_command": f"geng -cd3 -D3 {n} (partitioned, M={slices})",
        "total_connected_cubic": total,
        "elapsed_seconds": t1 - t0,
        "slices": slices,
        "candidate_counterexamples": candidates,
    }, indent=2))
    print(f"Results saved to {out}.")

    if candidates:
        print()
        print("!" * 60)
        print("CANDIDATE COUNTEREXAMPLE(S) TO ERDŐS 64 — quadruple-check.")
        for g6 in candidates:
            print(f"  g6={g6}")
        print("!" * 60)
        return 1
    print(f"OK. All {total} connected cubic graphs on n={n} have a 2^k cycle.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
