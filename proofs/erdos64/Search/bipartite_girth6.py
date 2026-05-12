#!/usr/bin/env python3
"""
Phase 3A: bipartite cubic girth-6 sub-case search.

Question (memo 0036): Does every bipartite cubic graph with girth exactly
6 contain a cycle of length 8 (= 2^3)?

If yes for all `n ≤ 32`, we **discharge the open hypothesis in
`Erdos64.has_2pow_cycle_of_isBipartite_girth_le_eight`** computationally
for n in that range. Nowbandegani-Esfandiari 2011 says any *bipartite*
counterexample to Erdős 64 has `n ≥ 32`, so the door of the open
question is exactly here.

Pipeline:
  geng -bcd3 -D3 n   # bipartite + connected + cubic
       │
       ▼
  networkx girth filter (girth == 6)
       │
       ▼
  has_cycle_of_length_sat_fast(g6, n, 8) — SAT-check for C_8
       │
       ▼
  If C_8 absent: also check C_16, C_32 — if all absent, it's a
  *true counterexample to Erdős 64*. Quadruple-check before any
  "counterexample" memo language.

Run:
    python3 bipartite_girth6.py 14
    python3 bipartite_girth6.py 18
    ...
    python3 bipartite_girth6.py 32
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

import networkx as nx

from sat_cycle import has_cycle_of_length_sat_fast
from exhaustive_cubic import find_geng, parse_graph6


def girth(G: nx.Graph) -> int:
    """Compute the girth of G; ∞ (sys.maxsize) if acyclic."""
    # networkx has `nx.girth` since 3.x; fall back to BFS if missing.
    if hasattr(nx, "girth"):
        try:
            return nx.girth(G)
        except Exception:
            pass
    # Fallback: BFS from each vertex, find shortest cycle.
    min_cycle = sys.maxsize
    for v in G.nodes():
        # BFS
        dist = {v: 0}
        parent = {v: None}
        queue = [v]
        while queue:
            next_queue = []
            for u in queue:
                for w in G.neighbors(u):
                    if w not in dist:
                        dist[w] = dist[u] + 1
                        parent[w] = u
                        next_queue.append(w)
                    elif parent[u] != w:
                        cycle_len = dist[u] + dist[w] + 1
                        if cycle_len < min_cycle:
                            min_cycle = cycle_len
            queue = next_queue
    return min_cycle


def enumerate_bipartite_cubic_girth6(n: int) -> list[str]:
    """Return graph6 strings of all connected bipartite cubic graphs on n
    vertices with girth exactly 6."""
    geng = find_geng()
    cmd = [geng, "-bcd3", "-D3", str(n), "-q"]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    if proc.returncode != 0:
        raise RuntimeError(f"geng failed: {proc.stderr}")
    all_g6 = [s.strip() for s in proc.stdout.split("\n") if s.strip()]
    result = []
    for g6 in all_g6:
        G = parse_graph6(g6, n)
        g = girth(G)
        if g == 6:
            result.append(g6)
    return result


def check_2pow_cycle_in(g6: str, n: int) -> tuple[int | None, list[int]]:
    """Find smallest k ≥ 2 with G has C_{2^k}, plus the list of k's actually
    tried. Returns (k, [tried_k]) or (None, [tried_k]) if no C_{2^k} found
    up to 2^k ≤ n."""
    tried = []
    for k in range(2, 8):
        L = 2 ** k
        if L > n:
            break
        tried.append(k)
        if has_cycle_of_length_sat_fast(g6, n, L):
            return k, tried
    return None, tried


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python3 bipartite_girth6.py <n>")
        return 2
    n = int(argv[1])
    if n < 14 or n > 40 or n % 2:
        print(f"n must be even and in [14, 40] (got n={n})")
        return 2

    print(f"Phase 3A: bipartite cubic girth-6 search at n={n}")
    print(f"  Step 1: enumerate connected bipartite cubic graphs on n={n}...")
    t0 = time.time()
    girth6 = enumerate_bipartite_cubic_girth6(n)
    t1 = time.time()
    print(f"  Found {len(girth6)} bipartite cubic graphs with girth=6 "
          f"(geng + girth filter {t1 - t0:.1f}s).")

    print(f"  Step 2: SAT-check each for a C_8...")
    failures_no_8 = []
    candidates_no_2pow = []
    for i, g6 in enumerate(girth6):
        k, tried = check_2pow_cycle_in(g6, n)
        if k is None:
            print(f"    !!! [{i}] graph6={g6!r}: NO 2^k cycle for k ∈ {tried}.")
            print(f"    THIS IS A CANDIDATE COUNTEREXAMPLE TO ERDŐS 64.")
            candidates_no_2pow.append(g6)
        elif k != 3:
            # Has 2^k cycle but not specifically C_8 (which would be unusual
            # for girth-6 bipartite cubic; record it).
            print(f"    [{i}] graph6={g6!r}: has C_{2**k} but no C_8 found.")
            failures_no_8.append((g6, k))
        if (i + 1) % max(1, len(girth6) // 10) == 0:
            print(f"    [{i+1}/{len(girth6)}] {time.time()-t1:.1f}s elapsed")
    t2 = time.time()
    print(f"  Step 2 done in {t2 - t1:.1f}s.")

    # Save results.
    results_dir = Path(__file__).parent / "results" / "bipartite_g6"
    results_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "n": n,
        "geng_command": f"geng -bcd3 -D3 {n}",
        "total_bipartite_cubic_girth6": len(girth6),
        "elapsed_enumerate_seconds": t1 - t0,
        "elapsed_check_seconds": t2 - t1,
        "no_C8_but_has_other_2pow": failures_no_8,
        "candidate_counterexamples_to_erdos_64": candidates_no_2pow,
    }
    out = results_dir / f"n{n:02d}.json"
    out.write_text(json.dumps(payload, indent=2))
    print(f"  Results saved to {out}.")

    if candidates_no_2pow:
        print()
        print("=" * 60)
        print("!!! CANDIDATE COUNTEREXAMPLE(S) TO ERDŐS 64 !!!")
        print("    Quadruple-check before any 'counterexample' claim.")
        print("=" * 60)
        return 1

    print()
    if not failures_no_8:
        print(f"OK. All {len(girth6)} bipartite cubic girth-6 graphs on n={n} "
              f"have a C_8 (= 2^3 cycle).")
    else:
        print(f"OK. All have some 2^k cycle, but {len(failures_no_8)} skip C_8.")
        print("    (Unusual; these still satisfy Erdős 64.)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
