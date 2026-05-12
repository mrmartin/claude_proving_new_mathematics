#!/usr/bin/env python3
"""
Partitioned variant of `bipartite_girth6.py` for large `n`.

The real bottleneck of `bipartite_girth6{,_mp}.py` is `geng` itself, not
the Python workers: `geng -bcd3 -D3 24 -q | wc -l` runs at ~91 graphs/s,
so worker-side parallelism gives at most a 1.05× speedup.

`geng` supports `res/mod` partitioning: `geng ... n R/M -q` generates
only graphs `i ≡ R (mod M)` in its internal canonical enumeration. The
M slices are disjoint and together cover the full enumeration. So we
can split into M parallel pipelines, each running a single `geng` and
its own Python parse+girth+SAT.

Run:
    python3 bipartite_girth6_partitioned.py 26 --slices 16
    python3 bipartite_girth6_partitioned.py 28 --slices 32
"""

from __future__ import annotations

import json
import multiprocessing as mp
import subprocess
import sys
import time
from pathlib import Path

import networkx as nx

from sat_cycle import has_cycle_of_length_sat_fast
from exhaustive_cubic import find_geng


def _fast_girth_adj(adj: list[tuple[int, ...]]) -> int:
    n = len(adj)
    min_g = sys.maxsize
    for v in range(n):
        dist = [-1] * n
        parent = [-1] * n
        dist[v] = 0
        frontier = [v]
        depth = 0
        while frontier:
            depth += 1
            if 2 * depth - 1 >= min_g:
                break
            next_frontier = []
            for u in frontier:
                du = dist[u]
                pu = parent[u]
                for w in adj[u]:
                    if dist[w] == -1:
                        dist[w] = du + 1
                        parent[w] = u
                        next_frontier.append(w)
                    elif w != pu:
                        cycle_len = du + dist[w] + 1
                        if cycle_len < min_g:
                            min_g = cycle_len
            frontier = next_frontier
    return min_g


def _parse_g6_adj(g6_bytes: bytes, n: int) -> list[tuple[int, ...]]:
    G = nx.from_graph6_bytes(g6_bytes)
    return [tuple(G.neighbors(i)) for i in range(n)]


def _check_2pow(g6_str: str, n: int) -> tuple[int | None, int]:
    """Return (k, smallest_L_tried_failed). k = None ⇒ candidate."""
    for k in range(2, 8):
        L = 2 ** k
        if L > n:
            return (None, L)
        if has_cycle_of_length_sat_fast(g6_str, n, L):
            return (k, L)
    return (None, 0)


def run_slice(args: tuple[int, int, int]) -> dict:
    """Process one geng slice `res/mod`. Returns a summary dict."""
    n, res, mod = args
    geng = find_geng()
    cmd = [geng, "-bcd3", "-D3", str(n), f"{res}/{mod}", "-q"]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL)
    if proc.stdout is None:
        raise RuntimeError("subprocess.Popen returned None stdout")

    total_bipartite = 0
    total_girth6 = 0
    failures_no_8: list[tuple[str, int]] = []
    candidates: list[str] = []
    for line in proc.stdout:
        g6 = line.strip()
        if not g6:
            continue
        total_bipartite += 1
        adj = _parse_g6_adj(g6, n)
        g = _fast_girth_adj(adj)
        if g != 6:
            continue
        total_girth6 += 1
        g6_str = g6.decode()
        k, _ = _check_2pow(g6_str, n)
        if k is None:
            candidates.append(g6_str)
        elif k != 3:
            failures_no_8.append((g6_str, k))
    proc.wait()
    if proc.returncode != 0:
        raise RuntimeError(f"geng slice {res}/{mod} exited"
                           f" {proc.returncode}")
    return {
        "res": res,
        "mod": mod,
        "total_bipartite": total_bipartite,
        "total_girth6": total_girth6,
        "failures_no_8": failures_no_8,
        "candidates": candidates,
    }


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python3 bipartite_girth6_partitioned.py <n>"
              " [--slices M]")
        return 2
    n = int(argv[1])
    slices = mp.cpu_count()
    if "--slices" in argv:
        slices = int(argv[argv.index("--slices") + 1])
    if n < 14 or n > 40 or n % 2:
        print(f"n must be even and in [14, 40] (got n={n})")
        return 2

    print(f"Phase 3A partitioned: bipartite cubic girth-6 at n={n},"
          f" slices={slices}")
    t0 = time.time()
    with mp.Pool(slices) as pool:
        slice_results = pool.map(run_slice,
                                  [(n, r, slices) for r in range(slices)])
    t1 = time.time()

    total_bipartite = sum(s["total_bipartite"] for s in slice_results)
    total_girth6 = sum(s["total_girth6"] for s in slice_results)
    failures_no_8: list[tuple[str, int]] = []
    candidates: list[str] = []
    for s in slice_results:
        failures_no_8.extend(s["failures_no_8"])
        candidates.extend(s["candidates"])

    print(f"Done in {t1 - t0:.1f}s. bipartite={total_bipartite},"
          f" girth6={total_girth6}.")

    results_dir = Path(__file__).parent / "results" / "bipartite_g6"
    results_dir.mkdir(parents=True, exist_ok=True)
    out = results_dir / f"n{n:02d}.json"
    out.write_text(json.dumps({
        "n": n,
        "geng_command": f"geng -bcd3 -D3 {n} (partitioned, M={slices})",
        "total_bipartite_cubic": total_bipartite,
        "total_bipartite_cubic_girth6": total_girth6,
        "elapsed_seconds": t1 - t0,
        "slices": slices,
        "no_C8_but_has_other_2pow": failures_no_8,
        "candidate_counterexamples_to_erdos_64": candidates,
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
    if not failures_no_8:
        print(f"OK. All {total_girth6} bipartite cubic girth-6 graphs on"
              f" n={n} have a C_8.")
    else:
        print(f"OK. All have some 2^k cycle, but {len(failures_no_8)}"
              f" skip C_8.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
