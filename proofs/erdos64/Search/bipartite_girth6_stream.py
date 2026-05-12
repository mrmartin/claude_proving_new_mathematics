#!/usr/bin/env python3
"""
Streaming version of `bipartite_girth6.py` for large `n`.

Reads `geng -bcd3 -D3 n` output line-by-line via `subprocess.Popen`
pipes, avoiding the OOM/timeout that `subprocess.run` causes when the
total `geng` output is hundreds of MB (n ≥ 28).

Same check as the non-streaming version:
  for each connected bipartite cubic graph with girth = 6, find the
  smallest k ≥ 2 such that the graph has a 2^k cycle.

Run:
    python3 bipartite_girth6_stream.py 26
    python3 bipartite_girth6_stream.py 28
    python3 bipartite_girth6_stream.py 30
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

import networkx as nx

from sat_cycle import has_cycle_of_length_sat_fast
from exhaustive_cubic import find_geng


def girth(G: nx.Graph) -> int:
    """Compute the girth of G; sys.maxsize if acyclic."""
    if hasattr(nx, "girth"):
        try:
            return nx.girth(G)
        except Exception:
            pass
    min_cycle = sys.maxsize
    for v in G.nodes():
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


def check_2pow_cycle(g6: bytes, n: int, k_max: int = 6) -> int | None:
    """Smallest k ≥ 2 with a 2^k cycle in G, or None."""
    for k in range(2, k_max + 1):
        L = 2 ** k
        if L > n:
            return None
        if has_cycle_of_length_sat_fast(g6, n, L):
            return k
    return None


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python3 bipartite_girth6_stream.py <n>")
        return 2
    n = int(argv[1])
    if n < 14 or n > 40 or n % 2:
        print(f"n must be even and in [14, 40] (got n={n})")
        return 2

    geng = find_geng()
    cmd = [geng, "-bcd3", "-D3", str(n), "-q"]
    print(f"Phase 3A streaming: bipartite cubic girth-6 at n={n}")
    print(f"  Spawning: {' '.join(cmd)}")
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, bufsize=1)
    total_bipartite = 0
    total_girth6 = 0
    failures_no_8 = []
    candidates = []
    last_print = t0
    if proc.stdout is None:
        raise RuntimeError("subprocess.Popen returned None stdout")
    for raw_line in proc.stdout:
        g6 = raw_line.strip()
        if not g6:
            continue
        total_bipartite += 1
        G = nx.from_graph6_bytes(g6)
        g = girth(G)
        if g != 6:
            continue
        total_girth6 += 1
        k = check_2pow_cycle(g6, n)
        if k is None:
            candidates.append(g6.decode())
            print(f"    !!! CANDIDATE [{total_bipartite}] g6={g6.decode()}")
        elif k != 3:
            failures_no_8.append((g6.decode(), k))
            print(f"    [{total_bipartite}] g6={g6.decode()}: 2^{k} but no C_8")
        now = time.time()
        if now - last_print >= 30:
            print(f"  [bipartite={total_bipartite}, girth6={total_girth6}] "
                  f"{now - t0:.0f}s elapsed")
            last_print = now
    proc.wait()
    if proc.returncode != 0:
        raise RuntimeError(f"geng exited non-zero: {proc.returncode}")
    t1 = time.time()
    print(f"  Done in {t1 - t0:.0f}s.")
    print(f"  Total bipartite cubic on n={n}: {total_bipartite}")
    print(f"  Total girth-6 among those: {total_girth6}")

    results_dir = Path(__file__).parent / "results" / "bipartite_g6"
    results_dir.mkdir(parents=True, exist_ok=True)
    out = results_dir / f"n{n:02d}.json"
    out.write_text(json.dumps({
        "n": n,
        "geng_command": f"geng -bcd3 -D3 {n}",
        "total_bipartite_cubic": total_bipartite,
        "total_bipartite_cubic_girth6": total_girth6,
        "elapsed_seconds": t1 - t0,
        "no_C8_but_has_other_2pow": failures_no_8,
        "candidate_counterexamples_to_erdos_64": candidates,
    }, indent=2))
    print(f"  Results saved to {out}.")

    if candidates:
        print()
        print("!!! CANDIDATE COUNTEREXAMPLE(S) TO ERDŐS 64 — quadruple-check.")
        return 1
    if not failures_no_8:
        print(f"OK. All {total_girth6} bipartite cubic girth-6 graphs on n={n}"
              f" have a C_8.")
    else:
        print(f"OK. All have 2^k cycle, but {len(failures_no_8)} skip C_8.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
