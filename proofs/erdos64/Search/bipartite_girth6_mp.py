#!/usr/bin/env python3
"""
Multiprocessing variant of `bipartite_girth6.py` for large `n`.

The single-process version takes ~342 s at `n = 24` (162 girth-6 graphs);
the bottleneck is per-graph parse + girth filter, not SAT. With
`multiprocessing.Pool`, expect near-linear speedup until `geng` itself
saturates a CPU.

Pipeline (same as buffered variant, but parallelised):
  geng -bcd3 -D3 n        # spawned via subprocess.Popen, streamed
       │
       ▼ batches of graph6 lines
  Pool of workers, each:
       parse(g6) → adj → girth → (if girth == 6) SAT-check C_8 (and
       larger 2^k if no C_8) → status tag
       │
       ▼ imap_unordered
  Aggregator: count, emit running progress, save JSON.

Run:
    python3 bipartite_girth6_mp.py 26
    python3 bipartite_girth6_mp.py 28 --workers 24
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
    """Compute the girth of a graph given as an immutable adjacency list.
    Returns `sys.maxsize` if the graph is acyclic. Pure-Python BFS,
    early-exits when no shorter cycle is reachable from `v`."""
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


def _worker(args: tuple[bytes, int]) -> tuple[bytes, str]:
    """Process one graph6 line.

    Returns `(g6, tag)` with tag ∈ {`not_g6`, `has_c8`, `no_c8_k{k}`,
    `no_2pow`}.
    """
    g6_bytes, n = args
    adj = _parse_g6_adj(g6_bytes, n)
    g = _fast_girth_adj(adj)
    if g != 6:
        return (g6_bytes, "not_g6")
    g6_str = g6_bytes.decode()
    for k in range(2, 8):
        L = 2 ** k
        if L > n:
            return (g6_bytes, "no_2pow")
        if has_cycle_of_length_sat_fast(g6_str, n, L):
            if k == 3:
                return (g6_bytes, "has_c8")
            return (g6_bytes, f"no_c8_k{k}")
    return (g6_bytes, "no_2pow")


def _feed(proc_stdout, n: int):
    for line in proc_stdout:
        g6 = line.strip()
        if not g6:
            continue
        yield (g6, n)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python3 bipartite_girth6_mp.py <n> [--workers W]"
              " [--chunksize C]")
        return 2
    n = int(argv[1])
    workers = mp.cpu_count()
    chunksize = 64
    if "--workers" in argv:
        workers = int(argv[argv.index("--workers") + 1])
    if "--chunksize" in argv:
        chunksize = int(argv[argv.index("--chunksize") + 1])
    if n < 14 or n > 40 or n % 2:
        print(f"n must be even and in [14, 40] (got n={n})")
        return 2

    geng = find_geng()
    cmd = [geng, "-bcd3", "-D3", str(n), "-q"]
    print(f"Phase 3A MP: bipartite cubic girth-6 at n={n}, workers={workers},"
          f" chunksize={chunksize}")
    print(f"  Spawning: {' '.join(cmd)}")
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, bufsize=1)
    if proc.stdout is None:
        raise RuntimeError("subprocess.Popen returned None stdout")

    total_bipartite = 0
    total_girth6 = 0
    failures_no_8: list[tuple[str, int]] = []
    candidates: list[str] = []
    last_print = t0

    with mp.Pool(workers) as pool:
        # imap_unordered over the streamed geng output.
        feeder = _feed(proc.stdout, n)
        # We use a wrapper iterator that also bumps `total_bipartite` as
        # graphs flow in (counts everything, not just girth-6).
        def counting_feeder():
            nonlocal total_bipartite
            for args in feeder:
                total_bipartite += 1
                yield args

        for g6_bytes, tag in pool.imap_unordered(_worker, counting_feeder(),
                                                  chunksize=chunksize):
            if tag == "not_g6":
                continue
            total_girth6 += 1
            if tag == "has_c8":
                pass
            elif tag == "no_2pow":
                candidates.append(g6_bytes.decode())
                print(f"  !!! CANDIDATE: g6={g6_bytes.decode()}")
            elif tag.startswith("no_c8_k"):
                k = int(tag[7:])
                failures_no_8.append((g6_bytes.decode(), k))
                print(f"  [{total_bipartite}] g6={g6_bytes.decode()}: "
                      f"has C_{2**k} but no C_8")
            now = time.time()
            if now - last_print >= 30:
                print(f"  [bipartite={total_bipartite}, girth6={total_girth6}]"
                      f" {now - t0:.0f}s")
                last_print = now

    proc.wait()
    if proc.returncode != 0:
        raise RuntimeError(f"geng exited non-zero: {proc.returncode}")
    t1 = time.time()
    print(f"Done in {t1 - t0:.1f}s. bipartite={total_bipartite},"
          f" girth6={total_girth6}.")

    results_dir = Path(__file__).parent / "results" / "bipartite_g6"
    results_dir.mkdir(parents=True, exist_ok=True)
    out = results_dir / f"n{n:02d}.json"
    out.write_text(json.dumps({
        "n": n,
        "geng_command": f"geng -bcd3 -D3 {n}",
        "total_bipartite_cubic": total_bipartite,
        "total_bipartite_cubic_girth6": total_girth6,
        "elapsed_seconds": t1 - t0,
        "workers": workers,
        "chunksize": chunksize,
        "no_C8_but_has_other_2pow": failures_no_8,
        "candidate_counterexamples_to_erdos_64": candidates,
    }, indent=2))
    print(f"Results saved to {out}.")

    if candidates:
        print()
        print("!" * 60)
        print("CANDIDATE COUNTEREXAMPLE(S) TO ERDŐS 64 — quadruple-check.")
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
