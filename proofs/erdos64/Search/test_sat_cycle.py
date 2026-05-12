#!/usr/bin/env python3
"""
Validate `sat_cycle.has_cycle_of_length_sat_fast` against the DFS-based
`exhaustive_cubic.has_cycle_of_length` on:

  (a) the 11-graph named-cubic corpus from `check_cubic.py`;
  (b) a 100-graph random sample from `geng -cd3 -D3 14` (509 connected
      cubic graphs total — we sample 100).

For each (graph, L) pair with L ∈ {3, 4, 5, 6, 7, 8, 10, 12, 14}, both
backends must agree. Discrepancy => fail with a graph6 dump.

Run:
    python3 test_sat_cycle.py
"""

from __future__ import annotations

import random
import subprocess
import sys
import time

import networkx as nx

from sat_cycle import has_cycle_of_length_sat_fast
from exhaustive_cubic import has_cycle_of_length, find_geng


GRAPH6_CORPUS = [
    # (name, networkx-builder, n)
    ("K_4", lambda: nx.complete_graph(4), 4),
    ("K_{3,3}", lambda: nx.complete_bipartite_graph(3, 3), 6),
    ("3-prism", lambda: nx.cartesian_product(nx.cycle_graph(3), nx.path_graph(2)), 6),
    ("Q_3 (3-cube)", lambda: nx.hypercube_graph(3), 8),
    ("Petersen", nx.petersen_graph, 10),
    ("5-prism", lambda: nx.cartesian_product(nx.cycle_graph(5), nx.path_graph(2)), 10),
    ("Möbius-Kantor", nx.moebius_kantor_graph, 16),
    ("Heawood", nx.heawood_graph, 14),
    ("Pappus", nx.pappus_graph, 18),
    ("Desargues", nx.desargues_graph, 20),
    ("Tutte (46v)", nx.tutte_graph, 46),
]


def to_g6(G: nx.Graph) -> tuple[bytes, int]:
    """Return (graph6 bytes, vertex count) for G, after relabelling to integers."""
    G = nx.convert_node_labels_to_integers(G)
    g6 = nx.to_graph6_bytes(G, header=False).strip()
    return g6, G.number_of_nodes()


def check_pair(g6: bytes, n: int, name: str, lengths: list[int]) -> int:
    """Compare SAT and DFS on `(g6, L)` for L in `lengths`; return failure count."""
    failures = 0
    G_dfs = nx.from_graph6_bytes(g6)
    for L in lengths:
        if L > n or L < 3:
            continue
        sat_result = has_cycle_of_length_sat_fast(g6, n, L)
        dfs_result = has_cycle_of_length(G_dfs, L)
        if sat_result != dfs_result:
            print(f"  MISMATCH on {name} L={L}: SAT={sat_result} DFS={dfs_result}")
            print(f"    graph6: {g6.decode()}")
            failures += 1
    return failures


def main(argv: list[str]) -> int:
    print("=== Part 1: 11-graph named-cubic corpus ===")
    lengths_small = [3, 4, 5, 6, 7, 8]
    lengths_big = [10, 12, 14]
    total_fail = 0
    for name, builder, n_expected in GRAPH6_CORPUS:
        G = builder()
        g6, n = to_g6(G)
        assert n == n_expected, f"size mismatch for {name}: {n} vs {n_expected}"
        t0 = time.time()
        fail = check_pair(g6, n, name, lengths_small + lengths_big)
        dt = time.time() - t0
        status = "OK" if fail == 0 else f"FAIL ({fail} mismatches)"
        print(f"  {name:<20} n={n:>3}   {status}   ({dt:.2f}s)")
        total_fail += fail

    print()
    print("=== Part 2: 100-graph random sample from geng -cd3 -D3 14 ===")
    geng = find_geng()
    proc = subprocess.run(
        [geng, "-cd3", "-D3", "14", "-q"],
        capture_output=True, text=True, check=True,
    )
    all_g6 = [line.strip() for line in proc.stdout.split("\n") if line.strip()]
    print(f"  geng emitted {len(all_g6)} connected cubic graphs on 14 vertices.")
    random.seed(42)
    sample = random.sample(all_g6, k=min(100, len(all_g6)))
    print(f"  Sampling {len(sample)} of them for SAT-vs-DFS round-trip.")
    t0 = time.time()
    for i, g6_str in enumerate(sample):
        g6 = g6_str.encode()
        fail = check_pair(g6, 14, f"sample-{i}", [3, 4, 5, 6, 7, 8, 10, 12, 14])
        total_fail += fail
        if (i + 1) % 20 == 0:
            print(f"  [{i+1}/{len(sample)}] {time.time()-t0:.1f}s elapsed")
    dt = time.time() - t0
    print(f"  Sample done in {dt:.2f}s.")

    print()
    if total_fail == 0:
        print(f"ALL TESTS PASS. SAT ↔ DFS agree on every checked (graph, L) pair.")
        return 0
    print(f"!!! {total_fail} mismatches. Audit `sat_cycle.py` before scaling.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
