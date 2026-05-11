#!/usr/bin/env python3
"""
Verify Erdős 64 for named small cubic graphs.

For each graph G in the table below, we check:
  (1) G is cubic (every vertex has degree 3);
  (2) G contains a cycle of length 2^k for some k >= 2.

This is the offline computational analogue of the Lean A4 module
(proofs/erdos64/Erdos64/Markstrom.lean). It serves two purposes:

  (a) A regression check: if any named cubic graph FAILS the Erdős
      64 conclusion, we want to know immediately — that would be a
      candidate counterexample to a 130-year-old open problem.

  (b) A pipeline pre-stage: graphs that pass this check are
      candidates for Lean encoding. The script writes a per-graph
      report identifying which 2^k cycle was found, suitable for
      transcription into a Pikhurko-style `inductive V` in Lean.

Run:
    python3 check_cubic.py

Dependencies:
    - networkx >= 2.8

Limitations:
    - Currently iterates over a *named* graph list. To extend to
      EVERY cubic graph on n vertices for n in {10, 12, ..., 30},
      we need `nauty`'s `geng -d3 -D3 n` (not currently installed).
      Once installed, pipe `geng` output through this script to
      verify the Markstrom bound on a fresh n.
    - SAT-style targeted counterexample search (Plan B1 full) needs
      `kissat` or `cadical` plus a SAT-encoder. See README.md.
"""

from __future__ import annotations
import networkx as nx
from typing import Iterable


# ----------------------------------------------------------------------
# Named cubic graphs we know about.
# ----------------------------------------------------------------------

def named_cubic_graphs() -> Iterable[tuple[str, nx.Graph]]:
    """A curated list of small cubic graphs."""
    # K_4 (4 vertices, the complete graph).
    yield ("K_4", nx.complete_graph(4))

    # K_{3,3} (6 vertices, complete bipartite).
    yield ("K_{3,3}", nx.complete_bipartite_graph(3, 3))

    # 3-prism = K_3 □ K_2 (6 vertices, the triangular prism).
    yield ("3-prism", nx.cartesian_product(nx.cycle_graph(3), nx.path_graph(2)))

    # 3-cube Q_3 (8 vertices, the cube). Built as the hypercube.
    yield ("Q_3 (3-cube)", nx.hypercube_graph(3))

    # K_4 ⊞ K_2 — the cube minus a perfect matching, alias Möbius-Kantor's
    # smaller cousin? Let's stick with Q_3 for 8 vertices.

    # Petersen graph (10 vertices).
    yield ("Petersen", nx.petersen_graph())

    # 5-prism = K_2 □ C_5 (10 vertices, pentagonal prism).
    yield ("5-prism", nx.cartesian_product(nx.cycle_graph(5), nx.path_graph(2)))

    # Möbius-Kantor (16 vertices, girth 6).
    yield ("Möbius-Kantor", nx.moebius_kantor_graph())

    # Heawood graph (14 vertices, girth 6, bipartite, the (3,6)-cage).
    yield ("Heawood", nx.heawood_graph())

    # Pappus graph (18 vertices, girth 6, bipartite).
    yield ("Pappus", nx.pappus_graph())

    # Desargues graph (20 vertices, girth 6, bipartite).
    yield ("Desargues", nx.desargues_graph())

    # Tutte graph (46 vertices, cubic, 3-connected, planar, non-Hamiltonian).
    # NB: This is NOT the Tutte-Coxeter graph (the (3,8)-cage on 30
    # vertices), which networkx does not currently ship. We leave the
    # Tutte graph here as a 46-vertex data point regardless.
    yield ("Tutte (46v)", nx.tutte_graph())


# ----------------------------------------------------------------------
# Cubic check + 2^k cycle search.
# ----------------------------------------------------------------------

def is_cubic(G: nx.Graph) -> bool:
    return all(d == 3 for _, d in G.degree())


def has_cycle_of_length(G: nx.Graph, k: int) -> tuple[bool, list[int] | None]:
    """Return (True, cycle_vertices) if G has a simple cycle of length k."""
    # networkx's `simple_cycles` for undirected graphs: use
    # `cycle_basis` plus extensions, or enumerate via length-bounded DFS.
    # For small graphs, brute-force DFS is fine.
    if k < 3:
        return (False, None)
    n = G.number_of_nodes()
    nodes = list(G.nodes())

    def dfs(start, current, visited, path) -> list[int] | None:
        if len(path) == k:
            if G.has_edge(current, start):
                return path[:]
            return None
        for nbr in G.neighbors(current):
            if nbr == start and len(path) == k:
                return path[:]
            if nbr not in visited and nbr != start:
                visited.add(nbr)
                path.append(nbr)
                result = dfs(start, nbr, visited, path)
                if result is not None:
                    return result
                path.pop()
                visited.discard(nbr)
        return None

    for start in nodes:
        visited = {start}
        path = [start]
        result = dfs(start, start, visited, path)
        if result is not None:
            return (True, result)
    return (False, None)


def find_2pow_cycle(G: nx.Graph, k_max: int = 6) -> tuple[int, list[int]] | None:
    """Search for the smallest cycle of length 2^k with k >= 2 and 2^k <= n."""
    n = G.number_of_nodes()
    for k in range(2, k_max + 1):
        L = 2 ** k
        if L > n:
            break
        found, cycle = has_cycle_of_length(G, L)
        if found:
            return (k, cycle)
    return None


# ----------------------------------------------------------------------
# Main: iterate, check, report.
# ----------------------------------------------------------------------

def main() -> int:
    print(f"{'graph':<20}  {'n':>3}  {'cubic':>6}  {'min 2^k cycle':<20}")
    print("-" * 60)
    failures = []
    for name, G in named_cubic_graphs():
        n = G.number_of_nodes()
        cubic = is_cubic(G)
        if not cubic:
            print(f"{name:<20}  {n:>3}  {'NO':>6}  (not cubic, skipping)")
            continue
        cycle = find_2pow_cycle(G)
        if cycle is None:
            print(f"{name:<20}  {n:>3}  {'YES':>6}  *** NONE FOUND ***")
            failures.append(name)
        else:
            k, c = cycle
            print(f"{name:<20}  {n:>3}  {'YES':>6}  length {2**k} = 2^{k}")
    print()
    if failures:
        print(f"!!! FAILURES: {failures}")
        print("    Investigate before claiming Erdős 64 candidate counterexample.")
        return 1
    print("All named cubic graphs satisfy Erdős 64 (some 2^k cycle exists).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
