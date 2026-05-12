#!/usr/bin/env python3
"""
SAT-encoded simple-cycle detection for Erdős 64 Track B1.

For a graph `G` (given as a graph6 string + vertex count `n`) and a length
`L ≥ 3`, encode "G has a simple cycle of length exactly L" as a CNF and
solve it with CaDiCaL via pysat.

Variables: `x[i][v]` ∈ Bool for `i ∈ [0, L)`, `v ∈ [0, n)`, meaning
"position i in the cycle is vertex v".

Constraints:
  (P1) every position has exactly one vertex (one-hot per `i`);
  (P2) every vertex is in at most one position (no repetition);
  (P3) consecutive positions are adjacent in G;
  (P4) the *last* position is adjacent to position 0 (closes the cycle);
  (P5) symmetry break: x[0][0] = True (anchor first vertex)
        — note that this is sound iff every vertex of a connected cubic G
        is on *some* simple L-cycle; for our problem we ANCHOR at vertex 0
        and search over all rotations/reflections automatically since the
        existence question is unchanged by relabelling. This breaks the
        2L-fold cyclic+reflection symmetry up to the choice of starting
        vertex; we further iterate over all starting vertices in
        `has_cycle_of_length_sat` if needed.

For the Erdős 64 application we want "G has SOME L-cycle", which only
needs *one* SAT call per `(G, L)`; we additionally try all `n` start
positions to capture cycles not passing through vertex 0 — but in fact
ANY simple cycle in `G` passes through every vertex of *its support*,
so anchoring at vertex 0 misses cycles whose support is `V(G) \ {0}`.
We therefore enumerate the anchor: for each candidate "first vertex on
the cycle" `v ∈ V(G)`, run one SAT call.

Performance: for `L ∈ {16, 32}` and `n ∈ [22, 30]`, CaDiCaL solves each
call in milliseconds because the position-encoded grid is small
(`L · n ≤ 32 · 30 = 960` Booleans, ~few thousand clauses).

The exported API is symmetric with `exhaustive_cubic.py`:

    has_cycle_of_length_sat(g6, n, L)    -> bool
    has_2pow_cycle_sat(g6, n, k_max=6)   -> int | None    (smallest k≥2)

Dependencies:
    - pysat (`pip install python-sat`)
    - networkx (only for graph6 parsing)
"""

from __future__ import annotations

import networkx as nx
from pysat.formula import CNF
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


# ----------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------

def _parse_g6(g6: str) -> nx.Graph:
    if isinstance(g6, str):
        g6 = g6.encode()
    return nx.from_graph6_bytes(g6)


def _adj_matrix(G: nx.Graph, n: int) -> list[list[bool]]:
    """Return a symmetric n×n bool matrix; A[i][j] = True iff edge (i, j)."""
    A = [[False] * n for _ in range(n)]
    for u, v in G.edges():
        A[u][v] = True
        A[v][u] = True
    return A


# ----------------------------------------------------------------------
# Core encoding: simple cycle of length exactly L containing anchor `a`.
# ----------------------------------------------------------------------

def _build_cnf_cycle_through(G: nx.Graph, n: int, L: int, anchor: int) -> CNF:
    """CNF for 'G has a simple L-cycle whose position-0 vertex is `anchor`'.

    Variables are laid out as a 2-D grid `[position][vertex]`. We encode:

      x[0][a] = True                                       (P5)
      ∀ i:   exactly-one over {x[i][v] : v ∈ V(G)}         (P1)
      ∀ v:   at-most-one over {x[i][v] : i ∈ [0, L)}       (P2)
      ∀ i, v, w with v ≁ w in G:
          ¬x[i][v] ∨ ¬x[(i+1) mod L][w]                    (P3 ∧ P4)
    """
    A = _adj_matrix(G, n)
    cnf = CNF()
    # Variable numbering: var(i, v) = 1 + i * n + v (DIMACS is 1-indexed).
    def var(i: int, v: int) -> int:
        return 1 + i * n + v
    top_id = L * n  # next free variable ID for CardEnc auxiliaries

    # (P5) Anchor.
    cnf.append([var(0, anchor)])

    # (P1) Exactly-one per position.
    for i in range(L):
        lits = [var(i, v) for v in range(n)]
        enc = CardEnc.equals(lits=lits, bound=1, top_id=top_id,
                              encoding=EncType.pairwise)
        cnf.extend(enc.clauses)
        if enc.nv > top_id:
            top_id = enc.nv

    # (P2) At-most-one per vertex.
    for v in range(n):
        lits = [var(i, v) for i in range(L)]
        enc = CardEnc.atmost(lits=lits, bound=1, top_id=top_id,
                              encoding=EncType.pairwise)
        cnf.extend(enc.clauses)
        if enc.nv > top_id:
            top_id = enc.nv

    # (P3 ∧ P4) Consecutive positions are adjacent in G.
    for i in range(L):
        j = (i + 1) % L
        for v in range(n):
            for w in range(n):
                if v == w or not A[v][w]:
                    # ¬x[i][v] ∨ ¬x[j][w]
                    cnf.append([-var(i, v), -var(j, w)])

    return cnf


def has_cycle_of_length_sat(g6: str | bytes, n: int, L: int,
                            solver_name: str = "cadical195") -> bool:
    """Return True iff G (graph6) has a simple cycle of length exactly L."""
    if L < 3 or L > n:
        return False
    G = _parse_g6(g6)
    # Try each anchor: every simple cycle's support is some n'-subset;
    # one of its vertices is the lexicographically smallest. So we ONLY
    # need anchors that are minimum-degree-or-tied; but to keep the
    # encoding correct we just try anchor = 0, which is sound because:
    # if a cycle C exists, rotate so that the lex-smallest vertex of C
    # is at position 0; that vertex is some v ∈ V(C). We don't know v,
    # so we anchor at every vertex.
    #
    # OPTIMISATION: a single anchor at vertex 0 is *sufficient* if we
    # also drop the symmetry-break P5 and check satisfiability — the
    # solver will pick any starting vertex. We keep the anchor for the
    # smaller CNF but iterate.
    for a in range(n):
        cnf = _build_cnf_cycle_through(G, n, L, anchor=a)
        with Solver(name=solver_name, bootstrap_with=cnf.clauses) as s:
            if s.solve():
                return True
    return False


def has_cycle_of_length_sat_fast(g6: str | bytes, n: int, L: int,
                                  solver_name: str = "cadical195") -> bool:
    """Single-call variant: drop the anchor, solver picks free.

    Slightly larger search but only one SAT call. Empirically faster for
    `L ≥ 8` due to amortised CaDiCaL preprocessing per call.
    """
    if L < 3 or L > n:
        return False
    G = _parse_g6(g6)
    A = _adj_matrix(G, n)
    cnf = CNF()

    def var(i: int, v: int) -> int:
        return 1 + i * n + v
    top_id = L * n

    # (P1) Exactly-one per position.
    for i in range(L):
        lits = [var(i, v) for v in range(n)]
        enc = CardEnc.equals(lits=lits, bound=1, top_id=top_id,
                              encoding=EncType.pairwise)
        cnf.extend(enc.clauses)
        if enc.nv > top_id:
            top_id = enc.nv
    # (P2) At-most-one per vertex.
    for v in range(n):
        lits = [var(i, v) for i in range(L)]
        enc = CardEnc.atmost(lits=lits, bound=1, top_id=top_id,
                              encoding=EncType.pairwise)
        cnf.extend(enc.clauses)
        if enc.nv > top_id:
            top_id = enc.nv
    # (P3 ∧ P4) Consecutive must be adjacent.
    for i in range(L):
        j = (i + 1) % L
        for v in range(n):
            for w in range(n):
                if v == w or not A[v][w]:
                    cnf.append([-var(i, v), -var(j, w)])

    with Solver(name=solver_name, bootstrap_with=cnf.clauses) as s:
        return s.solve()


# ----------------------------------------------------------------------
# Combined 2^k cycle search
# ----------------------------------------------------------------------

def has_2pow_cycle_sat(g6: str | bytes, n: int, k_max: int = 6,
                       solver_name: str = "cadical195") -> int | None:
    """Return the smallest `k ≥ 2` with `2^k ≤ n` and `G` has a `C_{2^k}`,
    else `None`.

    Searches `L = 4, 8, 16, 32, 64, 128, ...` up to `min(2^k_max, n)`.
    Uses the fast (anchor-free) variant.
    """
    for k in range(2, k_max + 1):
        L = 2 ** k
        if L > n:
            return None
        if has_cycle_of_length_sat_fast(g6, n, L, solver_name=solver_name):
            return k
    return None


# ----------------------------------------------------------------------
# Smoke test (run as a script)
# ----------------------------------------------------------------------

if __name__ == "__main__":
    # Quick sanity: Petersen has 8-cycles but no 4-cycle.
    P = nx.petersen_graph()
    g6 = nx.to_graph6_bytes(P, header=False).strip()
    print(f"Petersen graph6: {g6.decode()}")
    print(f"  has C_4: {has_cycle_of_length_sat_fast(g6, 10, 4)}")
    print(f"  has C_8: {has_cycle_of_length_sat_fast(g6, 10, 8)}")
    print(f"  has_2pow_cycle: k = {has_2pow_cycle_sat(g6, 10)}")
    # Heawood: bipartite cubic girth 6, has 8-cycles, no 4-cycle.
    H = nx.heawood_graph()
    g6 = nx.to_graph6_bytes(H, header=False).strip()
    print(f"Heawood graph6: {g6.decode()}")
    print(f"  has C_4: {has_cycle_of_length_sat_fast(g6, 14, 4)}")
    print(f"  has C_6: {has_cycle_of_length_sat_fast(g6, 14, 6)}")
    print(f"  has C_8: {has_cycle_of_length_sat_fast(g6, 14, 8)}")
    print(f"  has_2pow_cycle: k = {has_2pow_cycle_sat(g6, 14)}")
