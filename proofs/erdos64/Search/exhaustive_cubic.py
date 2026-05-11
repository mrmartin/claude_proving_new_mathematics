#!/usr/bin/env python3
"""
Exhaustive search: every connected cubic graph on n vertices has a 2^k cycle.

This is the **full** Track B1 pipeline (per memo 0039), running on
modest n. Uses `geng -cd3 -D3 n` (nauty) to enumerate connected
cubic graphs on n vertices, one canonical representative per
isomorphism class. For each graph, we run a depth-bounded DFS to
find a cycle of length 4, 8, 16, …, up to n. If none is found, the
graph is a candidate counterexample to Erdős 64.

Run:

    python3 exhaustive_cubic.py 10      # all 19 connected cubic on 10v
    python3 exhaustive_cubic.py 12      # all 85 on 12v
    python3 exhaustive_cubic.py 14      # all 509 on 14v
    python3 exhaustive_cubic.py 16      # all 4060 on 16v
    python3 exhaustive_cubic.py 18      # all 41301 on 18v

Counterexample candidates (graphs that fail the check) are printed
in graph6 format. As of 2026-05-11 with this script's first run, we
expect zero candidates up to at least n = 14 (well within Markstrom
2004's bound).

Beyond n ≈ 20, this script is too slow (millions of graphs). Use
the SAT-based search in `sat_search.py` (TODO) for larger n.

Dependencies:
    - networkx
    - geng (installed at /tmp/nauty2_8_8/geng or in PATH)
"""

from __future__ import annotations
import subprocess
import sys
from pathlib import Path
import networkx as nx


GENG_PATHS = [
    "geng",
    str(Path.home() / ".local" / "bin" / "geng"),
    "/tmp/nauty2_8_8/geng",
]


def find_geng() -> str:
    for path in GENG_PATHS:
        try:
            subprocess.check_output([path, "-q", "--help"], stderr=subprocess.STDOUT)
            return path
        except (FileNotFoundError, subprocess.CalledProcessError):
            # geng's --help may not work; try a sanity check.
            try:
                r = subprocess.run([path, "-q", "4"], capture_output=True, timeout=5)
                if r.returncode == 0:
                    return path
            except Exception:
                continue
    raise RuntimeError(
        f"geng not found in any of: {GENG_PATHS}. Install nauty."
    )


def parse_graph6(g6: str, n: int) -> nx.Graph:
    """Parse a graph6 string into a networkx graph."""
    return nx.from_graph6_bytes(g6.encode())


def has_cycle_of_length(G: nx.Graph, k: int) -> bool:
    """Return True if G has a simple cycle of length exactly k."""
    if k < 3 or k > G.number_of_nodes():
        return False
    nodes = list(G.nodes())

    def dfs(start, current, depth, visited) -> bool:
        if depth == k - 1:
            return G.has_edge(current, start)
        for nbr in G.neighbors(current):
            if nbr == start:
                continue
            if nbr in visited:
                continue
            visited.add(nbr)
            if dfs(start, nbr, depth + 1, visited):
                return True
            visited.discard(nbr)
        return False

    for start in nodes:
        if dfs(start, start, 0, {start}):
            return True
    return False


def has_2pow_cycle(G: nx.Graph) -> int | None:
    """Return the smallest k ≥ 2 such that G has a 2^k cycle, else None."""
    n = G.number_of_nodes()
    for k in range(2, 8):  # 2^k up to 128
        L = 2 ** k
        if L > n:
            return None
        if has_cycle_of_length(G, L):
            return k
    return None


def enumerate_cubic_and_check(n: int, verbose: bool = False) -> list[str]:
    """For n in {4, 6, 8, ...}, enumerate connected cubic graphs and check
    each. Return graph6 strings of any failing candidates."""
    geng = find_geng()
    cmd = [geng, "-cd3", "-D3", str(n), "-q"]
    if verbose:
        print(f"Running: {' '.join(cmd)}", file=sys.stderr)
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    if proc.returncode != 0:
        raise RuntimeError(f"geng failed: {proc.stderr}")
    lines = proc.stdout.strip().split("\n")
    total = len(lines)
    print(f"Checking {total} connected cubic graphs on {n} vertices...")
    failures = []
    for i, g6 in enumerate(lines):
        if not g6.strip():
            continue
        G = parse_graph6(g6, n)
        result = has_2pow_cycle(G)
        if result is None:
            print(f"  !!! CANDIDATE COUNTEREXAMPLE !!! [{i}] graph6: {g6}")
            failures.append(g6)
        elif verbose and i % max(1, total // 20) == 0:
            print(f"  [{i:>5}/{total}] 2^{result} cycle found")
    return failures


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("Usage: python3 exhaustive_cubic.py <n>")
        return 2
    n = int(argv[1])
    failures = enumerate_cubic_and_check(n, verbose=True)
    print()
    if failures:
        print(f"!!! {len(failures)} candidate counterexamples found on n={n}.")
        for g6 in failures:
            print(f"  graph6: {g6}")
        return 1
    print(f"OK. All connected cubic graphs on {n} vertices satisfy Erdős 64.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
