# Erdős 64 / Phase 1 — SAT cycle-encoder shipped

**Kind:** infra
**Status:** shipped (local). Phase 1 of the 4-phase plan complete.
**Date:** 2026-05-12
**Related:** 0031 (Erdős 64 target), 0039–0040 (B1.0 + B1 to n=20),
plan at `~/.claude/plans/zesty-launching-origami.md`.

## What this commit ships

`proofs/erdos64/Search/`:

- **`sat_cycle.py`** (~210 lines) — SAT-based simple-cycle detection.
  Encodes "G has `C_L`" as CNF with position-vertex Booleans
  `x[i][v]` ("vertex `v` at position `i` in the cycle"), exactly-one
  per position, at-most-one per vertex, consecutive-position
  adjacency in `G`, position-`L−1`-to-position-0 adjacency (closes
  the cycle). Solves via CaDiCaL through `pysat`.

  Two exported functions:
  - `has_cycle_of_length_sat(g6, n, L)`: anchor-iterating variant.
  - `has_cycle_of_length_sat_fast(g6, n, L)`: single SAT call (the
    one used in production).
  - `has_2pow_cycle_sat(g6, n)`: smallest `k ≥ 2` with a `C_{2^k}`.

- **`test_sat_cycle.py`** (~115 lines) — round-trips SAT against the
  DFS implementation on:
  (a) 11 named cubic graphs (K₄ through Tutte 46v),
  (b) a 100-graph random sample from `geng -cd3 -D3 14`.
  **All 11 + 100 graphs agree on every `L ∈ {3, 4, 5, 6, 7, 8, 10,
  12, 14}` between SAT and DFS.** Test run takes 5.6 s.

- **`exhaustive_cubic.py`** — modified to use SAT for
  `L ∈ {16, 32, 64, 128}` and DFS for `L ∈ {4, 8}`. Verified
  regression: `n = 18` still completes correctly (41 301 graphs, all
  pass).

## Performance notes

- DFS short-circuits cheaply for short cycles. For `L = 4` on a
  cubic graph: typically << 1 ms per graph. We keep DFS for
  `L ∈ {4, 8}`.
- SAT shines at `L = 16, 32`: a single CaDiCaL call on a
  20-vertex graph solves in single-digit ms; the per-tuple DFS
  enumeration costs `O(n^L)` worst-case. The cross-over is exactly
  where the existing pipeline started to stall (around `L = 16, n = 22`).

## Why this matters

Phase 1 of the 4-phase plan (`~/.claude/plans/zesty-launching-origami.md`)
exists to gate Phases 2 and 3. With the SAT encoder in place:

- **Phase 2** can scale exhaustive enumeration past `n = 22` (which
  killed the pure-DFS run earlier). The next memo (`0043` once n=22
  finishes) will be the first n-22 result with the SAT pipeline.
- **Phase 3** (bipartite cubic girth-6 sub-case) can now check
  large `n` quickly — the sub-class count is much smaller than the
  full cubic so we can reasonably target `n ≤ 32` exhaustively.

## Honest-language reminder

This commit ships *infrastructure*. It does not advance Erdős–Gyárfás
itself. The SAT round-trip matches DFS on every checked input —
that's correctness validation, not new mathematics.

## Validation output (the headline)

```
=== Part 1: 11-graph named-cubic corpus ===
  K_4                  n=  4   OK   (0.00s)
  K_{3,3}              n=  6   OK   (0.00s)
  3-prism              n=  6   OK   (0.00s)
  Q_3 (3-cube)         n=  8   OK   (0.01s)
  Petersen             n= 10   OK   (0.03s)
  5-prism              n= 10   OK   (0.01s)
  Möbius-Kantor        n= 16   OK   (0.08s)
  Heawood              n= 14   OK   (0.05s)
  Pappus               n= 18   OK   (0.08s)
  Desargues            n= 20   OK   (0.11s)
  Tutte (46v)          n= 46   OK   (0.49s)

=== Part 2: 100-graph random sample from geng -cd3 -D3 14 ===
  Sample done in 5.24s.

ALL TESTS PASS. SAT ↔ DFS agree on every checked (graph, L) pair.
```

## Next (Phase 2 immediate)

- `n = 22` with SAT-enabled pipeline (in flight).
- Memo `0043` once it completes; cumulative empirical record memo
  to follow once we reach the Markstrom frontier at `n = 30`.

Phase 3A (bipartite cubic girth-6 search) is unblocked and can run
in parallel.
