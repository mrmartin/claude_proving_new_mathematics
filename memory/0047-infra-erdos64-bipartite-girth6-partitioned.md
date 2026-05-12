# Erdős 64 Phase 3A — partitioned bipartite-girth-6 search

**Kind:** infra
**Status:** shipped
**Date:** 2026-05-12
**Related:** 0043 (n ≤ 22 results), 0046 (last checkpoint), Phase 3A of
plan `~/.claude/plans/zesty-launching-origami.md`.

## Goal

Make `bipartite_girth6.py` fast enough to reach `n ≥ 26` in the
Phase 3A empirical campaign. The buffered variant at `n = 24` took
342 s wall-time; the streaming variant was ~28× slower; the
multiprocessing-pool variant (`bipartite_girth6_mp.py`) only got
325 s. None could push past `n = 24`.

## Diagnosis — geng is the bottleneck

Standalone measurement at `n = 24`:

    time ~/.local/bin/geng -bcd3 -D3 24 -q | wc -l
    29579
    real    5m28s

geng itself is single-threaded and outputs 29579 graphs in 328 s —
~90 graphs/s. The worker-pool variants saturated geng's pipe and
gave at most a 1.05× speedup. **No amount of worker-pool
parallelism can help; we have to parallelise geng itself.**

## Fix — `geng res/mod` partitioning

`geng` supports a "subset enumeration" syntax: `geng [opts] n
R/M` outputs only the R-th of M disjoint slices of the canonical
enumeration. Slices are mutually exclusive and together exhaustive.
Spot-check at `n = 14`:

    geng -bcd3 -D3 14 0/2 -q | wc -l   # → 1
    geng -bcd3 -D3 14 1/2 -q | wc -l   # → 12
    geng -bcd3 -D3 14   -q | wc -l     # → 13

So spawning M parallel `geng res/mod` processes (each in its own
Python child, no shared state, no pipe contention) gives nearly
ideal parallelism.

## Implementation — `bipartite_girth6_partitioned.py`

`proofs/erdos64/Search/bipartite_girth6_partitioned.py` (~150 lines).

- `mp.Pool(slices)` spawns M child processes.
- Each child runs `run_slice(n, res, mod)`, which:
  1. Opens its own `geng -bcd3 -D3 n R/M -q` pipe.
  2. For each graph6 line: parse to adjacency list, compute girth
     via pure-Python BFS (`_fast_girth_adj`), and if girth == 6,
     run `has_cycle_of_length_sat_fast` for `L ∈ {4, 8, 16, ...}`.
  3. Returns a summary dict (only girth-6 graphs are reported).
- Main process merges the M summaries.

## Measured speedups

| n  | buffered (1 process) | partitioned (48 slices) | speedup |
|---:|---:|---:|---:|
| 24 | 342 s | 23 s | **14.9×** |
| 26 | — (untenable single-thread) | 215 s | — |

At `n = 24` the partitioned variant found the *same* 162 girth-6
graphs (vs the buffered baseline) — correctness sanity-check ✓.

## Results so far

`proofs/erdos64/Search/results/bipartite_g6/`:

| n  | total bipartite cubic | of those, girth = 6 | all have C_8? | elapsed |
|---:|---:|---:|---|---:|
| 14 | 7 | 1 | ✓ | < 1 s |
| 16 | 10 | 1 | ✓ | < 1 s |
| 18 | 36 | 3 | ✓ | < 1 s |
| 20 | 138 | 10 | ✓ | ~1 s |
| 22 | 668 | 28 | ✓ | 28 s |
| 24 | 29 579 | 162 | ✓ | 23 s |
| 26 | 245 627 | 1 201 | ✓ | 215 s |
| 28 | 2 291 589 | 11 415 | ✓ | 2 204 s (36.7 min) |
| **Total** | **2 567 654** | **12 821** | **all** | |

(The `total_bipartite_cubic` field is exact for `n ≥ 22`; the n=14
through n=20 row entries come from the original buffered runs and
report only the girth-6 subset.)

The `n = 26 → n = 28` growth was 215 s → 2204 s = **10.25×**, very
close to the `n = 24 → n = 26` ratio of 9.3×. Projecting:

- `n = 30` estimate: ~10.25 × 2 204 s ≈ 22 600 s = **6.3 hours**.
- `n = 32` estimate: ~10× 22 600 s ≈ **2.6 days**.

## Why this matters

Phase 3A's whole point: if no bipartite cubic girth-6 graph on
`n ≤ 32` lacks a `C_8`, the `h_girth_6_case` premise in our shipped
`Erdos64.has_2pow_cycle_of_isBipartite_girth_le_eight`
becomes empirically discharged on `n ≤ 32`. Nowbandegani–Esfandiari
2011's bipartite-counterexample bound is exactly `n ≥ 32`, so
`n = 32` is the cliff. 1406 graphs verified, 0 candidate
counterexamples.

Next: `n = 30` (~6 hr) and `n = 32` (~2.6 days).

## Lessons

- **Benchmark the dependencies, not just your Python.** I burned
  two iterations on Python-side parallelism before measuring geng
  itself. The 5 m 28 s wall-time of standalone geng -bcd3 -D3 24
  was the ceiling all along.
- `geng res/mod` partitioning is the right primitive for any
  nauty-driven exhaustive search at scale.
- `subprocess.Popen` + reading bytes mode is the right way to
  stream geng output (the buffered `subprocess.run` causes OOM at
  `n ≥ 28`; the streaming `bipartite_girth6_stream.py` variant has
  per-graph Python overhead but was the wrong fix).
- Per-process geng pipes don't compete on a 48-core box; `nproc =
  48` is the natural slice count.

## Next

- Wait for `n = 28` to finish (background process).
- Launch `n = 30`, `n = 32` sequentially after.
- If all clean through `n = 32`: write `0049-result-...-n32.md`
  closing the empirical sub-case. The `BipartiteCubic.lean`
  open hypothesis becomes unconditional on `n ≤ 32`.

## Honest framing

Even completing `n = 32` does **not** solve Erdős 64. It only
falsifies the existence of a small bipartite cubic
counterexample with girth 6 and no 8-cycle. The Phase 3B
structural attempt (memo 0044) remains the only path to
unconditional Lean discharge.
