# Erdős 64 / Track B1 — verified empirically for `n ≤ 18`

**Kind:** result (computational)
**Status:** shipped (local). Null result; no candidate counterexample.
**Date:** 2026-05-11
**Related:** 0031 (Erdős 64 target), 0039 (B1.0 infrastructure),
plan at `~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-3-adjacent partial result: a Markstrom-style empirical
verification at small `n`. This **extends our local empirical
record but does not extend Markstrom 2004's bound** (Markstrom
already verified up to `n = 29`); we re-derive a sub-range of his
result in our own pipeline, as the necessary calibration before
pushing to `n ≥ 30`.

## What was computed

Installed nauty 2.8.8 locally at `~/.local/bin/geng` (no root
needed; built from source at `/tmp/nauty2_8_8`).
`proofs/erdos64/Search/exhaustive_cubic.py` enumerates connected
cubic graphs via `geng -cd3 -D3 n` and per-graph DFS-checks for the
smallest `2^k` cycle.

Results:

| `n`  | # connected cubic | failures | wall-time |
|------|-------------------:|---------:|----------:|
| 10   |                 19 |        0 |    < 0.1s |
| 12   |                 85 |        0 |     0.2s  |
| 14   |                509 |        0 |     0.3s  |
| 16   |              4 060 |        0 |     1.9s  |
| 18   |             41 301 |        0 |    20.2s  |
| 20   |        (in flight) |    (TBD) |     (TBD) |

Every graph checked has at least one `2^k` cycle. So Erdős 64 holds
empirically on all connected cubic graphs of `n ≤ 18`. (Markstrom
2004's published bound: `n ≤ 29`. We are well below that, but the
pipeline is now wired, so larger `n` is just a matter of compute.)

## Pipeline architecture (now active)

```
geng -cd3 -D3 n     # nauty: enumerate cubic graphs, one per iso class
       │
       ▼
exhaustive_cubic.py # per-graph DFS for C_{2^k}, k=2,3,...
       │
       ▼
report failures     # any graph with NO 2^k cycle is a candidate CE
```

For larger `n` (≥ 22 the geng output becomes ~50 GB and the per-graph
check becomes the bottleneck), this needs:
- Streaming `geng | exhaustive_cubic.py` to avoid materialising
  the whole list. (Currently we read all of `geng`'s stdout into
  memory.)
- Parallelisation across cores (each graph is independent).
- SAT encoding of cubic-graph + no-2^k-cycle for `n ≥ 30` (where
  the count is ~30M+ and exhaustive DFS becomes infeasible).

## Honest framing

This is **infrastructure validation**, not new mathematics. The
result for `n ≤ 18` is implied by Markstrom 2004; what's new is
that we now have a Lean-adjacent pipeline that can scale.

If the in-flight `n = 20` run (and subsequent `n = 22, 24, …`) all
return no failures, we are still within Markstrom's bound. The
*genuinely informative* runs start at `n = 30` and beyond.

## Next

- Wait for `n = 20` to complete.
- Push to `n = 22` (the bottleneck is ~10 minutes of DFS on
  ~510 000 graphs).
- Eventually port to a SAT-encoded search for `n ≥ 30` so the
  per-graph cost stays sub-second.
- For any candidate counterexample (none expected within Markstrom's
  bound): encode in Lean via `inductive V`, verify with `decide
  +native`, then memo with quadruple-checking discipline before any
  "counterexample" language.
