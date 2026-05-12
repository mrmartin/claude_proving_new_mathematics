# Erdős 64 / Phase 3A — bipartite cubic girth-6 search, `n ∈ {14, …, 22}`

**Kind:** result (computational)
**Status:** shipped (local). All small `n` pass; pushing to `n ≥ 24`.
**Date:** 2026-05-12
**Related:** 0031 (Erdős 64), 0036 (girth-6 open sub-case), 0042
(SAT cycle-encoder), plan at `~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-3-adjacent partial result on the open conjecture. **This is
the highest-EV phase** per the 4-phase plan: closing the
bipartite-cubic-girth-6 sub-case discharges the `h_girth_6_case`
hypothesis in our shipped `has_2pow_cycle_of_isBipartite_girth_le_eight`
theorem.

## What's been computed

`proofs/erdos64/Search/bipartite_girth6.py` enumerates connected
bipartite cubic graphs (`geng -bcd3 -D3 n`), filters girth = 6 via
`networkx.girth`, then SAT-checks each for a `C_8`.

| `n`  | # bipartite cubic | # girth = 6 | # passing (have `C_8`) | wall-time |
|-----:|------------------:|------------:|------------------------:|---------:|
| 14   |                13 |           1 |                       1 |   < 0.1s |
| 16   |                  |           1 |                       1 |   < 0.1s |
| 18   |               149 |           3 |                       3 |    0.2s  |
| 20   |                   |          10 |                      10 |    0.4s  |
| 22   |              4132 |          28 |                      28 |    1.0s  |

**Every bipartite cubic girth-6 graph on `n ≤ 22` has a `C_8`.**
43 graphs total at small `n`. No candidate counterexample.

## Significance

This is the first computational evidence for the conjectured-true
sub-case **"bipartite cubic + girth = 6 ⇒ has `C_8`"** at the sizes
where `BipartiteCubic.has_2pow_cycle_of_isBipartite_girth_le_eight`
holds *unconditionally* once we discharge its `h_girth_6_case`
hypothesis. If we extend this empirically to `n ≤ 32`, then for
those `n` the conditional theorem becomes **unconditional**.

Nowbandegani–Esfandiari 2011 [NoEs11] proves any bipartite
counterexample to Erdős 64 has `n ≥ 32`, so `n = 32` is *exactly*
the door. Pushing the empirical check to `n = 32` covers the
sharpest test the literature gives.

## What's still running

- `n = 24, 26, 28`: in flight on the SAT pipeline (estimated < 10 min
  combined).
- `n = 30, 32`: queued.

## Honest framing

This does **not** advance Erdős 64. It supplies *evidence* for a
named sub-case that — if it holds universally — discharges an open
hypothesis in our shipped Lean theorem. A structural proof of the
sub-case (Phase 3B) would be the substantive step. Empirical
closure on `n ≤ 32` is a milestone, not a proof.

If at any `n ≤ 32` we find a graph without a `C_{2^k}` for `k ≥ 2`,
that is a **candidate counterexample to Erdős 64 itself** — must
quadruple-check before any "counterexample" language.

## Next

- Finish `n ∈ {24, 26, 28, 30, 32}` empirically.
- Update this memo (or successor 0044) with the cumulative table.
- Once `n = 32` lands clean, begin Phase 3B structural attack in
  `proofs/erdos64/Erdos64/BipartiteCubicGirth6.lean`.

## Header for the JSON results

Per-`n` results land in
`proofs/erdos64/Search/results/bipartite_g6/n{N:02d}.json`:

```json
{
  "n": <int>,
  "geng_command": "geng -bcd3 -D3 <N>",
  "total_bipartite_cubic_girth6": <int>,
  "elapsed_enumerate_seconds": <float>,
  "elapsed_check_seconds": <float>,
  "no_C8_but_has_other_2pow": [],
  "candidate_counterexamples_to_erdos_64": []
}
```
