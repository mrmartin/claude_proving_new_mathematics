# Erdős 64 — session checkpoint, 2026-05-11

**Kind:** infra / checkpoint
**Status:** in-progress overall plan; this session's milestones done.
**Date:** 2026-05-11
**Related:** 0031 (target), 0032–0040 (this session's commits),
plan at `~/.claude/plans/zesty-launching-origami.md`.

## What this session shipped

Across 10 commits (`145d897` → `e037469`), 10 memos (0031–0040),
~1500 lines of Lean across `proofs/erdos64/`, plus a working
computational pipeline:

### Lean side (`proofs/erdos64/`)

| Module                    | Lines | Status                       |
|---------------------------|------:|------------------------------|
| `Erdos64/Basic.lean`      |   95  | `Has2PowCycle`, `IsCounterexample64`, three reductions through `C₄`/`C₈`. Axiom-clean. |
| `Erdos64/WarmUp.lean`     |  140  | K₄, K₃,₃, 3-prism each have a 4-cycle. Axiom-clean. |
| `Erdos64/Bipartite.lean`  |   90  | Bipartite ⇒ every cycle is even (mathlib `Bipartite.lean:63` TODO). Axiom-clean. |
| `Erdos64/BipartiteCubic.lean` |  110 | Bipartite girth ∈ {4, 8} ⇒ `Has2PowCycle`. Girth-6 sub-case deferred. Axiom-clean. |
| `Erdos64/DiamTwo.lean`    |   65  | Carr 2026 *statement* + `exists_two_other_neighbours` setup helper. Body `sorry`. |
| `Erdos64/Markstrom.lean`  |  165  | Petersen (10v) + Möbius–Kantor (16v) each have an 8-cycle. Axiom-clean. |

### Computational side (`proofs/erdos64/Search/`)

| Tool                  | What                                               |
|-----------------------|----------------------------------------------------|
| `check_cubic.py`      | Named-graph spot check (K₄ … Tutte). 11 named cubic graphs verified. |
| `exhaustive_cubic.py` | `geng -cd3 -D3 n` + per-graph DFS check. Verified `n ∈ {10, 12, 14, 16, 18, 20}` exhaustively (556 463 graphs). |
| `README.md`           | Pipeline architecture + future-work pointers (SAT, parallelism, larger `n`). |

`nauty` 2.8.8 installed locally at `~/.local/bin/geng`. python-sat
1.9 installed (cadical / kissat bindings ready).

## What this session did *not* claim

- No claim of any progress on the *general* Erdős 64 problem (the
  conjecture remains open).
- No new sub-case proof of Erdős 64 (the bipartite/diameter-2/
  Markstrom-class results we shipped are *partial* in their own
  framing: bipartite girth-6 is open; Carr 2026 is `sorry`).
- The `n ≤ 20` empirical verification stays well within Markstrom
  2004's published bound (`n ≤ 29`); we re-derive a sub-range.

## What's queued (per plan)

- **A2 girth-6 sub-case**: bipartite cubic + girth = 6 ⇒ `C₈`?
  Not proved here, may not even be true in general. Sharp Track B
  target: search bipartite cubic girth-6 graphs on `n ≤ 30`.
- **A3 body**: Carr 2026 Cases 1, 2A, 2B, 2C. ~650 lines of vertex
  chasing. Deferred. Memo 0037 has the per-claim breakdown.
- **A4 extension**: Heawood graph (14v) verified empirically but
  not yet in Lean. Encoding by Fano-plane incidence is the natural
  route; ~80 lines.
- **B1 push to `n ≥ 22`**: per-graph DFS becomes too slow.
  Pipeline needs (a) streaming `geng | exhaustive_cubic.py`,
  (b) parallelism, (c) a SAT-encoded cycle search for `n ≥ 30`.
  python-sat is installed; the encoder is the next ~200-line
  Python addition.
- **B2 / B3**: research-stretch targets, not started.
- **C1 (`girth ≤ 2·diam+1`)**: deferred per memo 0035.
- **C3 (`Decidable (∃ c, c.IsCycle ∧ c.length = k)`)**: useful
  helper for A4 scaling. ~250 lines.

## Honest framing

This is **infrastructure + warm-up + computational validation** for
a long-term attack on Erdős–Gyárfás. The Lean side has a clean
scaffolding for any future sub-case proof to slot into. The
computational side has a working pipeline that scales to `n = 20`
in wall-time minutes; pushing to `n = 30` needs SAT + parallelism.

## Honest non-goals (CLAUDE.md HARD GATING RULE)

No commit, no memo, no PR in this session uses the phrase "solved
Erdős 64". The closest we come is the empirical record (no
counterexample on `n ≤ 20`), which is explicitly weaker than
Markstrom's already-published `n ≤ 29`. Permitted phrasing used
throughout: "Lean-verified partial result", "extension of the
empirical record", "infrastructure for B1".

## What a *next session* should do

Best return-per-hour:

1. Build the SAT cycle-search encoder (Python, ~200 lines). Push
   B1 to `n ≥ 24`. This is "real" empirical territory (`n ≥ 30`
   would be net-new beyond Markstrom).
2. Add Heawood graph to `Markstrom.lean` (~80 lines).
3. *Either* start Carr 2026 Case 2C (the cleanest 8-cycle
   construction, ~100 Lean lines), *or* pivot to Track B2 (the
   bipartite Moore-bound argument, research stretch).

We are **not** ready for B3 (girth-pigeonhole spike) yet — Tracks
A and C should ship more first to ground the spike.
