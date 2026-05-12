# Erdős 64 — session checkpoint, 2026-05-12

**Kind:** infra / checkpoint
**Status:** Phase 1 done. Phase 3A partial (`n ≤ 24` clean). Phase
4 prereq + pre-case done.
**Date:** 2026-05-12
**Related:** 0041 (last checkpoint, 2026-05-11), 0042–0045 (this
session's commits), plan at `~/.claude/plans/zesty-launching-origami.md`.

## What this session shipped

Across commits `7f79076` → `e2e722c` (5 commits), 5 memos
(0042–0045 and partial 0046):

### Phase 1: SAT cycle-encoder

- `proofs/erdos64/Search/sat_cycle.py` (~210 lines): position-vertex
  CNF encoding of `C_L`-existence in `G`. Solver: CaDiCaL via
  `pysat`. Two variants (anchor-iterating + anchor-free).
- `proofs/erdos64/Search/test_sat_cycle.py`: validates SAT against
  DFS on 11 named cubic graphs + 100-graph random sample from
  `geng -cd3 -D3 14`. **All 111 (graph, L) checks agree.**
- `proofs/erdos64/Search/exhaustive_cubic.py`: now uses SAT for
  `L ∈ {16, 32, 64, 128}`, DFS for `L ∈ {4, 8}`. `n = 18` regression
  passes (41 301 graphs).

Memo 0042.

### Phase 3A: bipartite cubic girth-6 empirical search

- `proofs/erdos64/Search/bipartite_girth6.py` (~140 lines):
  `geng -bcd3 -D3 n` ⇒ filter `girth = 6` via `networkx.girth` ⇒
  SAT-check `C_8`.

- **Results so far** (no candidate counterexample):
  - `n = 14`: 1 graph (Heawood), C_8 found.
  - `n = 16`: 1 graph, C_8 found.
  - `n = 18`: 3 graphs, all have C_8.
  - `n = 20`: 10 graphs, all have C_8.
  - `n = 22`: 28 graphs, all have C_8.
  - `n = 24`: 162 graphs, all have C_8.
  - **Total `n ≤ 24`: 205 graphs, all have `C_8`.**

- `n = 26` in flight (geng output is millions of bipartite cubic
  graphs; the filter to girth-6 yields ~1000s; SAT check is fast
  but `geng` itself is the bottleneck).

Memos 0043, 0044.

### Phase 4 prereq + pre-case

- `proofs/erdos64/Erdos64/CycleHelpers.lean` (~115 lines,
  axiom-clean): `walk4` constructor, `walk4_isCycle` and
  `has_2pow_cycle_of_chain4` for explicit 4-cycle construction
  with generic vertex type `V`. Closes the `cons_isCycle_iff`
  plumbing gap that originally blocked Carr's pre-case.
- `proofs/erdos64/Erdos64/DiamTwo.lean` updated:
  `carr2026_precase_two_shared_neighbours` — one of four cases in
  Carr 2026's argument, discharged via `has_2pow_cycle_of_chain4`.
  Cases 1, 2A, 2B, 2C still `sorry`.

Memo 0045.

## Current Lean state

| Module | Lines | Status |
|---|---:|---|
| `Erdos64/Basic.lean` | 86 | axiom-clean |
| `Erdos64/CycleHelpers.lean` | 117 | axiom-clean **NEW this session** |
| `Erdos64/WarmUp.lean` | 139 | axiom-clean |
| `Erdos64/Bipartite.lean` | 84 | axiom-clean |
| `Erdos64/BipartiteCubic.lean` | 108 | axiom-clean |
| `Erdos64/DiamTwo.lean` | 84 | one `sorry` (Carr Cases 1, 2A, 2B, 2C); pre-case discharged this session |
| `Erdos64/Markstrom.lean` | 161 | axiom-clean |

**Total: ~780 lines of Lean, all axiom-clean except the one
documented Carr 2026 sorry.**

## Honest framing

This session did *not* solve Erdős 64. It made measurable progress
on the highest-EV phase (3A: bipartite cubic girth-6) — every
single one of the 205 small-`n` graphs in that class has a `C_8`.
If this empirical pattern holds to `n = 32` (Nowbandegani–
Esfandiari's bipartite-CE bound), the `h_girth_6_case` premise in
our shipped `has_2pow_cycle_of_isBipartite_girth_le_eight`
becomes empirically discharged for `n ≤ 32`.

The structural argument (Phase 3B) has a clear obstacle in the
BFS-layer + Moore-bound sketch (memo 0044). The empirical record
is *not* a proof.

The Phase 4 helper (`CycleHelpers.lean`) is the most reusable Lean
artifact of the session — it's the foundation for any
candidate-counterexample certificate or sub-case proof requiring
explicit 4-cycle witnesses on generic vertex types.

## What's queued

- `n = 26` Phase 3A in flight; estimated ~30 min more.
- Push to `n ∈ {28, 30, 32}` after `n = 26` completes; each is
  ~3× the prior wall-time.
- Phase 4: build `walk8` analogue (`CycleHelpers.lean` extension)
  for Carr Case 2C (the cleanest 8-cycle construction).
- Phase 2 (full cubic to `n ≥ 30`): the `n = 22` cubic run was
  killed; needs streaming + parallelism per memo 0042's TODO.

## Per-phase progress against the 4-phase plan

| Phase | Status | Probability-weighted next outcome |
|---|---|---|
| 1 SAT cycle-encoder | ✅ done | enables 2 and 3 |
| 2 push exhaustive cubic to `n ≥ 30` | ⬜ infra in place, run not yet executed at `n ≥ 22` | pipeline needs parallelism |
| 3A bipartite cubic girth-6 empirical | 🟨 `n ≤ 24` done; `n ≤ 32` in progress | extending to `n = 32` likely 1–2 days more wall-time |
| 3B bipartite cubic girth-6 structural | ⬜ target memo only; BFS sketch has obstacle | low probability of closure |
| 4 Carr 2026 diameter-2 Lean translation | 🟨 prereq + pre-case done; 4 cases remaining | medium-high probability of closure over 1–2 weeks |

## Honest non-goals reminder

No commit, memo, or PR in this session claims any progress on
the parent Erdős–Gyárfás conjecture. The 205-graph empirical
record is *evidence*, not a proof. The Phase 4 pre-case is a
*sub-case sub-step*, not a sub-case proof.
