# Erdős 64 — session checkpoint, 2026-05-12 (round 2)

**Kind:** infra / checkpoint
**Status:** in-progress (n=28 running)
**Date:** 2026-05-12
**Related:** 0046 (previous checkpoint earlier today), 0047 (Phase
3A partitioned), 0048 (Phase 4 Case 2C). Plan
`~/.claude/plans/zesty-launching-origami.md`.

## What this round of the session shipped

Commits `abf79eb` → `a6ce81d` (5 commits this round):

### Phase 3A — partitioned `geng res/mod` (memo 0047)

Diagnosed and fixed the real bottleneck:
**geng is single-threaded, ~91 graphs/s**, so no worker-pool
Python parallelism could help. Switched to spawning M parallel
`geng -bcd3 -D3 n R/M -q` slices, one Python worker per slice.

- 14.9× speedup at `n = 24` (342 s → 23 s, same 162 girth-6 graphs).
- **`n = 26`: 245 627 bipartite cubic, 1 201 girth-6, all C_8 (215 s).**
- `n = 28` in flight as of this memo (estimated finish ~12:00 UTC,
  using the 9.3× growth observed `n = 24 → n = 26`).

`bipartite_girth6_partitioned.py` + result JSONs `n14.json` …
`n26.json`. Cumulative Phase 3A: **1 406 girth-6 graphs all have
C_8 across `n ∈ [14, 26]`. Zero candidate counterexamples.**

### Phase 2 — partitioned exhaustive cubic infra

`exhaustive_cubic_partitioned.py` mirrors the bipartite partitioning
but on the full `-cd3 -D3` enumeration. Sanity-checked against the
prior baselines:

- `n = 14`: 509 graphs, all 2^k cycle (0.2 s @ 4 slices).
- `n = 20`: **510 489** connected cubic graphs, all 2^k cycle (131 s
  @ 4 slices). Reproduces OEIS A002851.

Pipeline ready for `n = 22` (7.3 M graphs, ~30 min @ 48 slices).
Held until `n = 28` Phase 3A completes (to avoid 2× core
oversubscription).

### Phase 4 — `walk8_isCycle` + 3 of 4 remaining Carr cases (memo 0048)

`Erdos64.CycleHelpers`:
- `walk8_isCycle`: full 8-cycle constructor (~120 lines, 28
  distinctness obligations, axiom-clean).
- `has_2pow_cycle_of_chain8`: convenience wrapper mirroring the
  chain-4 helper.

`Erdos64.DiamTwo`: now discharges **4 of 5 Carr 2026 sub-cases**:

| Case | Status |
|---|---|
| Pre-case (two shared neighbours → C₄) | ✅ |
| Case 2C (zero shared, `v₈ ∉ {v₁,v₂}`) | ✅ |
| Case 2A (zero shared, `v₈ = v₁`)       | ✅ |
| Case 2B (zero shared, `v₈ = v₂`)       | ✅ |
| Case 1  (one shared neighbour, Carr's main case, ~250 lines) | ⬜ |
| Main theorem body                       | `sorry` |

All 4 discharged cases axiom-clean (`[propext, Classical.choice,
Quot.sound]`).

## Current Lean state

| Module | Lines | Status |
|---|---:|---|
| `Erdos64/Basic.lean` | 86 | axiom-clean |
| `Erdos64/CycleHelpers.lean` | 280 | axiom-clean (was 150) |
| `Erdos64/WarmUp.lean` | 139 | axiom-clean |
| `Erdos64/Bipartite.lean` | 84 | axiom-clean |
| `Erdos64/BipartiteCubic.lean` | 108 | axiom-clean |
| `Erdos64/DiamTwo.lean` | 295 | 1 `sorry` (main body); 4 of 5 sub-cases discharged |
| `Erdos64/Markstrom.lean` | 161 | axiom-clean |

**Total: ~1153 lines of Lean** (up from ~780). All axiom-clean
except the one documented sorry in `DiamTwo.lean::carr2026_diam_two_minDegree_three`'s
body.

## Per-phase progress against the 4-phase plan

| Phase | Status this round | Cumulative |
|---|---|---|
| 1 SAT cycle-encoder | (no change) | ✅ done |
| 2 push exhaustive cubic to `n ≥ 30` | infra ready; n=14, n=20 sanity | 🟨 ready to launch |
| 3A bipartite cubic girth-6 empirical | n=26 ✅ shipped, n=28 in flight | 🟨 `n ≤ 26` done; `n ≤ 32` 1-2 days more |
| 3B bipartite cubic girth-6 structural | (no change) | ⬜ target memo only |
| 4 Carr 2026 diameter-2 Lean translation | 3 cases discharged this round | 🟨 4 of 5 cases done; Case 1 + body remain |

## Honest framing reminder

This round shipped:
- 1 405 new bipartite-cubic-girth-6 graphs verified (`n ∈ {24, 26}`,
  bringing total to 1 406).
- 3 new explicit-cycle case-discharges (Case 2A, 2B, 2C of Carr
  2026's argument).
- Phase 2 infrastructure ready for the long-running cubic
  enumeration.

**None of this advances the parent Erdős–Gyárfás conjecture.** The
Phase 3A empirical record is *evidence*, not a proof. The Phase 4
cases are *Goal-3-adjacent partial work* on an open problem
(Carr 2026 is itself a published sub-case argument, so we're
formalising published mathematics; Erdős 64's parent is still open).

## What's queued

- `n = 28` Phase 3A: finishing now in background.
- `n ∈ {30, 32}` Phase 3A: launch sequentially after n=28; each
  ~10× the prior wall-time. `n = 32` would close the empirical
  campaign by reaching Nowbandegani–Esfandiari's bound.
- Phase 2 `n = 22`: ready to launch after n=28 frees cores
  (7.3 M graphs, ~30 min estimated).
- Phase 4 Case 1: ~250 lines, mechanical but the largest remaining
  Carr block. Not in the highest-EV slot.
- Phase 4 main theorem body: requires deriving the 28 pairwise
  distinctness from the diameter-2 + min-deg-3 setup, plus
  existence of `v₇`, `v₈`, `x`, `y` under diameter-2. Genuine new
  Lean work (not just mechanical case-relabelling).

## Lessons (also recorded in 0047)

- **Always benchmark dependencies, not just your Python.** Two
  iterations on Python-side worker pools before measuring geng
  itself — geng was always the ceiling.
- `geng R/M` is the right partition primitive for nauty-driven
  searches at scale.
- The walk4-pattern scales: `walk8_isCycle` is ~120 lines of the
  exact same `Walk.cons_isCycle_iff` + `Walk.isPath_def` +
  `simp` + `Sym2_ne_of_pairwise_distinct` machinery; would extend
  similarly to walk16 should a Case-1 cycle of length 16 arise.
- Each Case-2X dispatch is ~80 lines of mechanical relabelling
  boilerplate. Diminishing returns past the first 2-3 cases. Case 1
  is qualitatively different (one shared neighbour ⇒ Claims 1.1-1.6
  inductive argument) and deserves its own design pass.

## Next

- Wait for n=28 to complete (Monitor armed).
- On n=28 completion: update memo 0047 with row, commit + push.
- Optionally launch n=30 + Phase 2 n=22 in background.
- Possibly close session with this checkpoint as the end-state.
