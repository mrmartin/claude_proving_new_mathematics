# Erdős 64 — stop and wrap

**Kind:** infra / decision
**Status:** Erdős 64 work stopped on 2026-05-12 per user direction.
**Date:** 2026-05-12
**Related:** All `0031`–`0049` (the entire Erdős-64 track).

## Decision

Stop all Erdős-64 work. Specifically:

- **Phase 3A** (bipartite cubic girth-6 empirical search) is **abandoned**;
  do not run `bipartite_girth6_partitioned.py` for `n ∈ {30, 32}`.
  Results stored for `n ∈ [14, 28]` are retained on disk.
- **Phase 2** (full cubic exhaustive search) is **abandoned**; do not run
  `exhaustive_cubic_partitioned.py` past the existing `n=14`, `n=20`
  sanity checks.
- **Phase 4 Case 1** (Carr 2026 "one shared neighbour", ~250 lines) is
  **not** going to be written.
- **Phase 3B** (structural BFS-layer argument for bipartite cubic girth-6
  ⇒ has `C_8`) is **not** going to be attempted.

## Why

The remaining feasible Erdős-64 deliverables are:

1. The completion of Carr 2026's diameter-2 translation in Lean
   (Case 1, ~250 lines, plus main-body wiring).
2. The computational closure of the bipartite-cubic-girth-6 sub-case on
   `n ≤ 32` ("unconditional bipartite cubic Erdős 64 on small `n`").

Both fail the `formal-conjectures` shape test. The repo's mission is to
formalise mathematics — published proofs (Goal 2) or genuinely new
mathematics (Goal 3). It does **not** value:

- Computer-checked finite-`n` enumerations packaged as Lean theorems,
  regardless of how axiom-clean.
- "First Lean-verified statement of sub-case X" as a standalone artifact.
- Translating a published sub-case (Carr 2026) of an *open* parent
  problem — by the project's own HARD GATING RULE, the parent is open
  and the sub-case is "Goal-3-adjacent", which is a slot the repo
  doesn't actually accept upstream contributions to.

The mathematical content we could actually produce on Erdős 64 in a
session-scale budget is one of:

- A finite-`n` table re-stated as a theorem (not real mathematics);
- A Lean translation of a published sub-case of an open problem (not
  upstream-accepted; doesn't advance the parent conjecture);
- A counter-example or full proof of the parent conjecture
  (probability ≈ 10⁻⁶ / ≈ 0 respectively over the next year).

None of these fit the project. The right move is to stop and pick a
different target.

## What we are keeping (no rollback)

The repository on disk is left as-is. The committed work this session is:

| Commit | Content |
|---|---|
| `7f79076` | Phase 1: SAT cycle-encoder. |
| `f68f41e` | Phase 3A initial: bipartite cubic girth-6, `n ≤ 22`. |
| `8e9067d` | Phase 4 prereq: `CycleHelpers.lean` (`walk4_isCycle`, `has_2pow_cycle_of_chain4`). |
| `e2e722c` | Phase 4 pre-case: `carr2026_precase_two_shared_neighbours`. |
| `e4b32d1` | Session checkpoint 0046 (mid-day). |
| `0d5cf4b` | Phase 3A streaming variant (later superseded). |
| `abf79eb` | Phase 4: `walk8` + `has_2pow_cycle_of_isCycle_length_eight`. |
| `bae557b` | Phase 4 Case 2C: `walk8_isCycle` + `has_2pow_cycle_of_chain8`. |
| `6c4575d` | Phase 3A partitioned `geng res/mod`; `n ≤ 26`. |
| `3ec756d` | Phase 2 partitioned infra; `n=14`, `n=20` sanity. |
| `3b35b35` | Phase 4 Case 2A. |
| `a6ce81d` | Phase 4 Case 2B. |
| `15e82c0` | Checkpoint memo 0049 (round 2). |
| `41c7f56` | Phase 3A `n=28` result (11 415 girth-6 graphs all pass). |
| this commit | This memo; track is wound down. |

The committed artefacts are kept rather than reverted because they
represent real engineering hours and are axiom-clean, but the Erdős-64
track is closed. Future sessions: do **not** revive Phase 3A / Phase 4 /
Phase 2 unless the project's posture toward Erdős 64 changes
(it shouldn't, per the user's 2026-05-12 direction).

## Specific feedback retained in auto-memory

Saved as `feedback_formal_conjectures_not_artifact_shop.md` (in the
auto-memory directory):

> `formal-conjectures` cares about *actually formalised mathematics* —
> translating a published proof (Goal 2) or proving new mathematics
> (Goal 3). It does not value first-Lean-verified-X artifacts or
> computational small-`n` closures, even when axiom-clean.

## Next session — pivot

Erdős 64 is not the right target. Better targets exist on
`formal-conjectures`:

- A `category research solved` problem with a known *short* informal
  proof and no `formal_proof using …` annotation — that's pure Goal 2,
  no judgement calls about open-parent / sub-case shape.
- A `category textbook` problem ditto.
- Something where the catalogue (Goal 1 of the project) would clearly
  surface a sharp short target.

Goal 1 (the catalogue itself) was scoped in `0006` but isn't built;
that's a candidate session priority.

## Honest framing

The Erdős-64 track produced legitimate engineering output — Phase 1 +
Phase 3A partitioning + Phase 4 helpers + 4 of 5 Carr 2026 cases — but
**none of it is a contribution `formal-conjectures` would accept or that
advances the parent conjecture**. The lesson is encoded in the
auto-memory feedback entry above.
