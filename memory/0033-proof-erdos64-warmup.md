# Erdős 64 — `WarmUp.lean`: three small graphs verified

**Kind:** proof
**Status:** shipped (local). Axiom-clean.
**Date:** 2026-05-11
**Related:** 0031 (target), 0032 (skeleton), plan at
`~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-3-adjacent partial result on an open conjecture. None of these
three graphs are claims of progress on Erdős 64 itself — they are
toolkit exercises and Lean infrastructure tests.

## What this commit ships

`proofs/erdos64/Erdos64/WarmUp.lean` (~140 lines). Three specific
small graphs are shown to satisfy `Has2PowCycle G`:

- `K4_has_2pow_cycle` — `K₄ = completeGraph (Fin 4)` via the 4-cycle
  `0 → 1 → 2 → 3 → 0`.
- `K33_has_2pow_cycle` — `K_{3,3} = completeBipartiteGraph (Fin 3) (Fin 3)`
  via the 4-cycle `inl 0 → inr 0 → inl 1 → inr 1 → inl 0`.
- `prism3_has_2pow_cycle` — the 3-prism `K₃ □ K₂` (encoded as
  `inductive Prism3 | A (i : Fin 3) | B (i : Fin 3)` and an explicit
  `Adj'` pattern-match) via the 4-cycle `A0 → A1 → B1 → B0 → A0`.

Each theorem reduces to `Has2PowCycle G` via
`Erdos64.has_2pow_cycle_of_has_C4` from `Basic.lean`.

## Lean discipline tricks learned

- `decide` doesn't reduce through an opaque `private def K4Cycle` by
  default. Solution: keep the walk as a top-level `def`, then
  `unfold K4Cycle` before each `decide` on `K4Cycle.edges.Nodup`,
  `K4Cycle ≠ .nil`, and `K4Cycle.support.tail.Nodup`.
- `Walk.IsCycle` is a *structure*, not a Prop with a global Decidable.
  We decompose via `Walk.isCycle_def` and `Walk.isTrail_def` to get
  the three list-Nodup obligations, each of which is `decide`-able
  after `unfold`.
- `(completeBipartiteGraph (Fin 3) (Fin 3)).Adj` doesn't have a
  globally-registered `DecidableRel` instance in mathlib v4.28.0; we
  defined a local one via `K33_decAdj` that unfolds the definition
  and uses `infer_instance`.
- `inductive V deriving Fintype` works on v4.28.0; combined with the
  `loopless := ⟨...⟩` style (the field is `Std.Irrefl`, a one-field
  structure, not just `∀ v, ¬ Adj v v`).

## Axiom check

```
'Erdos64.K4_has_2pow_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos64.K33_has_2pow_cycle' depends on axioms: [propext, Quot.sound]
'Erdos64.prism3_has_2pow_cycle' depends on axioms: [propext, Quot.sound]
```

— the standard subset, no `sorryAx`, no `Lean.ofReduceBool`.

## Why this matters (and what it doesn't claim)

- This is **not** a contribution to Erdős 64. The 4-cycle exists in
  each graph trivially.
- It IS the project's first Lean output for Erdős 64 — the
  `Walk` / `IsCycle` / `unfold + decide` pattern is now banked for
  Track A4 (`Markstrom.lean`), where we will encode Petersen,
  Möbius–Kantor, Heawood, etc. on the same plan.
- The `Prism3` `inductive V` + `Adj'` pattern-match is a clean
  prototype for the Pikhurko-style encoding pattern Tao used in
  `proofs/erdos613/Erdos613/Tao.lean` for the 16-vertex
  counterexample graph.

## Next

Commit 3: `Erdos64/GirthDiam.lean` with the mathlib gap-fill
`SimpleGraph.girth_le_two_mul_diam_add_one` (Track C1).
