# Erdős 198 — bridge

**Status:** shipped (local).
**Date:** 2026-05-10.
**Related:** 0013 (pipeline tracking).
**Upstream:** `formal-conjectures/.../198.lean`, `Erdos198.erdos_198`
(unchanged, still `:= by sorry`).

## Source

plby/Alexeev's [Erdos198.lean](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos198.lean)
(161 lines, no axioms; v4.24.0). AlphaProof's `A = {(n+1)! + n}` Sidon set
hits every infinite AP.

## Drift fixes (v4.24.0 → v4.28.0)

1. `hab.not_lt` (LE.le.not_lt projection gone) → `Nat.not_lt.mpr hab`.
2. `Set.eq_empty_of_forall_not_mem` → `Set.eq_empty_iff_forall_notMem.mpr`.
3. `bound;` top-level iff split (no longer valid) → `constructor; intro a; ...; intro h; exact h.elim`.

(plus `le_or_lt` → `le_or_gt` in the bridge file).

The proof file emits 12 non-fatal `aesop: failed` warnings; they're tactic
backtrack messages, not errors — proof succeeds because surrounding tactics
close the goals. `#print axioms` is clean.

## Bridge

- Reproduces upstream FCM `IsSidon` (symmetric form) and
  `Set.IsAPOfLength` (matches the gist's `IsAPOfLength` definitionally).
- Predicate translation: `Gist.IsSidon A → IsSidon A` via 4-way case
  analysis on `i₁ ⋚ i₂`, `j₁ ⋚ j₂`, applying the gist's normalised form
  with appropriate swaps.
- Final theorem: composes gist's `erdos_198` (¬-shape) with the
  `answer(False) ↔ _` outer wrapping.

161 (gist) + 84 (bridge) = 245 lines total.

## Axioms

```
'Erdos198.erdos_198' depends on axioms: [propext, Classical.choice, Quot.sound]
```
