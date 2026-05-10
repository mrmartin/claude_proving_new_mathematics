# Erdős 645 — bridge

**Status:** shipped (local).
**Date:** 2026-05-10.
**Related:** 0013 (pipeline tracking).
**Upstream:** `formal-conjectures/.../645.lean`, `Erdos645.erdos_645`.

## Source

plby/Alexeev's [Erdos645.lean](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos645.lean)
(172 lines). Brown–Landman 1999 / Alweiss's argument: every 2-colouring
of ℕ has a monochromatic 3-AP `x, x+d, x+2d` with `d > x`.

## Drift fixes (v4.24.0 → v4.28.0)

`bound;` used as a forall-splitter (no longer valid in v4.28.0):
- `case_1_inductive`: replaced `bound; induction a <;> aesop; apply case_1_step ...`
  with explicit `intro m hm; induction m with | zero | succ k ih`.
- `h_inductive` (inside `case_2_impossible`): replaced `bound; exact?` with
  explicit `intro k; exact case_2_inductive c h_contra h1 h5 n hn.1 hn.2 k`.

## Bridge

Gist's `erdos_645` matches upstream signature character-for-character.
1-line bridge: `exact Gist.erdos_645 c`.

## Axioms

```
'Erdos645.erdos_645' depends on axioms: [propext, Classical.choice, Quot.sound]
```
