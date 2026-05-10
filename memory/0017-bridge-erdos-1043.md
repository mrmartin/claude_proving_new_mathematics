# Erdős 1043 — bridge

**Status:** shipped (local).
**Date:** 2026-05-10.
**Related:** 0013.

## Source

plby/Alexeev's [Erdos1043.lean](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1043.lean)
(225 lines). Pommerenke 1961: counterexample to "every monic complex
polynomial has a line whose projection of the unit-modulus level set
has measure ≤ 2". The gist exhibits `f(z) = z^k - 1` (`counterexample_poly`)
for the right `k`.

## Drift fixes

`MulAction.mul_smul` → `mul_smul` (renamed in v4.28.0).

## Bridge

Gist proves `¬ ∀ f, ...`. Upstream wants `answer(False) ↔ ∀ f, ...`.
`answer(False) ↔ X` iff `False ↔ X` iff `¬X`, so bridge is
`refine ⟨fun h => h.elim, fun h => Gist.erdos_1043 h⟩`.
Reproduces upstream's `levelSet` def (identical to gist's local one).

## Axioms

```
'Erdos1043.erdos_1043' depends on axioms: [propext, Classical.choice, Quot.sound]
```
