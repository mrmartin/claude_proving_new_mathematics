# Erdős 370 — bridge

**Status:** shipped (local).
**Date:** 2026-05-10.
**Related:** 0013.

## Source

plby/Alexeev's [Erdos370.lean](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos370.lean)
(190 lines): infinitely many `n` with `maxPrimeFac n < √n ∧ maxPrimeFac (n+1) < √(n+1)`,
constructed via `(k! + 3)² - 1` and the three-consecutive-composites trick.

## Drift fixes

None needed (only removed the gist's literal `#print axioms erdos_370`
line, which was a debugging statement).

## Bridge

`Nat.maxPrimeFac` (upstream FCM) and `Erdos370.Gist.maxPrimeFac` (local)
have identical definitions (`sSup {p | p.Prime ∧ p ∣ n}`). Bridge:
reproduce `Nat.maxPrimeFac` verbatim, then `convert Gist.erdos_370.mpr trivial using 2`.

## Axioms

```
'Erdos370.erdos_370' depends on axioms: [propext, Classical.choice, Quot.sound]
```
