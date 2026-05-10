# Erdős 259 — bridge

**Status:** shipped (local).
**Date:** 2026-05-10.
**Related:** 0013.

## Source

ster-oc's [Erdos259.lean](https://gist.githubusercontent.com/ster-oc/c7429943f6b3a634797dc8b2a3b01f2d/raw/8c6b5b7f08021f0aed2312542dd2e9ee7beaa6d6/Erdos259.lean)
(1012 lines). Chen–Ruzsa irrationality criterion applied to the Möbius
series `∑ μ(n)² · n / 2ⁿ`.

## Drift fixes

None — the gist was generated against a recent mathlib that's close
enough to v4.28.0.

## Bridge

`Bridge.lean` opens `ArithmeticFunction.Moebius` for the `μ` notation,
then proves the upstream signature by `convert Gist.erdos_259 using 1`
plus `push_cast; ring` to align the cast paths
(`(moebius n)^2 : ℤ → ℝ` vs `(μ n)^2 : ℝ` direct).

## Axioms

```
'Erdos259.erdos_259' depends on axioms: [propext, Classical.choice, Quot.sound]
```
