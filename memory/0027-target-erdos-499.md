# Erdős 499 — target evaluation (Marcus-Minc, parent SOLVED, plby bridge)

**Status:** in-progress
**Date:** 2026-05-11
**Related:** 0013 (bridge pipeline), 0026 (just-shipped Erdős 613)

## 2×2 cell

**Known proof × Solving a sorry → Goal 2.**

Parent problem on `erdosproblems.com/499` is SOLVED ("PROVED (LEAN)"
status). The Marcus-Minc 1962 theorem: every n×n doubly stochastic
matrix admits a permutation σ with ∏ M_{i,σ(i)} ≥ n^{-n}.

A Lean formalisation exists in
[`plby/lean-proofs/src/latest/ErdosProblems/Erdos499.lean`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos499.lean)
(229 lines), authored by Aristotle from Harmonic.

## Upstream sorry

```lean
@[category research solved, AMS 15]
lemma erdos_499 :
    answer(True) ↔ (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n),
      ∃ σ : Equiv.Perm (Fin n), n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) := by
  sorry
```

`answer(True)` ⇒ `True`, so the iff is `True ↔ RHS`, equivalent to
proving RHS directly.

## plby's local statement

```lean
theorem erdos_499 :
    (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) := by ...
```

Identical RHS. Bridge is a one-line wrapper.

## Proof strategy (Aristotle's)

1. `entropy_inequality`: For DS matrix M, ∑ᵢⱼ Mᵢⱼ log Mᵢⱼ ≥ n log(1/n).
   This is the convex AM-GM / log-sum / Gibbs inequality applied to
   the row-sum constraints, exploiting that the constant matrix 1/n is
   the minimizer.
2. Decompose M as a convex combination of permutation matrices
   (Birkhoff-von Neumann) via mathlib's `exists_eq_sum_perm_of_mem_doublyStochastic`.
3. Show by averaging that some permutation σ in the support has
   ∑ᵢ log M_{i, σ(i)} ≥ n log(1/n). Exponentiating gives ∏ M_{i, σ(i)} ≥ n^{-n}.

The Birkhoff decomposition guarantees positivity of `M_{i, σ(i)}` for
σ in the support, allowing the log to make sense.

## Format & toolchain

plby's file head says `leanprover/lean4:v4.29.1  mathlib v4.29.1`.
Builds cleanly at our `mathlib v4.28.0` with **no drift fixes** needed.

229 lines too long for inline upstream PR (limit 25–50). Local
artifact + `@[formal_proof using lean4 at "..."]` annotation upstream.

## Verdict

**Go.** Same Goal-2 bridge pattern as memos 0017/0014/0015 etc.
Build clean; axiom check passes. Bridge file 1 line of actual logic.
