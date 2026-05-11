# Erdős 1148 `.variants.weaker` — target evaluation

**Status:** in-progress (drafting the proof)
**Date:** 2026-05-11
**Related:** 0006 (catalogue infra)
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/1148.lean`

## 2×2 cell

**Known informal proof × Solving a sorry → Goal 2.**

The main problem `erdos_1148` on `erdosproblems.com/1148` was solved in
2026 by Chojecki via a Duke-type equidistribution theorem (status:
**PROVED**, with partial Lean reduction conditional on Duke's theorem
in a forum thread). That puts the file in-scope per the parent-problem
gating rule.

We are NOT going to formalise the main `erdos_1148` (Duke's theorem
is way beyond our scope). We target the *weaker* variant noted in
[Va99] as "obvious":

```lean
@[category research solved, AMS 11]
theorem erdos_1148.variants.weaker : ∀ n, erdos_1148_weaker_prop n := by
  sorry
```

where

```lean
def erdos_1148_weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n
```

## Informal proof (constructive, by cases on `n mod ⌊√n⌋²`)

Let `q = ⌊√n⌋` and `r = n - q² ∈ [0, 2q]`.

Case A: `r = 0` (so `n = q²`). Take `(x, y, z) = (q, 0, 0)`.
  Then `x² = q² = n ≤ n + 2√n`. ✓

Case B: `r` is odd (so `r ≥ 1`, and `r ≤ 2q - 1`).
  Take `(x, y, z) = (q, (r+1)/2, (r-1)/2)`.
  Check: `x² + y² - z² = q² + ((r+1)² - (r-1)²)/4 = q² + r = n`. ✓
  Bounds: `x² = q² ≤ n`; `y = (r+1)/2 ≤ q`, so `y² ≤ q² ≤ n`; `z ≤ y`. ✓

Case C: `r ≡ 0 (mod 4)`, `r ≥ 4`.
  Take `(x, y, z) = (q, r/4 + 1, r/4 - 1)`.
  Check: `y² - z² = (r/4+1)² - (r/4-1)² = r`, so `x² + y² - z² = q² + r = n`. ✓
  Bounds: `x² = q² ≤ n`; `y = r/4 + 1 ≤ q/2 + 1 ≤ q + 1` and `y² ≤ (q+1)²
  ≤ n + 2√n + 1`. Actually `r ≤ 2q` gives `y ≤ q/2 + 1`, so `y² ≤ q²/4 + q
  + 1 ≤ n`.

Case D: `r ≡ 2 (mod 4)`, so `r ≥ 2` and `r ≤ 2q` (`q ≥ 1`).
  Take `(x, y, z) = (q + 1, q - r/2, q + 1 - r/2)`.
  Check: `x² + y² - z² = (q+1)² - (q+1 - r/2)² + (q - r/2)²
                       = (r/2)(2q + 2 - r/2) + (q - r/2)²
                       = rq + r - r²/4 + q² - rq + r²/4
                       = q² + r = n`. ✓
  Bounds: `y = q - r/2 ≤ q - 1`, `y² ≤ (q-1)² ≤ q² ≤ n`.
          `z = q + 1 - r/2 ≤ q`, `z² ≤ q² ≤ n`.
          `x² = (q+1)² = q² + 2q + 1`. We need `x² ≤ n + 2√n = q² + r
          + 2√n`, i.e. `2q + 1 ≤ r + 2√n`. Since `r ≥ 2` and `√n ≥ q`
          (as `q² ≤ n`), `r + 2√n ≥ 2 + 2q`, so `2q + 1 ≤ 2q + 2`. ✓

All cases close with explicit witnesses; no asymptotic argument needed.

## Mathlib lemmas expected

- `Nat.sqrt_le_self` / `Nat.sqrt_le'` / `Nat.lt_succ_sqrt'`: gives `q² ≤
  n < (q+1)²`, hence `r ≤ 2q`.
- `Nat.sqrt_le_sqrt`, `Real.sqrt_le_sqrt`: bridges `q ≤ √n` in `ℝ`.
- `Real.sq_sqrt`, `Real.sqrt_nonneg`, etc.
- Basic `nlinarith` / `omega` / `ring` for the algebraic checks.

## Format & line budget

Short proof. Estimate ≤ 60 lines inline. Will try inline first,
overflow to `proofs/erdos1148weaker/` if needed.

## Verdict

**Go.** Clean Goal-2 candidate, classical construction, no exotic
machinery. Status check passed (parent SOLVED on erdosproblems.com).
