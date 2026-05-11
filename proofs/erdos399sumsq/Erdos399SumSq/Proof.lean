/-
**Partial Goal-2 contribution toward Erdős Problem 399
`.variants.sum_two_squares`.**

The full upstream sorry is:

  ∀ {n x y : ℕ}, 1 < x * y → n ! = x ^ 2 + y ^ 2 →
    n = 6 ∧ (x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12)

This file closes the `n ≤ 6` portion (the *finite* part of the
characterization): every solution with `1 < xy` and `n! = x² + y²` for
`n ≤ 6` has `n = 6` and `(x, y) ∈ {(12, 24), (24, 12)}`.

The `n ≥ 7` portion is the asymptotic claim that `n!` is *never* a sum
of two squares. The standard textbook proof uses

  *Bertrand-in-AP for primes ≡ 3 (mod 4)*:
    `∀ n ≥ 7, ∃ p prime, p ≡ 3 (mod 4) ∧ n / 2 < p ∧ p ≤ n`.

Combined with Fermat-Gauss (mathlib's `Nat.eq_sq_add_sq_iff`), the
asymptotic claim follows from such a prime giving `v_p(n!) = 1` (odd).
Mathlib has plain Bertrand and Dirichlet's infinitude of primes in AP,
but **not** Bertrand-in-AP, so the asymptotic step is currently a
genuine gap and is NOT proved here. See memo `0021` for the full
discussion.

What this file ships, no axioms beyond mathlib's standard three, no
`sorry`:

* `no_solutions_lt_six`: for `n < 6`, no `(x, y)` with `1 < xy` solves
  `n! = x² + y²`.
* `solutions_at_six`: for `n = 6`, exactly `(12, 24)` and `(24, 12)`.
* `sum_two_squares_of_le_six`: the combined `n ≤ 6` statement.
-/

import Mathlib

namespace Erdos399SumSq

open Nat

private lemma n_zero {x y : ℕ} (hxy : 1 < x * y) (heq : (0 : ℕ) ! = x ^ 2 + y ^ 2) :
    False := by
  simp only [Nat.factorial_zero] at heq
  have hx : x ≤ 1 := by nlinarith
  have hy : y ≤ 1 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private lemma n_one {x y : ℕ} (hxy : 1 < x * y) (heq : (1 : ℕ) ! = x ^ 2 + y ^ 2) :
    False := by
  simp only [Nat.factorial_one] at heq
  have hx : x ≤ 1 := by nlinarith
  have hy : y ≤ 1 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private lemma n_two {x y : ℕ} (hxy : 1 < x * y) (heq : (2 : ℕ) ! = x ^ 2 + y ^ 2) :
    False := by
  have h2 : (2 : ℕ) ! = 2 := by decide
  rw [h2] at heq
  have hx : x ≤ 1 := by nlinarith
  have hy : y ≤ 1 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private lemma n_three {x y : ℕ} (heq : (3 : ℕ) ! = x ^ 2 + y ^ 2) : False := by
  have : (3 : ℕ) ! = 6 := by decide
  rw [this] at heq
  have hx : x ≤ 2 := by nlinarith
  have hy : y ≤ 2 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private lemma n_four {x y : ℕ} (heq : (4 : ℕ) ! = x ^ 2 + y ^ 2) : False := by
  have : (4 : ℕ) ! = 24 := by decide
  rw [this] at heq
  have hx : x ≤ 4 := by nlinarith
  have hy : y ≤ 4 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private lemma n_five {x y : ℕ} (heq : (5 : ℕ) ! = x ^ 2 + y ^ 2) : False := by
  have : (5 : ℕ) ! = 120 := by decide
  rw [this] at heq
  have hx : x ≤ 10 := by nlinarith
  have hy : y ≤ 10 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private lemma n_six {x y : ℕ} (hxy : 1 < x * y) (heq : (6 : ℕ) ! = x ^ 2 + y ^ 2) :
    x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12 := by
  have : (6 : ℕ) ! = 720 := by decide
  rw [this] at heq
  have hx : x ≤ 26 := by nlinarith
  have hy : y ≤ 26 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

/-- For every `n < 6`, there are no `(x, y) : ℕ²` with `1 < x * y` and
`n! = x² + y²`. -/
theorem no_solutions_lt_six : ∀ {n x y : ℕ}, n < 6 → 1 < x * y → n ! ≠ x ^ 2 + y ^ 2 := by
  intro n x y hn hxy heq
  interval_cases n
  · exact n_zero hxy heq
  · exact n_one hxy heq
  · exact n_two hxy heq
  · exact n_three heq
  · exact n_four heq
  · exact n_five heq

/-- At `n = 6`, the only solutions to `6! = x² + y²` with `1 < x * y` are
`(x, y) = (12, 24)` and `(x, y) = (24, 12)`. -/
theorem solutions_at_six : ∀ {x y : ℕ}, 1 < x * y → (6 : ℕ) ! = x ^ 2 + y ^ 2 →
    x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12 := fun hxy heq => n_six hxy heq

/-- Combined: for every `n ≤ 6`, the only solutions to `n! = x² + y²` with
`1 < x * y` are at `n = 6` with `(x, y) ∈ {(12, 24), (24, 12)}`. -/
theorem sum_two_squares_of_le_six {n x y : ℕ} (hn : n ≤ 6) (hxy : 1 < x * y)
    (heq : n ! = x ^ 2 + y ^ 2) :
    n = 6 ∧ (x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12) := by
  interval_cases n
  · exact absurd heq (fun h => n_zero hxy h)
  · exact absurd heq (fun h => n_one hxy h)
  · exact absurd heq (fun h => n_two hxy h)
  · exact absurd heq (fun h => n_three h)
  · exact absurd heq (fun h => n_four h)
  · exact absurd heq (fun h => n_five h)
  · exact ⟨rfl, n_six hxy heq⟩

end Erdos399SumSq
