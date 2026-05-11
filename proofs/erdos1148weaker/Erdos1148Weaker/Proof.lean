/-
**Goal-2 contribution: Erdős Problem 1148 — `.variants.weaker`.**

The upstream sorry (Va99 'obvious'):

  ∀ n : ℕ, ∃ x y z : ℕ,
      n = x^2 + y^2 - z^2 ∧
      (x^2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
      (y^2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
      (z^2 : ℝ) ≤ n + 2 * Real.sqrt n.

Construction:  let `q = Nat.sqrt n`, `r = n - q²` (so `0 ≤ r ≤ 2q`).

  Case A: `r = 0`          → `(q, 0, 0)`.
  Case B: `r` odd          → `(q, (r+1)/2, (r-1)/2)`.
  Case C: `r ≡ 0 (mod 4)`  → `(q, r/4 + 1, r/4 - 1)`.
  Case D: `r ≡ 2 (mod 4)`  → `(q + 1, q - r/2, q + 1 - r/2)`.
-/

import Mathlib

namespace Erdos1148Weaker

open Nat Real

/-- The Erdős-1148-weaker property. -/
def Weaker (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

/-- `(Nat.sqrt n : ℝ) ≤ Real.sqrt n`. -/
private lemma nat_sqrt_le_real_sqrt (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
  have h : ((Nat.sqrt n) ^ 2 : ℝ) ≤ (n : ℝ) := by
    have := Nat.sqrt_le n
    have h2 : (Nat.sqrt n) ^ 2 ≤ n := by simpa [pow_two] using this
    exact_mod_cast h2
  have hq : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hq] at this

/-- `q² ≤ n` and `n - q² ≤ 2q` for `q = Nat.sqrt n`. -/
private lemma sqrt_resid (n : ℕ) :
    (Nat.sqrt n) ^ 2 ≤ n ∧ n - (Nat.sqrt n) ^ 2 ≤ 2 * Nat.sqrt n := by
  refine ⟨?_, ?_⟩
  · have := Nat.sqrt_le n; simpa [pow_two] using this
  · have h1 : (Nat.sqrt n) ^ 2 ≤ n := by have := Nat.sqrt_le n; simpa [pow_two] using this
    have h2 : n < (Nat.sqrt n + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt n; simpa [pow_two] using this
    have hexp : (Nat.sqrt n + 1) ^ 2 = (Nat.sqrt n) ^ 2 + 2 * Nat.sqrt n + 1 := by ring
    omega


/-- Main theorem. -/
theorem witness_spec (n : ℕ) : Weaker n := by
  set q : ℕ := Nat.sqrt n with hq_def
  obtain ⟨hq_sq, hr_le⟩ := sqrt_resid n
  rw [← hq_def] at hq_sq hr_le
  set r : ℕ := n - q ^ 2 with hr_def
  have hn_eq : n = q ^ 2 + r := by omega
  -- Real-side bounds
  have hq_real_sq : ((q : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hq_sq
  have hq_real_sqrt : ((q : ℝ)) ≤ Real.sqrt n := nat_sqrt_le_real_sqrt n
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have h_qsq_le : ((q : ℝ)) ^ 2 ≤ (n : ℝ) + 2 * Real.sqrt n := by linarith
  -- Case A: r = 0
  rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
  · refine ⟨q, 0, 0, ?_, h_qsq_le, by simp; linarith, by simp; linarith⟩
    have : n = q ^ 2 := by omega
    simp [this]
  -- r ≥ 1; deduce q ≥ 1 too
  have hq_pos : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · simp [hq0] at hr_le; omega
    · exact hq0
  have hq_real_pos : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pos
  by_cases hrodd : r % 2 = 1
  · -- Case B: r odd. Witness (q, (r+1)/2, (r-1)/2).
    have hr_ge_one : 1 ≤ r := hr_pos
    have hr_le_odd : r ≤ 2 * q - 1 := by
      have : r ≤ 2 * q := hr_le
      omega
    obtain ⟨k, hk⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    -- Now y = k+1, z = k.
    have hy_def : (r + 1) / 2 = k + 1 := by omega
    have hz_def : (r - 1) / 2 = k := by omega
    have hk_le : k + 1 ≤ q := by
      -- 2k+1 ≤ 2q - 1, so k ≤ q - 1, k+1 ≤ q
      omega
    refine ⟨q, k + 1, k, ?_, h_qsq_le, ?_, ?_⟩
    · -- Equation: q² + (k+1)² - k² = q² + 2k+1 = q² + r = n
      rw [hn_eq, hk]
      have : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
      omega
    · -- (k+1)² ≤ q² ≤ n + 2√n
      have hkq : ((k : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast hk_le
      have h0 : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ ((q : ℝ)) ^ 2 := by nlinarith
      push_cast
      nlinarith
    · -- k² ≤ (k+1)² ≤ q²
      have hkq : ((k : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast hk_le
      have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hsq : ((k : ℝ)) ^ 2 ≤ ((q : ℝ)) ^ 2 := by nlinarith
      nlinarith
  · -- r even
    have hr_even : r % 2 = 0 := by omega
    by_cases hr4 : r % 4 = 0
    · -- Case C: r ≡ 0 (mod 4), so r ≥ 4
      have hr_ge_4 : 4 ≤ r := by omega
      obtain ⟨k, hk⟩ : ∃ k, r = 4 * k := ⟨r / 4, by omega⟩
      have hk_pos : 1 ≤ k := by omega
      have hk_le : k ≤ q / 2 := by omega
      -- y = k + 1, z = k - 1
      refine ⟨q, k + 1, k - 1, ?_, h_qsq_le, ?_, ?_⟩
      · -- Equation: q² + (k+1)² - (k-1)² = q² + 4k = q² + r = n
        -- Use k = k0 + 1 to handle natural subtraction.
        obtain ⟨k0, hk0⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
        have hk1 : k - 1 = k0 := by omega
        have hk2 : k + 1 = k0 + 2 := by omega
        rw [hk1, hk2, hn_eq, hk, hk0]
        have hexp1 : (k0 + 2) ^ 2 = k0 ^ 2 + (4 * k0 + 4) := by ring
        have hexp2 : 4 * (k0 + 1) = 4 * k0 + 4 := by ring
        omega
      · -- (k+1)² ≤ (q/2 + 1)² ≤ q² + 2q ≤ n + 2√n
        have h4k : (4 * k : ℕ) ≤ 2 * q := by omega
        have hk_real : ((k : ℝ)) ≤ (q : ℝ) / 2 := by
          have : ((4 * k : ℕ) : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast h4k
          push_cast at this
          linarith
        have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        push_cast
        nlinarith
      · -- (k-1)² ≤ (k+1)² ≤ q² + 2q
        have hk1 : ((k - 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : k - 1 ≤ k + 1)
        have h0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h4k : (4 * k : ℕ) ≤ 2 * q := by omega
        have hk_real : ((k : ℝ)) ≤ (q : ℝ) / 2 := by
          have : ((4 * k : ℕ) : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast h4k
          push_cast at this
          linarith
        have hkr : ((k + 1 : ℕ) : ℝ) ≤ (q : ℝ) / 2 + 1 := by push_cast; linarith
        nlinarith
    · -- Case D: r ≡ 2 (mod 4), so r ≥ 2, x = q+1, y = q - r/2, z = q+1 - r/2
      have hr2 : r % 4 = 2 := by omega
      have hr_ge_2 : 2 ≤ r := by omega
      obtain ⟨m, hm⟩ : ∃ m, r = 2 * m := ⟨r / 2, by omega⟩
      have hm_pos : 1 ≤ m := by omega
      have hm_le_q : m ≤ q := by omega
      refine ⟨q + 1, q - m, q + 1 - m, ?_, ?_, ?_, ?_⟩
      · -- (q+1)² + (q-m)² - (q+1-m)² = q² + 2m = q² + r = n
        rw [hn_eq, hm]
        have h_q1 : 1 ≤ q + 1 := by omega
        have hm_le_q1 : m ≤ q + 1 := by omega
        -- Rewrite as integer identity then transfer
        have hineq : (q + 1 - m) ^ 2 ≤ (q + 1) ^ 2 + (q - m) ^ 2 := by
          -- (q+1)² + (q-m)² - (q+1-m)² = q² + 2m (in ℤ), which is ≥ 0
          have : (q + 1) ^ 2 + (q - m) ^ 2 ≥ (q + 1 - m) ^ 2 := by
            -- expand in ℤ
            zify [show m ≤ q + 1 from hm_le_q1, show m ≤ q from hm_le_q]
            nlinarith [sq_nonneg ((q : ℤ) - m), sq_nonneg ((q + 1 - m : ℤ))]
          omega
        zify [hineq, show m ≤ q from hm_le_q, show m ≤ q + 1 from hm_le_q1]
        ring
      · -- (q+1)² ≤ n + 2√n. Need 2q+1 ≤ r + 2√n, with r ≥ 2 and √n ≥ q.
        have h1 : ((q + 1 : ℕ) : ℝ) ^ 2 = ((q : ℝ)) ^ 2 + 2 * (q : ℝ) + 1 := by push_cast; ring
        rw [h1]
        -- (q : ℝ)² ≤ n; 2q ≤ 2 √n; 1 ≤ ?
        -- We have q² + r ≤ n + 2√n; r ≥ 2; q ≤ √n.
        -- Need (q² + 2q + 1) ≤ (n + 2√n). Have q² ≤ n, 2q ≤ 2√n, 1 ≤ ... ?
        -- Actually: (n + 2√n) - (q² + 2q + 1) = (n - q²) + (2√n - 2q) - 1 = r + 2(√n - q) - 1
        -- We have r ≥ 2, √n - q ≥ 0, so the difference is ≥ 2 + 0 - 1 = 1 ≥ 0. ✓
        have hr_real : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge_2
        have hr_real' : ((r : ℕ) : ℝ) = (n : ℝ) - ((q : ℝ)) ^ 2 := by
          have : (r : ℝ) = ((n - q^2 : ℕ) : ℝ) := by rw [hr_def]
          have hr_cast : ((n - q^2 : ℕ) : ℝ) = (n : ℝ) - ((q^2 : ℕ) : ℝ) := by
            push_cast [Nat.cast_sub hq_sq]; ring
          push_cast at hr_cast
          linarith [hr_cast]
        linarith
      · -- (q - m)² ≤ q² ≤ n + 2√n
        have hqm_le : q - m ≤ q := Nat.sub_le _ _
        have hqm_real : ((q - m : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqm_le
        have h0 : (0 : ℝ) ≤ ((q - m : ℕ) : ℝ) := Nat.cast_nonneg _
        have : ((q - m : ℕ) : ℝ) ^ 2 ≤ ((q : ℝ)) ^ 2 := by nlinarith
        linarith
      · -- (q+1 - m)² ≤ q² ≤ n + 2√n (since q+1 - m ≤ q when m ≥ 1)
        have hzle : q + 1 - m ≤ q := by omega
        have hz_real : ((q + 1 - m : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hzle
        have h0 : (0 : ℝ) ≤ ((q + 1 - m : ℕ) : ℝ) := Nat.cast_nonneg _
        have : ((q + 1 - m : ℕ) : ℝ) ^ 2 ≤ ((q : ℝ)) ^ 2 := by nlinarith
        linarith

end Erdos1148Weaker

-- Axiom check: should depend only on mathlib's standard three.
#print axioms Erdos1148Weaker.witness_spec
