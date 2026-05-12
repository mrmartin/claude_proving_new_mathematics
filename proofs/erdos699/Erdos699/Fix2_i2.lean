/-
**Fix 2 — the `i = 2` sub-case** of the Pure-Power Dichotomy.

The dichotomy: for any triple `(n, 2, j)`, write `n = k + 2^V · M` with
`k = n mod 2 ∈ {0, 1}`, `V ≥ 1`, `Nat.Coprime M 2`. The `M = 1` case is
closed by `Erdos699.carry_lemma_fo_resolution`. This file attacks the
`M ≥ 2` case, where `M` is odd and `M ≥ 3`.

**Strategy (Lucas's theorem).** Pick an odd prime factor `r ≥ 3` of `M`.
Then:

1. `r ∣ C(n, 2)`: since `r ∣ n − k` and `k ∈ {0, 1}`, `r` divides `n` or
   `n − 1`, hence `r ∣ n(n − 1)`; being odd, `r` is coprime to 2, so
   `r ∣ n(n − 1)/2 = C(n, 2)`.

2. `r ∣ C(n, j)`: by Lucas's theorem, the base-`r` representations of
   `n` and `j` are compared digit-by-digit. The structure
   `n − k = 2^V · M` with `r ∣ M` forces a digit mismatch in most cases
   (the "easy" Sub-case 3a — `j mod r > k` — closes by a direct Lucas
   factor `C(k, j mod r) = 0`).

3. Combining gives `¬ FullyObstructed n 2 j` (witness: prime `r > 2`).

This file ships the foundations (Steps 1 + 2). Steps 3a and 3b are
attacked in subsequent commits.
-/

import Erdos699.Master
import Erdos699.FullyObstructed
import Erdos699.Carry
import Erdos699.Fix2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- **Step 1.** Any `M ≥ 2` coprime to `2` has an odd prime factor `r ≥ 3`. -/
theorem exists_odd_prime_dvd_of_coprime_two {M : ℕ}
    (hM : 2 ≤ M) (hcop : Nat.Coprime M 2) :
    ∃ r, Nat.Prime r ∧ 3 ≤ r ∧ r ∣ M := by
  have h2_ndvd_M : ¬ (2 : ℕ) ∣ M := by
    intro h2
    have hcop' : Nat.Coprime 2 M := hcop.symm
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hcop'
    exact hcop' h2
  have hM_ne_1 : M ≠ 1 := by omega
  have h_prime : Nat.Prime M.minFac := Nat.minFac_prime hM_ne_1
  have h_two_le : 2 ≤ M.minFac := h_prime.two_le
  have h_ne_two : M.minFac ≠ 2 := fun h => h2_ndvd_M (h ▸ M.minFac_dvd)
  exact ⟨M.minFac, h_prime, by omega, M.minFac_dvd⟩

/-- Auxiliary: `2 · C(n, 2) = n · (n - 1)` for `n ≥ 2`. -/
private lemma two_mul_choose_two_eq (n : ℕ) (hn : 2 ≤ n) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  have h2dvd : 2 ∣ n * (n - 1) := by
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · exact Dvd.dvd.mul_right ⟨n / 2, by omega⟩ (n - 1)
    · refine Dvd.dvd.mul_left ⟨(n - 1) / 2, ?_⟩ n
      omega
  exact Nat.mul_div_cancel' h2dvd

/-- **Step 2.** An odd prime `r` dividing `n(n − 1)` divides `C(n, 2)`. -/
theorem odd_prime_dvd_choose_two {r n : ℕ}
    (hr : Nat.Prime r) (hr_odd : r ≠ 2) (hn : 2 ≤ n)
    (hr_dvd_prod : r ∣ n * (n - 1)) :
    r ∣ n.choose 2 := by
  have h_eq : 2 * n.choose 2 = n * (n - 1) := two_mul_choose_two_eq n hn
  have hr_dvd_2C : r ∣ 2 * n.choose 2 := h_eq ▸ hr_dvd_prod
  rcases hr.dvd_mul.mp hr_dvd_2C with h | h
  · -- `r ∣ 2` with `r` prime and `r ≠ 2` is impossible.
    exfalso
    have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have hge : r ≥ 2 := hr.two_le
    have : r = 2 := by omega
    exact hr_odd this
  · exact h

/-- **Step 1 + 2 combined.** Under dichotomy data with `M ≥ 2` and
`i = 2`, there is an odd prime `r ≥ 3` with `r ∣ M` and `r ∣ C(n, 2)`. -/
theorem dichotomy_M_ge_2_witness {n k V M : ℕ}
    (hM : 2 ≤ M) (h_dich : DichotomyData n 2 k V M) :
    ∃ r, Nat.Prime r ∧ 3 ≤ r ∧ r ∣ M ∧ r ∣ n.choose 2 := by
  obtain ⟨hk_def, hVge1, hcop, hnk⟩ := h_dich
  obtain ⟨r, hr_prime, hr_ge_3, hr_dvd_M⟩ :=
    exists_odd_prime_dvd_of_coprime_two hM hcop
  refine ⟨r, hr_prime, hr_ge_3, hr_dvd_M, ?_⟩
  -- `r ∣ M` and `n - k = 2^V * M` ⟹ `r ∣ n - k`.
  have hr_dvd_nk : r ∣ n - k := by
    rw [hnk]; exact Dvd.dvd.mul_left hr_dvd_M _
  -- `k ≤ 1` because `k = n mod 2`.
  have hk_le_1 : k ≤ 1 := by rw [hk_def]; omega
  -- `n ≥ 4`: from `V ≥ 1`, `M ≥ 2`, so `n - k = 2^V · M ≥ 4`, hence `n ≥ 4`.
  have h_nk_ge_4 : n - k ≥ 4 := by
    rw [hnk]
    have h_pow : (2 : ℕ) ^ V ≥ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) hVge1
    have h_pow' : (2 : ℕ) ^ V ≥ 2 := by simpa using h_pow
    calc (2 : ℕ) ^ V * M ≥ 2 * 2 := Nat.mul_le_mul h_pow' hM
      _ = 4 := by norm_num
  have hn_ge : 2 ≤ n := by omega
  -- Split on `k ∈ {0, 1}` to extract `r ∣ n * (n - 1)`.
  have hr_dvd_prod : r ∣ n * (n - 1) := by
    interval_cases k
    · simp at hr_dvd_nk
      exact Dvd.dvd.mul_right hr_dvd_nk _
    · exact Dvd.dvd.mul_left hr_dvd_nk _
  have hr_odd : r ≠ 2 := by omega
  exact odd_prime_dvd_choose_two hr_prime hr_odd hn_ge hr_dvd_prod

/-- **Step 3a (easy Lucas sub-case).** If `r` is an odd prime dividing
`M`, `j mod r > k` (where `k = n mod 2 ∈ {0, 1}`), and `j ≤ n`, then
`r ∣ C(n, j)`.

Proof: Lucas's theorem gives
`C(n, j) ≡ C(n mod r, j mod r) · C(n / r, j / r) (mod r)`. Since `r ∣ M`
and `n − k = 2^V · M`, we have `r ∣ n − k`, so `n mod r = k mod r = k`
(using `k < r`). Then `C(n mod r, j mod r) = C(k, j mod r) = 0`
because `k < j mod r`. So `r ∣ C(n, j)`. -/
theorem dvd_choose_of_dichotomy_digit_zero_mismatch
    {n j k V M r : ℕ}
    (hr_prime : Nat.Prime r) (hr_ge_3 : 3 ≤ r) (hr_dvd_M : r ∣ M)
    (h_dich : DichotomyData n 2 k V M)
    (h_mismatch : k < j % r) :
    r ∣ n.choose j := by
  obtain ⟨hk_def, _hVge1, _hcop, hnk⟩ := h_dich
  haveI : Fact r.Prime := ⟨hr_prime⟩
  -- `k ≤ 1`
  have hk_le_1 : k ≤ 1 := by rw [hk_def]; omega
  have hk_lt_r : k < r := by omega
  -- `n = k + 2^V * M` from `n - k = 2^V * M` and `k ≤ n`.
  have hk_le_n : k ≤ n := by
    rw [hk_def]; exact Nat.mod_le _ _
  have h_n_eq : n = k + 2 ^ V * M := by omega
  -- `r ∣ 2^V * M` (since `r ∣ M`).
  have h_r_dvd_VM : r ∣ 2 ^ V * M := Dvd.dvd.mul_left hr_dvd_M _
  -- `n mod r = k`: rewrite `n = k + r · c` (since `r ∣ 2^V · M`).
  have h_n_mod : n % r = k := by
    rcases h_r_dvd_VM with ⟨c, hc⟩
    rw [h_n_eq, hc, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hk_lt_r
  -- C(k, j mod r) = 0 since k < j mod r.
  have h_choose_zero : Nat.choose (n % r) (j % r) = 0 := by
    rw [h_n_mod]
    exact Nat.choose_eq_zero_of_lt h_mismatch
  -- Lucas: C(n, j) ≡ C(n mod r, j mod r) · C(n / r, j / r) (mod r).
  have hcong : n.choose j ≡
      Nat.choose (n % r) (j % r) * Nat.choose (n / r) (j / r) [MOD r] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rw [h_choose_zero, Nat.zero_mul] at hcong
  exact Nat.modEq_zero_iff_dvd.mp hcong

/-- **Target B main statement, Phase 3 partial.** If `(n, 2, j)` admits
dichotomy data with `M ≥ 2`, the triple is not Fully Obstructed.

Phase 3 closes the easy Lucas sub-case (`j mod r > k`). The exceptional
case (`j mod r ≤ k`), which is a narrow digit-alignment configuration,
is left as `sorry` for Phase 4. -/
theorem pure_power_dichotomy_M_ge_2_i_eq_2 {n j k V M : ℕ}
    (hij : 2 < j) (hjn : j ≤ n / 2) (hM : 2 ≤ M)
    (h_dich : DichotomyData n 2 k V M) :
    ¬ FullyObstructed n 2 j := by
  -- Extract the witness prime `r` with `r ∣ M`, `r ∣ C(n, 2)`.
  obtain ⟨r, hr_prime, hr_ge_3, hr_dvd_M, hr_dvd_Cn2⟩ :=
    dichotomy_M_ge_2_witness hM h_dich
  -- Negate FO: show ¬ (∀ p, prime → 2 < p → p ∣ C(n, 2) → ¬ p ∣ C(n, j))
  intro h_FO
  -- Specialize FO to `r`.
  apply h_FO r hr_prime (by omega : (2 : ℕ) < r) hr_dvd_Cn2
  -- Goal: r ∣ C(n, j). Easy case `j mod r > k`, hard case `j mod r ≤ k`.
  by_cases h_easy : k < j % r
  · -- Easy case (Phase 3): direct Lucas digit-0 mismatch.
    exact dvd_choose_of_dichotomy_digit_zero_mismatch
      hr_prime hr_ge_3 hr_dvd_M h_dich h_easy
  · -- Hard case (Phase 4): narrow digit-alignment configuration.
    push_neg at h_easy
    sorry

end Erdos699
