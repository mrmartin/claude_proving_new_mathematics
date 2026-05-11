/-
**Caveat.** This file proves `Erdos1054.f_undefined_at_2 : f 2 = 0`. That is
a *Lean-encoding sanity check*, not a solution to Erdős Problem 1054. The
real problem (https://www.erdosproblems.com/1054) is the OPEN question

  "Is it true that f(n) = o(n), or is the lim sup f(n)/n = ∞?"

The function `f` is defined upstream as `if (∃ m k ≥ 1, …) then Nat.find h
else 0`. The `else 0` is a junk value when no valid `m, k` exists.
erdosproblems.com itself notes that `f` is undefined at `n = 2` and `n = 5`,
so the upstream `textbook`-tagged sanity check `f 2 = 0` simply verifies
that the `else` branch fires. It is *not* progress on the asymptotic
question. See memo `memory/0020-proof-erdos-1054-f2.md` for the full
discussion.

Mathematical argument for `f 2 = 0`: the sum `∑_{i<k} nth (· ∈ divisors m) i`
is never `2`.

* For `m = 0`: all `Nat.nth` values are `0`, sum is `0`.
* For `m = 1`: only divisor is `1`, sum is `1` (for any `k ≥ 1`).
* For `m ≥ 2`, `k = 1`: sum is `nth 0 = 1`.
* For `m ≥ 2`, `k ≥ 2`: sum ≥ `nth 0 + nth 1 ≥ 1 + 2 = 3`.

In all cases, sum ≠ 2, so the existential fails and `f 2 = 0`.
-/

import Mathlib

namespace Erdos1054

open Classical Filter Asymptotics
open scoped Finset

/-- Upstream `Erdos1054.f`. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : ∃ᵉ (m) (k ≥ 1), n = ∑ i < k, Nat.nth (· ∈ m.divisors) i then
    Nat.find h
  else 0

/-! ## Helper lemmas -/

private lemma divisors_finite (m : ℕ) : Set.Finite (setOf (· ∈ Nat.divisors m)) :=
  (Nat.divisors m).finite_toSet

private lemma divisors_toFinset_card (m : ℕ) :
    #(divisors_finite m).toFinset = #(Nat.divisors m) := by
  rw [show (divisors_finite m).toFinset = Nat.divisors m from
    Finset.finite_toSet_toFinset _]

/-- `Nat.nth p` at indices beyond the divisor count is `0`. -/
private lemma nth_divisors_of_card_le {m i : ℕ} (h : #(Nat.divisors m) ≤ i) :
    Nat.nth (· ∈ Nat.divisors m) i = 0 := by
  rw [Nat.nth_of_card_le (divisors_finite m)]
  rwa [divisors_toFinset_card]

/-- `m = 0`: all nths vanish. -/
private lemma nth_divisors_zero (i : ℕ) :
    Nat.nth (· ∈ Nat.divisors 0) i = 0 := by
  apply nth_divisors_of_card_le; simp [Nat.divisors_zero]

/-- `m ≥ 1`: smallest divisor is `1`. -/
private lemma nth_divisors_pos_zero {m : ℕ} (hm : 1 ≤ m) :
    Nat.nth (· ∈ Nat.divisors m) 0 = 1 := by
  rw [Nat.nth_zero]
  have h1 : (1 : ℕ) ∈ setOf (· ∈ Nat.divisors m) := by
    simp [Nat.mem_divisors]; omega
  apply le_antisymm (Nat.sInf_le h1)
  refine le_csInf ⟨1, h1⟩ ?_
  intro x hx
  simp only [Set.mem_setOf_eq, Nat.mem_divisors] at hx
  rcases Nat.eq_zero_or_pos x with rfl | hxp
  · exact absurd (Nat.zero_dvd.mp hx.1) hx.2
  · exact hxp

/-- For `m ≥ 2`, `#(Nat.divisors m) ≥ 2` since `1, m ∈ divisors m` and `1 ≠ m`. -/
private lemma card_divisors_ge_two {m : ℕ} (hm : 2 ≤ m) : 2 ≤ #(Nat.divisors m) := by
  have h1 : (1 : ℕ) ∈ Nat.divisors m := by simp [Nat.mem_divisors]; omega
  have hm_mem : m ∈ Nat.divisors m := by simp [Nat.mem_divisors]; omega
  have hne : (1 : ℕ) ≠ m := by omega
  calc 2 = #({1, m} : Finset ℕ) := by
          rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    _ ≤ #(Nat.divisors m) := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption

/-- For `m ≥ 2`, `nth 1 ≥ 2` (strictly greater than `nth 0 = 1`, and `∈ divisors m`). -/
private lemma nth_divisors_ge_two_one {m : ℕ} (hm : 2 ≤ m) :
    2 ≤ Nat.nth (· ∈ Nat.divisors m) 1 := by
  have hfin := divisors_finite m
  have hcard1 : 1 < #hfin.toFinset := by
    rw [divisors_toFinset_card]; exact card_divisors_ge_two hm
  have h_mem : Nat.nth (· ∈ Nat.divisors m) 1 ∈ Nat.divisors m :=
    Nat.nth_mem_of_lt_card hfin hcard1
  have h_ne_zero : Nat.nth (· ∈ Nat.divisors m) 1 ≠ 0 := by
    intro h; rw [h] at h_mem; simp [Nat.mem_divisors] at h_mem
  have h_lt : Nat.nth (· ∈ Nat.divisors m) 0 < Nat.nth (· ∈ Nat.divisors m) 1 :=
    Nat.nth_lt_nth_of_lt_card hfin (by omega) hcard1
  rw [nth_divisors_pos_zero (by omega)] at h_lt
  omega

/-! ## Main theorem -/

theorem f_undefined_at_2 : f 2 = 0 := by
  unfold f
  apply dif_neg
  rintro ⟨m, k, hk, hsum⟩
  -- Convert `∑ i < k, ...` (which parses as `Finset.Iio k`) to `Finset.range k`.
  simp only [Nat.Iio_eq_range] at hsum
  -- Case-split on m
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · -- m = 0
      simp only [nth_divisors_zero, Finset.sum_const_zero] at hsum
      norm_num at hsum
    · -- m = 1: divisors 1 = {1}; nth 0 = 1, nth (i+1) = 0
      have h_tail : ∀ i, Nat.nth (· ∈ Nat.divisors 1) (i + 1) = 0 := fun i => by
        apply nth_divisors_of_card_le
        rw [show #(Nat.divisors 1) = 1 from by decide]
        omega
      -- Sum = nth 0 + Σ nth (i+1) = 1 + 0 = 1
      have h_sum_one : ∑ i ∈ Finset.range k, Nat.nth (· ∈ Nat.divisors 1) i = 1 := by
        rcases k with _ | k'
        · omega
        · rw [Finset.sum_range_succ', nth_divisors_pos_zero (by omega : (1 : ℕ) ≥ 1)]
          have : ∑ i ∈ Finset.range k', Nat.nth (· ∈ Nat.divisors 1) (i + 1) = 0 :=
            Finset.sum_eq_zero (fun i _ => h_tail i)
          omega
      rw [h_sum_one] at hsum
      omega
  · -- m ≥ 2
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · -- k = 1
      interval_cases k
      simp only [Finset.sum_range_one] at hsum
      rw [nth_divisors_pos_zero (by omega : m ≥ 1)] at hsum
      omega
    · -- k ≥ 2: peel off first two terms
      -- sum ≥ nth 0 + nth 1 ≥ 1 + 2 = 3
      have h_split : ∑ i ∈ Finset.range k, Nat.nth (· ∈ Nat.divisors m) i ≥
          Nat.nth (· ∈ Nat.divisors m) 0 + Nat.nth (· ∈ Nat.divisors m) 1 := by
        have hkk : Finset.range 2 ⊆ Finset.range k :=
          Finset.range_subset_range.mpr hk2
        calc Nat.nth (· ∈ Nat.divisors m) 0 + Nat.nth (· ∈ Nat.divisors m) 1
            = ∑ i ∈ Finset.range 2, Nat.nth (· ∈ Nat.divisors m) i := by
              rw [Finset.sum_range_succ, Finset.sum_range_one]
          _ ≤ ∑ i ∈ Finset.range k, Nat.nth (· ∈ Nat.divisors m) i :=
              Finset.sum_le_sum_of_subset_of_nonneg hkk (fun _ _ _ => Nat.zero_le _)
      rw [nth_divisors_pos_zero (by omega : m ≥ 1)] at h_split
      have h1 := nth_divisors_ge_two_one hm
      omega

end Erdos1054
