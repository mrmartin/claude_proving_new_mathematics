/-
**Carry Lemma** (Parthasarathy 2026 supplement, S1).

If `p` is prime, `V ≥ 2`, and `n = r + p^V` with `0 ≤ r < p`, then
`p ∣ C(n, j)` for every `j` with `p ≤ j < p^V`. The proof works via
`Nat.add_choose_eq` (Vandermonde antidiagonal) plus
`Nat.Prime.dvd_choose_pow`.

This lemma settles the `M = 1` Fully-Obstructed triples
algebraically — all 9 known FO triples lie on this `n = r + p^V`
structure.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace Erdos699

open Nat Finset

/-- Carry Lemma (Parthasarathy supplement S1). For `p` prime, `V ≥ 2`,
`0 ≤ r < p`, and `p ≤ j < p^V`, the prime `p` divides `(r + p^V).choose j`. -/
theorem carry_lemma {p V r j : ℕ} (hp : Nat.Prime p) (_hV : 2 ≤ V)
    (hr : r < p) (hj_lb : p ≤ j) (hj_ub : j < p ^ V) :
    p ∣ (r + p ^ V).choose j := by
  rw [Nat.add_choose_eq]
  apply Finset.dvd_sum
  intro ⟨s, t⟩ hst
  rw [Finset.mem_antidiagonal] at hst
  by_cases hs : r < s
  · have : r.choose s = 0 := Nat.choose_eq_zero_of_lt hs
    simp only [this, zero_mul, dvd_zero]
  · push_neg at hs
    apply dvd_mul_of_dvd_right
    have ht_ne_zero : t ≠ 0 := by omega
    have ht_ne_pow : t ≠ p ^ V := by omega
    exact hp.dvd_choose_pow ht_ne_zero ht_ne_pow

/-- Specialisation of `carry_lemma` to `j = p`. -/
theorem carry_lemma_at_p {p V r : ℕ} (hp : Nat.Prime p) (hV : 2 ≤ V)
    (hr : r < p) :
    p ∣ (r + p ^ V).choose p := by
  apply carry_lemma hp hV hr le_rfl
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ V := Nat.pow_lt_pow_right (Nat.Prime.one_lt hp) (by omega)

/-- Carry-Lemma resolution of `M = 1` FO triples (Parthasarathy
supplement S2). When `n = r + p^V` with `2 j ≤ n`, the prime `p`
witnesses `gcd(C(n, p), C(n, j))`. -/
theorem carry_lemma_fo_resolution {p V r j : ℕ} (hp : Nat.Prime p)
    (hV : 2 ≤ V) (hr : r < p) (hj_lb : p ≤ j)
    (hj_half : 2 * j ≤ r + p ^ V) :
    p ∣ Nat.gcd ((r + p ^ V).choose p) ((r + p ^ V).choose j) := by
  apply Nat.dvd_gcd
  · exact carry_lemma_at_p hp hV hr
  · apply carry_lemma hp hV hr hj_lb
    have hpV : p ≤ p ^ V := Nat.le_self_pow (by omega) p
    omega

end Erdos699
