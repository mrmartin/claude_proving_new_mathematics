/-
**Tame-prime lemmas** (Parthasarathy §2.5–2.6).

A prime `q` is *tame* (with respect to `i, j`) if `q ∈ (j - i, j]` and
`q > i`. Tame primes always divide `C(j, i)` (because `q | j!` but `q`
divides neither `i!` nor `(j-i)!`).
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- A prime `q` with `m < q` does not divide `m!`. -/
theorem prime_not_dvd_factorial {q m : ℕ} (hq : Nat.Prime q)
    (hm : m < q) : ¬ (q ∣ m.factorial) := by
  induction m with
  | zero =>
    rw [factorial_zero]
    exact hq.not_dvd_one
  | succ k ih =>
    intro h
    rw [Nat.factorial_succ] at h
    rcases hq.dvd_mul.mp h with h1 | h1
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · exact ih (by omega) h1

/-- **Lonely-factor lemma.** If `q` is a prime with `m < q`, and `q`
divides one of the factors `(n - k)` for some `k < m`, then
`q ∣ n.choose m`.

This is the residual-block analogue of `tame_prime`: a single divisibility
in the descending-factorial expansion of `C(n, m)` propagates to the
binomial coefficient itself, because `q` is coprime to `m!` (the
denominator), so the multiplicity transfers cleanly. -/
theorem dvd_choose_of_dvd_residual_block {q n m : ℕ}
    (hq : Nat.Prime q) (hqm : m < q)
    {k : ℕ} (hk : k < m) (hdvd : q ∣ n - k) :
    q ∣ n.choose m := by
  -- Step 1: q ∣ n.descFactorial (k+1) from the recurrence.
  have h_succ : q ∣ n.descFactorial (k + 1) := by
    rw [Nat.descFactorial_succ]
    exact Dvd.dvd.mul_right hdvd _
  -- Step 2: n.descFactorial (k+1) ∣ n.descFactorial m since k+1 ≤ m.
  have h_split :
      (n - (k + 1)).descFactorial (m - (k + 1)) * n.descFactorial (k + 1)
        = n.descFactorial m :=
    Nat.descFactorial_mul_descFactorial (Nat.succ_le_of_lt hk)
  have h_desc : q ∣ n.descFactorial m :=
    h_split ▸ Dvd.dvd.mul_left h_succ _
  -- Step 3: descFactorial = m! * choose, and q ∤ m! (m < q), so q ∣ choose.
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h_desc
  have h_q_ndvd_fac : ¬ q ∣ m.factorial := prime_not_dvd_factorial hq hqm
  exact (hq.dvd_mul.mp h_desc).resolve_left h_q_ndvd_fac

/-- Tame-Prime Lemma (Parthasarathy §2.5). Every prime `q ∈ (j - i, j]`
with `q > i` divides `C(j, i)`. -/
theorem tame_prime {q i j : ℕ} (hq : Nat.Prime q)
    (hq_gt_ji : j - i < q) (hq_le_j : q ≤ j)
    (hq_gt_i : i < q) (hij : i ≤ j) :
    q ∣ j.choose i := by
  have hq_dvd_jfac : q ∣ j.factorial := dvd_factorial hq.pos hq_le_j
  have hq_ndvd_ifac : ¬ (q ∣ i.factorial) :=
    prime_not_dvd_factorial hq hq_gt_i
  have hq_ndvd_jifac : ¬ (q ∣ (j - i).factorial) :=
    prime_not_dvd_factorial hq hq_gt_ji
  have hfac := Nat.choose_mul_factorial_mul_factorial hij
  have hqdvd : q ∣ j.choose i * i.factorial * (j - i).factorial := by
    rw [hfac]; exact hq_dvd_jfac
  have hqdvd2 : q ∣ j.choose i * (i.factorial * (j - i).factorial) := by
    rwa [mul_assoc] at hqdvd
  rcases hq.dvd_mul.mp hqdvd2 with h | h
  · exact h
  · exfalso
    rcases hq.dvd_mul.mp h with h2 | h2
    · exact hq_ndvd_ifac h2
    · exact hq_ndvd_jifac h2

end Erdos699
