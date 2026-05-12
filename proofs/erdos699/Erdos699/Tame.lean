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
