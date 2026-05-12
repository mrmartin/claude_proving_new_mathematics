/-
**Absorption identity + `i = 1` case** (Parthasarathy §6).

The absorption identity is `j · C(n, j) = n · C(n-1, j-1)` — directly
available in Mathlib as `Nat.succ_mul_choose_eq`. We re-export under our
namespace and use it to give the `i = 1` algebraic resolution.

When `i = 1`, we want a prime `p ∣ n` to witness `gcd(C(n,1), C(n,j))`.
The witness is *any* prime divisor of `n` that does not divide `j` (since
`C(n,1) = n`).
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- Absorption identity: `j · C(n, j) = n · C(n-1, j-1)`. -/
theorem absorption {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    j * n.choose j = n * (n - 1).choose (j - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    cases j with
    | zero => omega
    | succ j =>
      have h := Nat.add_one_mul_choose_eq n j
      show (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j
      linarith

/-- If a prime `p` divides `n` but not `j`, then `p ∣ C(n, j)`.
This is the key step in the `i = 1` case of Erdős #699 (Parthasarathy
§6 part (a)). -/
theorem dvd_choose_of_dvd_n_not_dvd_j {n j p : ℕ} (hp : Nat.Prime p)
    (hpn : p ∣ n) (hpj : ¬ (p ∣ j)) (hj : 1 ≤ j) (hjn : j ≤ n) :
    p ∣ n.choose j := by
  have hab := absorption hj hjn
  have hdvd : p ∣ j * n.choose j := by
    rw [hab]; exact dvd_mul_of_dvd_left hpn _
  exact (hp.dvd_mul.mp hdvd).resolve_left hpj

end Erdos699
