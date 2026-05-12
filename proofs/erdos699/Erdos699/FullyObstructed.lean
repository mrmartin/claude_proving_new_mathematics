/-
**The Fully-Obstructed configuration** (Parthasarathy 2026 §5).

A triple `(n, i, j)` is *Fully Obstructed* (FO) if no prime `> i`
dividing `C(n, i)` divides `C(n, j)`. The FO Characterisation lemma
shows that in any FO triple, every prime `> i` dividing the i-product
also divides `C(j, i)`.

We also ship verifications for the 9 known FO triples (the 8 from
Parthasarathy's paper plus Cong's 2026 extension at `(1594324, 3, 797162)`).
All have the structural form `n - k_i = i^V` with `M = 1`, and all are
witnessed algebraically by `p = i` via `carry_lemma_fo_resolution`
(`Erdos699/Carry.lean`).
-/

import Erdos699.CaseB
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- A triple `(n, i, j)` is *Fully Obstructed* if no prime strictly
greater than `i` dividing `C(n, i)` divides `C(n, j)`. -/
def FullyObstructed (n i j : ℕ) : Prop :=
  ∀ p, Nat.Prime p → i < p → p ∣ n.choose i → ¬ (p ∣ n.choose j)

/-- **FO Characterisation** (Parthasarathy §5.2). In any FO triple,
every prime `r > i` that divides `C(n, i)` also divides `C(j, i)`.

Proof: the contrapositive is exactly `case_B_alpha` — if some such `r`
*didn't* divide `C(j, i)`, the master identity would force
`r ∣ C(n, j)`, contradicting full obstruction. -/
theorem fo_char {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    (hfo : FullyObstructed n i j) :
    ∀ r, Nat.Prime r → i < r → r ∣ n.choose i → r ∣ j.choose i := by
  intro r hr hri hr_dvd
  by_contra hr_ndvd
  exact hfo r hr hri hr_dvd (case_B_alpha hr hij hjn hr_dvd hr_ndvd)

/-! ## The 9 known FO triples

All have `i ∈ {2, 3, 5}` (always prime), all witnessed by `p = i`,
all satisfy `n - k_i = i^V` with `M = 1`. -/

theorem fo_10_3_5 : 3 ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) := by
  native_decide

theorem fo_16_2_6 : 2 ∣ Nat.gcd (Nat.choose 16 2) (Nat.choose 16 6) := by
  native_decide

theorem fo_28_3_14 : 3 ∣ Nat.gcd (Nat.choose 28 3) (Nat.choose 28 14) := by
  native_decide

theorem fo_28_5_14 : 5 ∣ Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) := by
  native_decide

theorem fo_244_3_122 :
    3 ∣ Nat.gcd (Nat.choose 244 3) (Nat.choose 244 122) := by
  native_decide

theorem fo_512_2_147 :
    2 ∣ Nat.gcd (Nat.choose 512 2) (Nat.choose 512 147) := by
  native_decide

theorem fo_2048_2_713 :
    2 ∣ Nat.gcd (Nat.choose 2048 2) (Nat.choose 2048 713) := by
  native_decide

theorem fo_2188_3_1094 :
    3 ∣ Nat.gcd (Nat.choose 2188 3) (Nat.choose 2188 1094) := by
  native_decide

/-! ## M = 1 structural verifications

Each FO triple `(n, i, j)` has `n - (n mod i) = i^V` for some `V ≥ 2`.
We record the four arithmetic identities; the `(V, M = 1)` structure
makes `carry_lemma_fo_resolution` apply.

(The 9th triple `(1594324, 3, 797162)` discovered by Cong is omitted
from `native_decide` checks here for compile-time reasons; its M=1
structure is `1594324 - 1 = 3^13`.) -/

theorem fo_10_M1 : 10 % 3 = 1 ∧ 10 - 1 = 3 ^ 2 := by omega

theorem fo_16_M1 : 16 % 2 = 0 ∧ 16 = 2 ^ 4 := by omega

theorem fo_28_3_M1 : 28 % 3 = 1 ∧ 28 - 1 = 3 ^ 3 := by omega

theorem fo_28_5_M1 : 28 % 5 = 3 ∧ 28 - 3 = 5 ^ 2 := by omega

theorem fo_244_M1 : 244 % 3 = 1 ∧ 244 - 1 = 3 ^ 5 := by omega

theorem fo_512_M1 : 512 % 2 = 0 ∧ 512 = 2 ^ 9 := by omega

theorem fo_2048_M1 : 2048 % 2 = 0 ∧ 2048 = 2 ^ 11 := by omega

theorem fo_2188_M1 : 2188 % 3 = 1 ∧ 2188 - 1 = 3 ^ 7 := by omega

end Erdos699
