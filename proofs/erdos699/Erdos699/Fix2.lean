/-
**Fix 2 attempt: Pure-Power Dichotomy without the gap.**

All 9 known Fully-Obstructed triples for Erdős #699 satisfy
`n - (n mod i) = i^V` with `M = 1` (Parthasarathy 2026 supplement S2).
The Carry Lemma settles them algebraically.

The remaining open question — for both the Parthasarathy paper and any
future attack — is whether `M ≥ 2` triples can be FO. Parthasarathy's
supplement S2.3 *attempts* to prove `M ≥ 2 ⇒ not FO` by base-`i`
subordinate analysis, but Bloom declared the proof invalid: the
analysis depends on the same Cofactor Escape that StijnC's example
refutes.

This file states the key sub-lemma. Closing it (combined with the M=1
case in `Erdos699/Carry.lean`) would close the FO residual of
Erdős #699 **unconditionally**. Combined with Case A and the
algebraic Case B sub-cases (B-α / B-β-i / Bridge), this closes
`erdos_699_main`.

The strategy below leaves the main statement `sorry` after one
attempted tactic angle (sub-case on the prime factorisation of `M`).
A genuine proof requires deeper base-`i` Kummer carry analysis than
fits in a session-scale budget.
-/

import Erdos699.FullyObstructed
import Erdos699.Carry
import Erdos699.CaseB
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- The *Pure-Power-Dichotomy data* for a triple `(n, i)`:
`n = k + i^V · M` with `k < i` (`k = n mod i`), `V ≥ 1`,
`Nat.Coprime M i`.

The Parthasarathy supplement names `V = v_i(n - k)` and observes that
all known FO triples have `M = 1`. -/
def DichotomyData (n i : ℕ) (k V M : ℕ) : Prop :=
  k = n % i ∧ V ≥ 1 ∧ Nat.Coprime M i ∧ n - k = i ^ V * M

/-- **Fix 2 goal**: if `(n, i, j)` admits `DichotomyData` with `M ≥ 2`,
the triple is not Fully Obstructed.

This is the key sub-lemma. Closing it (together with the `M = 1` case
already proved by `carry_lemma_fo_resolution`) would close the FO
residual of Erdős #699 unconditionally.

The proof should proceed by sub-case on the prime factorisation of `M`:

* **(a)** If `M` has a prime factor `r > i`: by the master identity
  (`Erdos699.master_identity`), `r ∣ C(n, j)` whenever the base-`r`
  expansion of `j` has a non-zero digit above the `i^V`-position. For
  this to fail we'd need a delicate alignment of digits between `n`
  and `j` in base `r`; the FO Size Constraint (Parthasarathy §5.2)
  rules this out for sufficiently large `n`.
* **(b)** If `i = 2`: `M` is odd and `M ≥ 3`, so case (a) applies.
  Settles `i = 2` completely.
* **(c)** If `M` is prime: since case (a) covers `M > i`, the
  remaining case is `M ≤ i` and `M` prime — finite per `(i, j)`.
* **(d)** Otherwise (`M` is `(i-1)`-smooth): this is the residual
  case. Parthasarathy's supplement S2.3 *defers* to Baker–Wüstholz
  + computation; doing it unconditionally requires a sharper Kummer
  analysis that this attack cannot supply in a session-scale budget. -/
theorem pure_power_dichotomy_M_ge_2 {n i j k V M : ℕ}
    (hi : 2 ≤ i)
    (hij : i < j) (hjn : j ≤ n / 2)
    (hM : 2 ≤ M)
    (h_dich : DichotomyData n i k V M) :
    ¬ FullyObstructed n i j := by
  sorry

/-- Combined statement: every Erdős #699 triple `(n, i, j)` with
`i ≥ 2` admits *some* dichotomy data, and if `M = 1` we win via
the Carry Lemma; if `M ≥ 2` we win via
`pure_power_dichotomy_M_ge_2`. This packaging makes the dependence
of the full theorem on the open sub-lemma explicit.

The proof is `sorry` because `pure_power_dichotomy_M_ge_2` is `sorry`. -/
theorem dichotomy_closes_FO_residual {n i j : ℕ}
    (hi : 2 ≤ i)
    (hij : i < j) (hjn : j ≤ n / 2) :
    ¬ FullyObstructed n i j ∨ ∃ p, Nat.Prime p ∧ i ≤ p ∧
      p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  sorry

end Erdos699
