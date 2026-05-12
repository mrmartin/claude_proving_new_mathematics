/-
**Case B framework for Erdős #699** (Parthasarathy 2026 §4).

In Case B, the i-product `P = n(n-1)···(n-i+1)` is `j`-smooth, so
Sylvester-Schur supplies a prime `q ∈ (i, j]` dividing `P`. The paper
splits on whether `q | C(j, i)`:

  * **B-α**: `q ∤ C(j, i)` ⟹ master identity gives `q ∣ C(n, j)` directly.
  * **B-β**: `q | C(j, i)` ⟹ further case split on tameness, loneliness,
                              and `v_q(n - k_q)`.
  * **B-γ**: `q | C(j, i)` and `q ≤ j - i` ⟹ deferred; rely on another
                              witness in §5.

The Case-B *exhaustiveness* (every tame `q` witnesses) is what
Parthasarathy's §4 implicitly claims and what StijnC's 2026-05-01
comment refutes. We encode both forms below: a *naive* one
(`caseB_split_naive`) — the buggy claim — and a *strengthened* one
(`caseB_split_with_hyp`) with an explicit non-simultaneity hypothesis
that makes the gap machine-checkable.
-/

import Erdos699.Master
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- **Case B-α** (Parthasarathy §4). When the tame prime `q ∈ (i, j]`
divides `C(n, i)` but does **not** divide `C(j, i)`, the master identity
forces `q ∣ C(n, j)`. -/
theorem case_B_alpha {n i j q : ℕ} (hq : Nat.Prime q)
    (hij : i ≤ j) (_hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (hq_ndvd_ji : ¬ (q ∣ j.choose i)) :
    q ∣ n.choose j := by
  have hmi : n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) :=
    master_identity hij
  have hq_dvd_rhs : q ∣ n.choose i * (n - i).choose (j - i) :=
    dvd_mul_of_dvd_left hq_dvd_ni _
  have hq_dvd_lhs : q ∣ n.choose j * j.choose i := hmi ▸ hq_dvd_rhs
  exact (hq.dvd_mul.mp hq_dvd_lhs).resolve_right hq_ndvd_ji

/-- gcd-witness packaging of `case_B_alpha`. -/
theorem case_B_alpha_gcd {n i j q : ℕ} (hq : Nat.Prime q)
    (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (hq_ndvd_ji : ¬ (q ∣ j.choose i)) :
    q ∣ Nat.gcd (n.choose i) (n.choose j) :=
  Nat.dvd_gcd hq_dvd_ni (case_B_alpha hq hij hjn hq_dvd_ni hq_ndvd_ji)

/-- **The naive Case-B claim** (Parthasarathy §4, implicit). Every
tame prime `q ∈ (i, j]` dividing `C(n, i)` witnesses `gcd(C(n, i), C(n, j))`.

**This is the buggy claim.** StijnC's 2026-05-01 comment exhibits a
configuration in which:

  * `q ∣ C(j, i)` (so case B-α does not apply),
  * `q ∣ C(n, i)` with `v_q = 1` (so the Prime-Power Bridge Lemma
    does not apply — it needs `v ≥ 2`),
  * the `(j - i)`-block has no multiple of `q` (so neither the Master
    Identity for Case B-β-i nor the lonely-prime Bridge applies on
    `q` itself),
  * none of the three Cofactor-Escape routes is guaranteed to fire.

In that configuration, `q ∤ C(n, j)` (via the master-identity
valuation form `v_q(C(n, j)) = 1 + 0 - 1 = 0`), so `q` is *not* a
gcd witness. The Stijn example in `Erdos699/Stijn.lean` constructs an
explicit instance.

We leave the theorem `sorry`-bodied to make any future fix face the
obstruction directly: a closure of `caseB_split_naive` must either
strengthen the hypothesis (which is the route taken by
`caseB_split_with_hyp`) or supply an alternative witness via a
fourth Cofactor-Escape route (`Erdos699/Fix2.lean`). -/
theorem caseB_split_naive {n i j q : ℕ}
    (hq : Nat.Prime q) (hi_lt_q : i < q) (hq_le_j : q ≤ j)
    (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i) :
    q ∣ Nat.gcd (n.choose i) (n.choose j) := by
  sorry

/-- The "simultaneity signature" of Stijn's example: a tame prime `q`
divides both `C(n, i)` and `C(j, i)`, the `(j - i)`-block has no
multiple of `q`, and `v_q(C(n, i)) = 1`. Under this signature, the
naive Case-B split fails: none of the four standard escape routes
fires. -/
def StijnObstruction (n i j q : ℕ) : Prop :=
  q ∣ n.choose i ∧
  q ∣ j.choose i ∧
  Nat.factorization (n.choose i) q = 1 ∧
  ∀ k, k < j - i → ¬ q ∣ (n - i - k)

/-- **Strengthened Case-B claim** (the theorem Parthasarathy's case
analysis *actually* proves). Under the non-simultaneity hypothesis
`¬ StijnObstruction`, the tame prime `q` does witness the gcd.

Closing this `sorry` is plausible — it requires a careful case split
on whether `q ∤ C(j, i)` (Case B-α, already proved) or `q | C(j, i)`
with non-Stijn structure (Bridge or Cofactor-Escape routes 1–3). The
case `StijnObstruction n i j q` is precisely where the naive claim
fails and where Fix 1 / Fix 2 are needed. -/
theorem caseB_split_with_hyp {n i j q : ℕ}
    (hq : Nat.Prime q) (hi_lt_q : i < q) (hq_le_j : q ≤ j)
    (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (h_not_stijn : ¬ StijnObstruction n i j q) :
    q ∣ Nat.gcd (n.choose i) (n.choose j) := by
  sorry

end Erdos699
