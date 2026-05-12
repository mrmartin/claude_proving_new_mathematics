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

/-- **The naive Case-B claim** (Parthasarathy 2026 §4, implicit).
Every tame prime `q ∈ (i, j]` dividing `C(n, i)` witnesses
`gcd(C(n, i), C(n, j))`.

We package it as a `Prop` rather than a `theorem` because — as
StijnC pointed out on 2026-05-01 — it is **provably false** (see
`caseB_split_naive_refuted` below). The Stijn-spirit instance
`(n, i, j, q) = (10, 3, 5, 5)` satisfies every hypothesis but
violates the conclusion: `5 ∣ C(10, 3) = 120` and `5 ∤ C(10, 5) = 252`,
so `5 ∤ gcd(120, 252) = 12`. -/
def CaseBSplitNaive : Prop :=
  ∀ {n i j q : ℕ}, Nat.Prime q → i < q → q ≤ j → i ≤ j → j ≤ n →
    q ∣ n.choose i → q ∣ Nat.gcd (n.choose i) (n.choose j)

/-- **The bug is real, machine-checked.** Parthasarathy's implicit
Case-B exhaustiveness claim is refuted by the spirit instance
`(n, i, j, q) = (10, 3, 5, 5)`. The instance also coincides with the
known FO triple `(10, 3, 5)` — recall `gcd(C(10, 3), C(10, 5)) =
gcd(120, 252) = 12 = 2² · 3`, so `3` *does* witness Erdős #699 at
this triple, just not the tame prime `5`. The point of the refutation
is that **Case B's argument cannot rely on the tame prime alone**;
the witness must come from elsewhere (e.g. the Carry Lemma supplies
`p = 3` here via `n − 1 = 3²`). -/
theorem caseB_split_naive_refuted : ¬ CaseBSplitNaive := by
  intro H
  have h5_dvd : (5 : ℕ) ∣ Nat.choose 10 3 := by native_decide
  have h := H (n := 10) (i := 3) (j := 5) (q := 5)
              (by decide) (by decide) (by decide)
              (by decide) (by decide) h5_dvd
  -- `h : 5 ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5)`
  -- But `Nat.gcd 120 252 = 12` and `5 ∤ 12`.
  revert h
  native_decide

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
  -- Split on whether `q` divides `C(j, i)`. The `q ∤ C(j, i)` arm is
  -- Case B-α (already proved). The `q ∣ C(j, i)` arm requires Bridge /
  -- Cofactor Escape — left as `sorry`.
  by_cases hji : q ∣ j.choose i
  · -- `q ∣ C(j, i)`: deferred to Bridge / Cofactor Escape (open).
    -- Under `h_not_stijn` plus `q ∣ C(n, i)` plus `q ∣ C(j, i)`, the
    -- `StijnObstruction` reduces to: either `factorization _ q ≠ 1`
    -- (Bridge case, `v ≥ 2`) or `∃ k, q ∣ (n - i - k)` (lonely-prime
    -- escape). Neither is formalised here.
    sorry
  · -- `q ∤ C(j, i)`: direct from `case_B_alpha`.
    exact case_B_alpha_gcd hq hij hjn hq_dvd_ni hji

end Erdos699
