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
import Erdos699.Tame
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorization.Basic
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

/-- **Tame-residual Case-B closure.** Under the tame regime
`j − i < q ≤ j` (equivalently, `q` divides `C(j, i)` by `tame_prime`),
if the residual block contains at least one factor divisible by `q`
(i.e. `∃ k < j − i, q ∣ (n − i − k)`), then `q` witnesses the gcd.

This closes the "lonely-prime escape" arm of Parthasarathy 2026 §4's
case analysis cleanly: tameness plus a non-empty residual block forces
`q ∣ C(n − i, j − i)`, and the master identity propagates divisibility
to `C(n, j)` via the multiplicity bound `v_q(C(j, i)) ≤ 1` (which
follows from `j < q²`, itself a consequence of tameness via
`q ≥ max(i + 1, j − i + 1) ≥ (j + 2)/2`).

The Bridge sub-case (`v_q(C(n, i)) ≥ 2`) is *not* covered by this
helper — it requires a separate argument and is, at the time of writing,
the same algebraic obstruction as Erdős #699 itself. -/
theorem caseB_split_with_hyp_tame_residual {n i j q : ℕ}
    (hq : Nat.Prime q) (hi_lt_q : i < q) (hq_le_j : q ≤ j)
    (hq_tame_ji : j - i < q) (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (hk : ∃ k, k < j - i ∧ q ∣ (n - i - k)) :
    q ∣ Nat.gcd (n.choose i) (n.choose j) := by
  obtain ⟨k₀, hk₀_lt, hq_dvd_k₀⟩ := hk
  -- Step 1: q ∣ C(n - i, j - i) via the lonely-factor lemma.
  have hq_dvd_Cni : q ∣ (n - i).choose (j - i) :=
    dvd_choose_of_dvd_residual_block hq hq_tame_ji hk₀_lt hq_dvd_k₀
  -- Step 2: tame_prime gives q ∣ C(j, i); j < q² gives v_q(C(j, i)) ≤ 1.
  have hq_dvd_ji : q ∣ j.choose i := tame_prime hq hq_tame_ji hq_le_j hi_lt_q hij
  have hq_ge_2 : 2 ≤ q := hq.two_le
  have h_j_lt_qq : j < q ^ 2 := by
    have h1 : 2 * q ≥ j + 2 := by omega
    have h2 : q * q ≥ 2 * q := Nat.mul_le_mul_right q hq_ge_2
    have h3 : q * q > j := by omega
    simpa [pow_two] using h3
  have h_v_ji_le_1 : (j.choose i).factorization q ≤ 1 :=
    Nat.factorization_choose_le_one h_j_lt_qq
  -- Step 3: master identity ⟹ q² ∣ C(n, j) · C(j, i).
  have h_master : n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) :=
    master_identity hij
  have h_qq_rhs : q ^ 2 ∣ n.choose i * (n - i).choose (j - i) := by
    rw [pow_two]; exact mul_dvd_mul hq_dvd_ni hq_dvd_Cni
  have h_qq_lhs : q ^ 2 ∣ n.choose j * j.choose i := h_master ▸ h_qq_rhs
  -- Step 4: v_q split + bound ⟹ q ∣ C(n, j).
  have h_choose_nj_pos : 0 < n.choose j := Nat.choose_pos hjn
  have h_choose_ji_pos : 0 < j.choose i := Nat.choose_pos hij
  have h_v_prod_ge_2 :
      2 ≤ (n.choose j * j.choose i).factorization q :=
    (hq.pow_dvd_iff_le_factorization
      (Nat.mul_ne_zero h_choose_nj_pos.ne' h_choose_ji_pos.ne')).mp h_qq_lhs
  rw [Nat.factorization_mul h_choose_nj_pos.ne' h_choose_ji_pos.ne'] at h_v_prod_ge_2
  simp only [Finsupp.coe_add, Pi.add_apply] at h_v_prod_ge_2
  have h_v_nj_ge_1 : 1 ≤ (n.choose j).factorization q := by omega
  have hq_dvd_nj : q ∣ n.choose j := by
    have h := (hq.pow_dvd_iff_le_factorization h_choose_nj_pos.ne').mpr h_v_nj_ge_1
    simpa using h
  exact Nat.dvd_gcd hq_dvd_ni hq_dvd_nj

/-- **Strengthened Case-B claim** (the theorem Parthasarathy's case
analysis *actually* proves, in the tame regime). Under the
non-simultaneity hypothesis `¬ StijnObstruction` plus the tame-prime
hypothesis `j − i < q`, the prime `q` witnesses the gcd *except* in the
Bridge sub-case `v_q(C(n, i)) ≥ 2`. The remaining sorry corresponds
precisely to that Bridge case — a strictly smaller open obstruction
than the original (this session, memo `0055`, narrowed the sorry from
the full `q ∣ C(j, i)` arm to its `v_q(C(n, i)) ≥ 2` sub-arm). -/
theorem caseB_split_with_hyp {n i j q : ℕ}
    (hq : Nat.Prime q) (hi_lt_q : i < q) (hq_le_j : q ≤ j)
    (hq_tame_ji : j - i < q) (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (h_not_stijn : ¬ StijnObstruction n i j q) :
    q ∣ Nat.gcd (n.choose i) (n.choose j) := by
  by_cases hji : q ∣ j.choose i
  · -- `q ∣ C(j, i)`: unpack `¬ StijnObstruction` into Bridge vs. lonely-residual.
    by_cases hD : ∀ k, k < j - i → ¬ q ∣ (n - i - k)
    · -- Bridge sub-case: residual block empty, so the failing conjunct is `v_q = 1`.
      -- `¬ StijnObstruction` ∧ `q ∣ C(n, i)` ∧ `q ∣ C(j, i)` ∧ `D = empty residual`
      -- ⟹ `v_q(C(n, i)) ≠ 1`, hence `≥ 2`. This is the same obstruction as
      -- Erdős #699 itself; left as a *narrower* sorry than the original.
      sorry
    · -- Lonely-residual sub-case: ∃ k < j - i, q ∣ (n - i - k). Apply helper.
      push_neg at hD
      exact caseB_split_with_hyp_tame_residual
        hq hi_lt_q hq_le_j hq_tame_ji hij hjn hq_dvd_ni hD
  · -- `q ∤ C(j, i)`: direct from `case_B_alpha`.
    exact case_B_alpha_gcd hq hij hjn hq_dvd_ni hji

end Erdos699
