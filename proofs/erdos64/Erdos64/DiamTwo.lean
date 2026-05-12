/-
**Track A3 setup: diameter-2 case (Carr 2026).**

Theorem (Carr 2026, `arXiv:2508.19302`, Theorem 1.1): every graph
with `diam(G) = 2` and `δ(G) ≥ 3` contains a cycle of length 4 or 8.

Carr's proof is a ~12-page case analysis. This module ships:

* `exists_two_other_neighbours`: from `δ ≥ 3` and one edge `v₁ v₂`,
  extract two other neighbours of `v₁` distinct from `v₂` (a setup
  lemma used by every case of Carr's argument).
* `carr2026_diam_two_minDegree_three`: the theorem **statement** in
  the right shape for use in the eventual upstream bridge. The proof
  body is `sorry` — the full case analysis (Cases 1, 2A, 2B, 2C of
  the paper) is queued in memo 0037 with a per-claim line budget.

Discharging the trivial "two distinct shared neighbours ⇒ `C₄`" case
needed careful `cons_isCycle_iff` manipulation in a generic-vertex
setting; deferred until we have a small helper lemma library for
explicit 4-cycle construction without `decide`. Tracked in memo 0037
as item *A3.0*.
-/

import Erdos64.Basic
import Erdos64.CycleHelpers

namespace Erdos64

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For any edge `v₁ v₂` in a `δ ≥ 3` graph, there are at least two other
neighbours of `v₁` (distinct from `v₂` and from each other). -/
theorem exists_two_other_neighbours
    (hδ : 3 ≤ G.minDegree) {v₁ v₂ : V} (hadj : G.Adj v₁ v₂) :
    ∃ v₃ v₄ : V, v₃ ≠ v₄ ∧ v₃ ≠ v₂ ∧ v₄ ≠ v₂ ∧ G.Adj v₁ v₃ ∧ G.Adj v₁ v₄ := by
  have hdeg : 3 ≤ G.degree v₁ := le_trans hδ (G.minDegree_le_degree v₁)
  have hcard : 3 ≤ (G.neighborFinset v₁).card := by
    rw [G.card_neighborFinset_eq_degree]; exact hdeg
  have hv₂_mem : v₂ ∈ G.neighborFinset v₁ := by
    simp [G.mem_neighborFinset]; exact hadj
  have hcard' : 2 ≤ ((G.neighborFinset v₁).erase v₂).card := by
    rw [Finset.card_erase_of_mem hv₂_mem]; omega
  obtain ⟨v₃, hv₃_mem, v₄, hv₄_mem, hv₃v₄⟩ :=
    Finset.one_lt_card.mp (by linarith : 1 < ((G.neighborFinset v₁).erase v₂).card)
  refine ⟨v₃, v₄, hv₃v₄, ?_, ?_, ?_, ?_⟩
  · exact (Finset.mem_erase.mp hv₃_mem).1
  · exact (Finset.mem_erase.mp hv₄_mem).1
  · rw [← G.mem_neighborFinset]; exact (Finset.mem_erase.mp hv₃_mem).2
  · rw [← G.mem_neighborFinset]; exact (Finset.mem_erase.mp hv₄_mem).2

/-- **Carr 2026 pre-case**: if an edge `v₁ v₂` has two *distinct* common
external neighbours `v₃ ≠ v₄`, then `G` has a 4-cycle. This is the case
that the main Carr argument discharges *before* the Case 1 / Case 2
split, and is closed by `has_2pow_cycle_of_chain4`. -/
theorem carr2026_precase_two_shared_neighbours
    {v₁ v₂ v₃ v₄ : V} (h₁₂ : G.Adj v₁ v₂)
    (h₁₃ : G.Adj v₁ v₃) (h₂₃ : G.Adj v₂ v₃)
    (h₁₄ : G.Adj v₁ v₄) (h₂₄ : G.Adj v₂ v₄)
    (h₃₄ : v₃ ≠ v₄) :
    Has2PowCycle G := by
  -- 4-cycle: v₁ → v₃ → v₂ → v₄ → v₁.
  apply has_2pow_cycle_of_chain4
    (h₁₃)               -- v₁ ~ v₃
    (h₂₃.symm)          -- v₃ ~ v₂
    (h₂₄)               -- v₂ ~ v₄
    (h₁₄.symm)          -- v₄ ~ v₁
  · exact h₁₃.ne                 -- v₁ ≠ v₃
  · exact h₁₂.ne                 -- v₁ ≠ v₂
  · exact h₁₄.ne                 -- v₁ ≠ v₄
  · exact h₂₃.ne'                -- v₃ ≠ v₂  (note flipped)
  · exact h₃₄                    -- v₃ ≠ v₄
  · exact h₂₄.ne                 -- v₂ ≠ v₄

/-- **Carr 2026, Case 2C**: zero shared neighbours and `v₈ ∉ {v₁, v₂}`.
With Carr's labelling (edge `v₁v₂`; `v₃, v₄` other neighbours of `v₁`;
`v₅, v₆` other neighbours of `v₂`; `v₇ ∈ N(v₃) ∩ N(v₅)`;
`v₈ ∈ N(v₄) ∩ N(v₆)`), the explicit 8-cycle is

  `v₇ — v₃ — v₁ — v₄ — v₈ — v₆ — v₂ — v₅ — v₇`.

Discharged via `has_2pow_cycle_of_chain8` once the 28 pairwise
distinctness hypotheses are in scope. -/
theorem carr2026_case_2C_eightCycle
    {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h13 : G.Adj v₁ v₃) (h14 : G.Adj v₁ v₄) (h25 : G.Adj v₂ v₅)
    (h26 : G.Adj v₂ v₆) (h37 : G.Adj v₃ v₇) (h48 : G.Adj v₄ v₈)
    (h57 : G.Adj v₅ v₇) (h68 : G.Adj v₆ v₈)
    (h_12 : v₁ ≠ v₂) (h_13 : v₁ ≠ v₃) (h_14 : v₁ ≠ v₄) (h_15 : v₁ ≠ v₅)
    (h_16 : v₁ ≠ v₆) (h_17 : v₁ ≠ v₇) (h_18 : v₁ ≠ v₈)
    (h_23 : v₂ ≠ v₃) (h_24 : v₂ ≠ v₄) (h_25 : v₂ ≠ v₅) (h_26 : v₂ ≠ v₆)
    (h_27 : v₂ ≠ v₇) (h_28 : v₂ ≠ v₈)
    (h_34 : v₃ ≠ v₄) (h_35 : v₃ ≠ v₅) (h_36 : v₃ ≠ v₆) (h_37 : v₃ ≠ v₇)
    (h_38 : v₃ ≠ v₈)
    (h_45 : v₄ ≠ v₅) (h_46 : v₄ ≠ v₆) (h_47 : v₄ ≠ v₇) (h_48 : v₄ ≠ v₈)
    (h_56 : v₅ ≠ v₆) (h_57 : v₅ ≠ v₇) (h_58 : v₅ ≠ v₈)
    (h_67 : v₆ ≠ v₇) (h_68 : v₆ ≠ v₈)
    (h_78 : v₇ ≠ v₈) :
    Has2PowCycle G := by
  -- Apply `has_2pow_cycle_of_chain8` with the u-ordering
  --   u = (v₇, v₃, v₁, v₄, v₈, v₆, v₂, v₅)
  -- 8 adjacencies for the cycle u₁→u₂→…→u₈→u₁.
  apply has_2pow_cycle_of_chain8
    (h37.symm)         -- u₁u₂ : v₇ ~ v₃
    (h13.symm)         -- u₂u₃ : v₃ ~ v₁
    (h14)              -- u₃u₄ : v₁ ~ v₄
    (h48)              -- u₄u₅ : v₄ ~ v₈
    (h68.symm)         -- u₅u₆ : v₈ ~ v₆
    (h26.symm)         -- u₆u₇ : v₆ ~ v₂
    (h25)              -- u₇u₈ : v₂ ~ v₅
    (h57)              -- u₈u₁ : v₅ ~ v₇
  -- 28 distinctness, in the order (d_ij : u_i ≠ u_j for 1 ≤ i < j ≤ 8).
  -- u₁=v₇, u₂=v₃, u₃=v₁, u₄=v₄, u₅=v₈, u₆=v₆, u₇=v₂, u₈=v₅.
  · exact h_37.symm   -- d12: v₇ ≠ v₃
  · exact h_17.symm   -- d13: v₇ ≠ v₁
  · exact h_47.symm   -- d14: v₇ ≠ v₄
  · exact h_78        -- d15: v₇ ≠ v₈
  · exact h_67.symm   -- d16: v₇ ≠ v₆
  · exact h_27.symm   -- d17: v₇ ≠ v₂
  · exact h_57.symm   -- d18: v₇ ≠ v₅
  · exact h_13.symm   -- d23: v₃ ≠ v₁
  · exact h_34        -- d24: v₃ ≠ v₄
  · exact h_38        -- d25: v₃ ≠ v₈
  · exact h_36        -- d26: v₃ ≠ v₆
  · exact h_23.symm   -- d27: v₃ ≠ v₂
  · exact h_35        -- d28: v₃ ≠ v₅
  · exact h_14        -- d34: v₁ ≠ v₄
  · exact h_18        -- d35: v₁ ≠ v₈
  · exact h_16        -- d36: v₁ ≠ v₆
  · exact h_12        -- d37: v₁ ≠ v₂
  · exact h_15        -- d38: v₁ ≠ v₅
  · exact h_48        -- d45: v₄ ≠ v₈
  · exact h_46        -- d46: v₄ ≠ v₆
  · exact h_24.symm   -- d47: v₄ ≠ v₂
  · exact h_45        -- d48: v₄ ≠ v₅
  · exact h_68.symm   -- d56: v₈ ≠ v₆
  · exact h_28.symm   -- d57: v₈ ≠ v₂
  · exact h_58.symm   -- d58: v₈ ≠ v₅
  · exact h_26.symm   -- d67: v₆ ≠ v₂
  · exact h_56.symm   -- d68: v₆ ≠ v₅
  · exact h_25        -- d78: v₂ ≠ v₅

/-- **Carr 2026, Theorem 1.1**: every graph with diameter 2 and minimum
degree ≥ 3 contains a cycle of length 4 or 8.

Proof body deferred; the pre-case (two shared neighbours → `C₄`) is
discharged by `carr2026_precase_two_shared_neighbours` above. Cases 1,
2A, 2B, 2C from Carr 2026 remain `sorry`. See memo 0037 for the
per-claim breakdown. -/
theorem carr2026_diam_two_minDegree_three
    (_hδ : 3 ≤ G.minDegree) (_hd : G.diam ≤ 2) (_hd_pos : G.diam ≠ 0) :
    Has2PowCycle G := by
  sorry

end Erdos64

#print axioms Erdos64.exists_two_other_neighbours
#print axioms Erdos64.carr2026_precase_two_shared_neighbours
#print axioms Erdos64.carr2026_case_2C_eightCycle
