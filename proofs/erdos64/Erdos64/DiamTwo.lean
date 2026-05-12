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
