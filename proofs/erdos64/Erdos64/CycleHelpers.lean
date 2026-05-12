/-
**Cycle constructors for explicit walks.**

mathlib has `Walk.IsCycle` but its constructor obligations
(`IsTrail.edges_nodup`, `support_nodup`) are awkward to discharge
for a generic vertex type `V` without `decide`. This module bridges
that gap: given four pairwise-distinct vertices and the chain of
adjacency hypotheses, produce a `Walk.IsCycle` for the cyclic walk.
-/

import Erdos64.Basic

namespace Erdos64

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-! ### Sym2-equality helper

For pairwise-distinct vertices, `Sym2` "unordered pair" equality
collapses to ordered equality (modulo swap). -/

private lemma Sym2_ne_of_pairwise_distinct {a b c d : V}
    (hac : a ≠ c) (hbd : b ≠ d) (had : a ≠ d) (hbc : b ≠ c) :
    s(a, b) ≠ s(c, d) := by
  intro h
  -- s(a,b) = s(c,d) ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c).
  rcases (Sym2.eq_iff).mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hac ha
  · exact had ha

/-! ### 4-cycle constructor -/

/-- A 4-walk `a → b → c → d → a` in a `SimpleGraph`. -/
def walk4 {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) : G.Walk a a :=
  Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))

@[simp] theorem walk4_length {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) :
    (walk4 hab hbc hcd hda).length = 4 := by
  simp [walk4, Walk.length_cons]

/-- Inner walk `b → c → d → a` of a `walk4`, exposed as a separate def for
the `cons_isCycle_iff` rewrite. -/
private def walk4_inner {a b c d : V} (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) : G.Walk b a :=
  Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil))

private theorem walk4_inner_isPath {a b c d : V}
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_ad : a ≠ d)
    (h_bc : b ≠ c) (h_bd : b ≠ d) (h_cd : c ≠ d) :
    (walk4_inner hbc hcd hda).IsPath := by
  rw [Walk.isPath_def]
  show (walk4_inner hbc hcd hda).support.Nodup
  -- support = [b, c, d, a].
  simp only [walk4_inner, Walk.support_cons, Walk.support_nil,
             List.nodup_cons, List.mem_cons, List.mem_singleton,
             List.not_mem_nil, List.nodup_nil, or_false, not_or,
             not_false_eq_true, and_true]
  exact ⟨⟨h_bc, h_bd, h_ab.symm⟩, ⟨h_cd, h_ac.symm⟩, h_ad.symm⟩

private theorem walk4_inner_edge_not_mem {a b c d : V}
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_ad : a ≠ d)
    (h_bc : b ≠ c) (h_bd : b ≠ d) (h_cd : c ≠ d) :
    s(a, b) ∉ (walk4_inner hbc hcd hda).edges := by
  simp only [walk4_inner, Walk.edges_cons, Walk.edges_nil,
             List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩
  · -- s(a, b) ≠ s(b, c). {a, b} = {b, c} iff (a = b ∧ b = c) or
    -- (a = c ∧ b = b). The first contradicts h_ab; the second contradicts h_ac.
    intro h
    rcases (Sym2.eq_iff).mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact h_ab ha
    · exact h_ac ha
  · -- s(a, b) ≠ s(c, d)
    exact Sym2_ne_of_pairwise_distinct h_ac h_bd h_ad h_bc
  · -- s(a, b) ≠ s(d, a). {a, b} = {d, a} iff (a = d ∧ b = a) or
    -- (a = a ∧ b = d). The first contradicts h_ad; the second contradicts h_bd.
    intro h
    rcases (Sym2.eq_iff).mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact h_ad ha
    · exact h_bd hb

/-- Given four pairwise-distinct vertices `a, b, c, d` with the four
chain edges `a ~ b ~ c ~ d ~ a`, the cyclic walk `a → b → c → d → a`
is a cycle. -/
theorem walk4_isCycle {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_ad : a ≠ d)
    (h_bc : b ≠ c) (h_bd : b ≠ d) (h_cd : c ≠ d) :
    (walk4 hab hbc hcd hda).IsCycle := by
  show (Walk.cons hab (walk4_inner hbc hcd hda)).IsCycle
  rw [Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · exact walk4_inner_isPath hbc hcd hda h_ab h_ac h_ad h_bc h_bd h_cd
  · exact walk4_inner_edge_not_mem hbc hcd hda h_ab h_ac h_ad h_bc h_bd h_cd

/-- Convenience wrapper: a 4-cycle witness suffices to discharge
`Has2PowCycle`. -/
theorem has_2pow_cycle_of_chain4 {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_ad : a ≠ d)
    (h_bc : b ≠ c) (h_bd : b ≠ d) (h_cd : c ≠ d) :
    Has2PowCycle G := by
  apply has_2pow_cycle_of_has_C4
  exact ⟨a, walk4 hab hbc hcd hda,
         walk4_isCycle hab hbc hcd hda h_ab h_ac h_ad h_bc h_bd h_cd,
         walk4_length hab hbc hcd hda⟩

/-! ### 8-cycle helper (needed for Carr 2026 Case 2C). -/

/-- An 8-walk `v₁ → v₂ → … → v₈ → v₁`. -/
def walk8 {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄)
    (h45 : G.Adj v₄ v₅) (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇)
    (h78 : G.Adj v₇ v₈) (h81 : G.Adj v₈ v₁) : G.Walk v₁ v₁ :=
  Walk.cons h12 (Walk.cons h23 (Walk.cons h34 (Walk.cons h45
    (Walk.cons h56 (Walk.cons h67 (Walk.cons h78
    (Walk.cons h81 Walk.nil)))))))

@[simp] theorem walk8_length {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄)
    (h45 : G.Adj v₄ v₅) (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇)
    (h78 : G.Adj v₇ v₈) (h81 : G.Adj v₈ v₁) :
    (walk8 h12 h23 h34 h45 h56 h67 h78 h81).length = 8 := by
  simp [walk8, Walk.length_cons]

/-- Inner walk `v₂ → v₃ → v₄ → v₅ → v₆ → v₇ → v₈ → v₁` of a `walk8`. -/
private def walk8_inner {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄) (h45 : G.Adj v₄ v₅)
    (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇) (h78 : G.Adj v₇ v₈)
    (h81 : G.Adj v₈ v₁) : G.Walk v₂ v₁ :=
  Walk.cons h23 (Walk.cons h34 (Walk.cons h45 (Walk.cons h56
    (Walk.cons h67 (Walk.cons h78 (Walk.cons h81 Walk.nil))))))

private theorem walk8_inner_isPath {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄) (h45 : G.Adj v₄ v₅)
    (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇) (h78 : G.Adj v₇ v₈)
    (h81 : G.Adj v₈ v₁)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d16 : v₁ ≠ v₆) (d17 : v₁ ≠ v₇) (d18 : v₁ ≠ v₈)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅) (d26 : v₂ ≠ v₆)
    (d27 : v₂ ≠ v₇) (d28 : v₂ ≠ v₈)
    (d34 : v₃ ≠ v₄) (d35 : v₃ ≠ v₅) (d36 : v₃ ≠ v₆) (d37 : v₃ ≠ v₇)
    (d38 : v₃ ≠ v₈)
    (d45 : v₄ ≠ v₅) (d46 : v₄ ≠ v₆) (d47 : v₄ ≠ v₇) (d48 : v₄ ≠ v₈)
    (d56 : v₅ ≠ v₆) (d57 : v₅ ≠ v₇) (d58 : v₅ ≠ v₈)
    (d67 : v₆ ≠ v₇) (d68 : v₆ ≠ v₈)
    (d78 : v₇ ≠ v₈) :
    (walk8_inner h23 h34 h45 h56 h67 h78 h81).IsPath := by
  rw [Walk.isPath_def]
  show (walk8_inner h23 h34 h45 h56 h67 h78 h81).support.Nodup
  -- support = [v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₁].
  simp only [walk8_inner, Walk.support_cons, Walk.support_nil,
             List.nodup_cons, List.mem_cons,
             List.not_mem_nil, List.nodup_nil, or_false, not_or,
             not_false_eq_true, and_true]
  refine ⟨⟨d23, d24, d25, d26, d27, d28, d12.symm⟩,
          ⟨d34, d35, d36, d37, d38, d13.symm⟩,
          ⟨d45, d46, d47, d48, d14.symm⟩,
          ⟨d56, d57, d58, d15.symm⟩,
          ⟨d67, d68, d16.symm⟩,
          ⟨d78, d17.symm⟩,
          d18.symm⟩

private theorem walk8_inner_edge_not_mem {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄) (h45 : G.Adj v₄ v₅)
    (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇) (h78 : G.Adj v₇ v₈)
    (h81 : G.Adj v₈ v₁)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d16 : v₁ ≠ v₆) (d17 : v₁ ≠ v₇) (d18 : v₁ ≠ v₈)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅) (d26 : v₂ ≠ v₆)
    (d27 : v₂ ≠ v₇) (d28 : v₂ ≠ v₈) :
    s(v₁, v₂) ∉ (walk8_inner h23 h34 h45 h56 h67 h78 h81).edges := by
  simp only [walk8_inner, Walk.edges_cons, Walk.edges_nil,
             List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- s(v₁, v₂) ≠ s(v₂, v₃)
    intro h
    rcases (Sym2.eq_iff).mp h with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact d12 ha
    · exact d13 ha
  · -- s(v₁, v₂) ≠ s(v₃, v₄)
    exact Sym2_ne_of_pairwise_distinct d13 d24 d14 d23
  · -- s(v₁, v₂) ≠ s(v₄, v₅)
    exact Sym2_ne_of_pairwise_distinct d14 d25 d15 d24
  · -- s(v₁, v₂) ≠ s(v₅, v₆)
    exact Sym2_ne_of_pairwise_distinct d15 d26 d16 d25
  · -- s(v₁, v₂) ≠ s(v₆, v₇)
    exact Sym2_ne_of_pairwise_distinct d16 d27 d17 d26
  · -- s(v₁, v₂) ≠ s(v₇, v₈)
    exact Sym2_ne_of_pairwise_distinct d17 d28 d18 d27
  · -- s(v₁, v₂) ≠ s(v₈, v₁)
    intro h
    rcases (Sym2.eq_iff).mp h with ⟨ha, hb⟩ | ⟨_, hb⟩
    · exact d18 ha
    · exact d28 hb

/-- Given eight pairwise-distinct vertices `v₁, …, v₈` with the eight
chain edges `v₁ ~ v₂ ~ v₃ ~ v₄ ~ v₅ ~ v₆ ~ v₇ ~ v₈ ~ v₁`, the cyclic
walk `walk8` is a cycle. -/
theorem walk8_isCycle {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄)
    (h45 : G.Adj v₄ v₅) (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇)
    (h78 : G.Adj v₇ v₈) (h81 : G.Adj v₈ v₁)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d16 : v₁ ≠ v₆) (d17 : v₁ ≠ v₇) (d18 : v₁ ≠ v₈)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅) (d26 : v₂ ≠ v₆)
    (d27 : v₂ ≠ v₇) (d28 : v₂ ≠ v₈)
    (d34 : v₃ ≠ v₄) (d35 : v₃ ≠ v₅) (d36 : v₃ ≠ v₆) (d37 : v₃ ≠ v₇)
    (d38 : v₃ ≠ v₈)
    (d45 : v₄ ≠ v₅) (d46 : v₄ ≠ v₆) (d47 : v₄ ≠ v₇) (d48 : v₄ ≠ v₈)
    (d56 : v₅ ≠ v₆) (d57 : v₅ ≠ v₇) (d58 : v₅ ≠ v₈)
    (d67 : v₆ ≠ v₇) (d68 : v₆ ≠ v₈)
    (d78 : v₇ ≠ v₈) :
    (walk8 h12 h23 h34 h45 h56 h67 h78 h81).IsCycle := by
  show (Walk.cons h12 (walk8_inner h23 h34 h45 h56 h67 h78 h81)).IsCycle
  rw [Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · exact walk8_inner_isPath h23 h34 h45 h56 h67 h78 h81
      d12 d13 d14 d15 d16 d17 d18
      d23 d24 d25 d26 d27 d28
      d34 d35 d36 d37 d38
      d45 d46 d47 d48
      d56 d57 d58
      d67 d68
      d78
  · exact walk8_inner_edge_not_mem h23 h34 h45 h56 h67 h78 h81
      d12 d13 d14 d15 d16 d17 d18
      d23 d24 d25 d26 d27 d28

/-- Convenience wrapper: an 8-cycle witness from 8 pairwise-distinct
vertices suffices to discharge `Has2PowCycle`. Mirrors
`has_2pow_cycle_of_chain4`. -/
theorem has_2pow_cycle_of_chain8 {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h12 : G.Adj v₁ v₂) (h23 : G.Adj v₂ v₃) (h34 : G.Adj v₃ v₄)
    (h45 : G.Adj v₄ v₅) (h56 : G.Adj v₅ v₆) (h67 : G.Adj v₆ v₇)
    (h78 : G.Adj v₇ v₈) (h81 : G.Adj v₈ v₁)
    (d12 : v₁ ≠ v₂) (d13 : v₁ ≠ v₃) (d14 : v₁ ≠ v₄) (d15 : v₁ ≠ v₅)
    (d16 : v₁ ≠ v₆) (d17 : v₁ ≠ v₇) (d18 : v₁ ≠ v₈)
    (d23 : v₂ ≠ v₃) (d24 : v₂ ≠ v₄) (d25 : v₂ ≠ v₅) (d26 : v₂ ≠ v₆)
    (d27 : v₂ ≠ v₇) (d28 : v₂ ≠ v₈)
    (d34 : v₃ ≠ v₄) (d35 : v₃ ≠ v₅) (d36 : v₃ ≠ v₆) (d37 : v₃ ≠ v₇)
    (d38 : v₃ ≠ v₈)
    (d45 : v₄ ≠ v₅) (d46 : v₄ ≠ v₆) (d47 : v₄ ≠ v₇) (d48 : v₄ ≠ v₈)
    (d56 : v₅ ≠ v₆) (d57 : v₅ ≠ v₇) (d58 : v₅ ≠ v₈)
    (d67 : v₆ ≠ v₇) (d68 : v₆ ≠ v₈)
    (d78 : v₇ ≠ v₈) :
    Has2PowCycle G := by
  apply has_2pow_cycle_of_has_C8
  exact ⟨v₁, walk8 h12 h23 h34 h45 h56 h67 h78 h81,
         walk8_isCycle h12 h23 h34 h45 h56 h67 h78 h81
           d12 d13 d14 d15 d16 d17 d18
           d23 d24 d25 d26 d27 d28
           d34 d35 d36 d37 d38
           d45 d46 d47 d48
           d56 d57 d58
           d67 d68
           d78,
         walk8_length h12 h23 h34 h45 h56 h67 h78 h81⟩

/-- The version we originally shipped (Phase 4 walkthrough): if you
already have a cycle of length 8 explicitly, `Has2PowCycle G` follows.
Kept for backwards compatibility with the `DiamTwo` outline. -/
theorem has_2pow_cycle_of_isCycle_length_eight {v : V}
    (w : G.Walk v v) (hw : w.IsCycle) (hlen : w.length = 8) :
    Has2PowCycle G :=
  has_2pow_cycle_of_has_C8 _ ⟨v, w, hw, hlen⟩

end Erdos64

#print axioms Erdos64.walk4_isCycle
#print axioms Erdos64.has_2pow_cycle_of_chain4
#print axioms Erdos64.walk8_isCycle
#print axioms Erdos64.has_2pow_cycle_of_chain8
#print axioms Erdos64.has_2pow_cycle_of_isCycle_length_eight
