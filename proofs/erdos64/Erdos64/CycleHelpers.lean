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

end Erdos64

#print axioms Erdos64.walk4_isCycle
#print axioms Erdos64.has_2pow_cycle_of_chain4
