/-
**Track A2 partial: bipartite graphs with girth ∈ {4, 8} satisfy Erdős 64.**

A genuinely full Track A2 deliverable would be "every bipartite cubic
graph with girth ≤ 8 has a `C₄` or `C₈`". The structural breakdown is:

- bipartite ⇒ every cycle has even length ≥ 4 (memo 0034, this repo).
- so if `girth ≤ 8` and `girth > 0`, then `girth ∈ {4, 6, 8}`.
- girth = 4 ⇒ `C₄` exists (= the girth cycle).
- girth = 8 ⇒ `C₈` exists (= the girth cycle).
- girth = 6 ⇒ need to show `C₈` exists. **NOT obviously true** even for
  cubic bipartite graphs; needs a structural argument (BFS-layer
  count + pigeonhole) that we do not yet have. Deferred.

So this module ships the **easy two-thirds** of the bipartite cubic
A2 deliverable: girth-4 and girth-8 cases (no cubic hypothesis needed
at all — the only premise we use is `bipartite` plus `girth ∈ {4, 8}`).
The girth-6 case is flagged in memo 0036 as a separate open question.
-/

import Erdos64.Basic
import Erdos64.Bipartite

namespace Erdos64

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- If `G.girth = 4`, the girth-realising cycle is a 4-cycle, hence
`G` satisfies the Erdős 64 conclusion. -/
theorem has_2pow_cycle_of_girth_eq_four (hG : ¬ G.IsAcyclic) (hg : G.girth = 4) :
    Has2PowCycle G := by
  obtain ⟨a, w, hw_cycle, hw_len⟩ := exists_girth_eq_length.mpr hG
  apply has_2pow_cycle_of_has_C4
  refine ⟨a, w, hw_cycle, ?_⟩
  rw [← hw_len, hg]

/-- If `G.girth = 8`, the girth-realising cycle is an 8-cycle, hence
`G` satisfies the Erdős 64 conclusion. -/
theorem has_2pow_cycle_of_girth_eq_eight (hG : ¬ G.IsAcyclic) (hg : G.girth = 8) :
    Has2PowCycle G := by
  obtain ⟨a, w, hw_cycle, hw_len⟩ := exists_girth_eq_length.mpr hG
  apply has_2pow_cycle_of_has_C8
  refine ⟨a, w, hw_cycle, ?_⟩
  rw [← hw_len, hg]

/-- In a bipartite graph (with at least one cycle), the girth is even. -/
theorem girth_even_of_isBipartite (hbip : G.IsBipartite) (hG : ¬ G.IsAcyclic) :
    Even G.girth := by
  obtain ⟨a, w, hw_cycle, hw_len⟩ := exists_girth_eq_length.mpr hG
  rw [hw_len]
  exact IsCycle.even_length_of_isBipartite hbip hw_cycle

/-- A bipartite graph (with at least one cycle) whose girth is `≤ 5` has
girth `= 4`, because the girth must be even and `≥ 3`. -/
theorem girth_eq_four_of_isBipartite_girth_le_five
    (hbip : G.IsBipartite) (hG : ¬ G.IsAcyclic) (hg : G.girth ≤ 5) :
    G.girth = 4 := by
  have h3 : 3 ≤ G.girth := three_le_girth hG
  have heven : Even G.girth := girth_even_of_isBipartite hbip hG
  -- girth ∈ {3, 4, 5}, even, so girth = 4.
  rcases heven with ⟨k, hk⟩
  omega

/-- A bipartite graph (with at least one cycle) whose girth is `≤ 8` has
girth in `{4, 6, 8}`. -/
theorem girth_mem_four_six_eight_of_isBipartite_girth_le_eight
    (hbip : G.IsBipartite) (hG : ¬ G.IsAcyclic) (hg : G.girth ≤ 8) :
    G.girth = 4 ∨ G.girth = 6 ∨ G.girth = 8 := by
  have h3 : 3 ≤ G.girth := three_le_girth hG
  have heven : Even G.girth := girth_even_of_isBipartite hbip hG
  rcases heven with ⟨k, hk⟩
  omega

/-- **A2 partial-1:** a bipartite graph with `girth ≤ 5` (and a cycle) has
girth exactly 4, hence a `C₄`. -/
theorem has_2pow_cycle_of_isBipartite_girth_le_five
    (hbip : G.IsBipartite) (hG : ¬ G.IsAcyclic) (hg : G.girth ≤ 5) :
    Has2PowCycle G :=
  has_2pow_cycle_of_girth_eq_four hG (girth_eq_four_of_isBipartite_girth_le_five hbip hG hg)

/-- **A2 partial-2:** a bipartite graph with `girth = 8` has an
8-cycle. (The `IsBipartite` hypothesis isn't actually used — girth-8
suffices — but we keep it for the symmetric API surface.) -/
theorem has_2pow_cycle_of_isBipartite_girth_eq_eight
    (_hbip : G.IsBipartite) (hG : ¬ G.IsAcyclic) (hg : G.girth = 8) :
    Has2PowCycle G :=
  has_2pow_cycle_of_girth_eq_eight hG hg

/-- **A2 conditional-on-girth-6:** a bipartite graph with `girth ≤ 8`
satisfies Erdős 64 *provided* the girth-6 sub-case is settled
(`girth = 6 → Has2PowCycle G`). The girth-6 case is **not** proved
here; it is the open piece of Track A2 (cf. memo 0036). -/
theorem has_2pow_cycle_of_isBipartite_girth_le_eight
    (hbip : G.IsBipartite) (hG : ¬ G.IsAcyclic) (hg : G.girth ≤ 8)
    (h_girth_6_case : G.girth = 6 → Has2PowCycle G) :
    Has2PowCycle G := by
  rcases girth_mem_four_six_eight_of_isBipartite_girth_le_eight hbip hG hg with h4 | h6 | h8
  · exact has_2pow_cycle_of_girth_eq_four hG h4
  · exact h_girth_6_case h6
  · exact has_2pow_cycle_of_girth_eq_eight hG h8

end Erdos64

#print axioms Erdos64.has_2pow_cycle_of_isBipartite_girth_le_five
#print axioms Erdos64.has_2pow_cycle_of_isBipartite_girth_eq_eight
#print axioms Erdos64.has_2pow_cycle_of_isBipartite_girth_le_eight
