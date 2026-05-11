/-
**Track C2 / A2 prerequisite: bipartite graphs have no odd cycle.**

This module proves:

* `Walk.length_eq_of_coloring_endpoints`: a properly-2-coloured walk has
  endpoint colours equal iff its length is even.
* `IsBipartite.even_length_of_isCycle`: every cycle in a bipartite graph
  has even length.

Both directions of the equivalence `IsBipartite ↔ no odd cycle` would
require the converse (no odd cycle → bipartite), which is more
involved (it constructs the coloring via BFS layers). We only need
the easy direction here.

`Bipartite.lean` of mathlib v4.28.0 explicitly lists this as a TODO
(line 63: "Prove that `G.IsBipartite` iff `G` does not contain an
odd cycle").

This lemma feeds Track A2's bipartite cubic sub-case: a cubic
bipartite graph with girth ≤ 8 must contain a 4-cycle (when girth = 4)
or an 8-cycle (when girth ≥ 6, by parity + degree count). The
parity step requires what we prove here.
-/

import Erdos64.Basic

namespace Erdos64

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- For a proper 2-colouring `C` of `G`, walking along `G` flips the
colour iff the walk length is odd. -/
lemma colour_eq_iff_even (C : G.Coloring (Fin 2)) {u v : V} (w : G.Walk u v) :
    C u = C v ↔ Even w.length := by
  induction w with
  | nil => simp
  | @cons a b c h_adj p ih =>
    -- Walk = cons h_adj p, where p : G.Walk b c and we want C a = C c ↔ Even (1 + p.length).
    simp only [Walk.length_cons]
    have h_diff : C a ≠ C b := C.valid h_adj
    have hCb_lt : (C b).val < 2 := (C b).isLt
    have hCa_lt : (C a).val < 2 := (C a).isLt
    have hCc_lt : (C c).val < 2 := (C c).isLt
    have h_ab : (C a).val ≠ (C b).val := fun e => h_diff (Fin.ext e)
    constructor
    · intro hCac
      by_cases hCbc : C b = C c
      · exact absurd (hCac.trans hCbc.symm) h_diff
      · have h_not_even : ¬ Even p.length := fun he => hCbc (ih.mpr he)
        have h_odd : Odd p.length := Nat.not_even_iff_odd.mp h_not_even
        exact h_odd.add_one
    · intro h_even
      have h_odd : Odd p.length := by
        rcases h_even with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have h_not_even : ¬ Even p.length := Nat.not_even_iff_odd.mpr h_odd
      have hCbc_ne : C b ≠ C c := fun e => h_not_even (ih.mp e)
      have h_bc : (C b).val ≠ (C c).val := fun e => hCbc_ne (Fin.ext e)
      apply Fin.ext
      omega

/-- Every closed walk in a 2-colourable graph has even length. -/
theorem even_length_of_isBipartite_of_closed (h : G.IsBipartite) {u : V}
    (c : G.Walk u u) : Even c.length := by
  obtain ⟨C⟩ := h
  exact (colour_eq_iff_even C c).mp rfl

/-- Every cycle in a 2-colourable graph has even length. -/
theorem IsCycle.even_length_of_isBipartite (h : G.IsBipartite) {u : V}
    {c : G.Walk u u} (_hc : c.IsCycle) : Even c.length :=
  even_length_of_isBipartite_of_closed h c

/-- In a bipartite graph, there is no cycle of odd length. -/
theorem not_isCycle_of_odd_length_of_isBipartite (h : G.IsBipartite) {u : V}
    {c : G.Walk u u} (hodd : Odd c.length) : ¬ c.IsCycle := fun hc => by
  have heven := IsCycle.even_length_of_isBipartite h hc
  exact (Nat.not_odd_iff_even.mpr heven) hodd

end Erdos64

#print axioms Erdos64.IsCycle.even_length_of_isBipartite
