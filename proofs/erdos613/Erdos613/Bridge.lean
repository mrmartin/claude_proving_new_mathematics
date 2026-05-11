/-
Bridge from Tao's `PikhurkoN5.red_triangle_of_no_blue_star` to the upstream
`Erdos613.erdos_613` shape.

We refute the universal `∀ n ≥ 3, ∀ G, edgeCount → ∃ B D, G = B⊔D ∧
B.IsBipartite ∧ ∀v, D.deg v < n` by instantiating `n = 5`, `G = PikhurkoN5.G`.

From the existential we'd obtain `(B, D)`; we define an edge 2-coloring
`c(e) = 0` on `D.edgeSet`, `1` elsewhere. Tao gives `hasMonoStar c 0 5 ∨
hasMonoTriangle c 1`:

* a `c = 0` star at vertex `x` ⇒ `D.degree x ≥ 5`, contradicting `D.deg v < 5`;
* a `c = 1` triangle ⇒ a triangle in `B`, contradicting `B.IsBipartite`.
-/

import Erdos613.Tao
import Mathlib

namespace Erdos613Bridge

open Classical PikhurkoN5

/-- Edge 2-coloring: `0` on `D.edgeSet`, `1` elsewhere. -/
noncomputable def coloringOfDecomp {V : Type*} (D : SimpleGraph V) :
    Sym2 V → Fin 2 := fun e => if e ∈ D.edgeSet then 0 else 1

lemma coloringOfDecomp_eq_zero {V : Type*} {D : SimpleGraph V} {e : Sym2 V}
    (h : e ∈ D.edgeSet) : coloringOfDecomp D e = 0 := by
  simp [coloringOfDecomp, h]

lemma coloringOfDecomp_eq_one {V : Type*} {D : SimpleGraph V} {e : Sym2 V}
    (h : e ∉ D.edgeSet) : coloringOfDecomp D e = 1 := by
  simp [coloringOfDecomp, h]

/-- If `c(s(u, v)) = 0` then `D.Adj u v`. -/
lemma adj_of_color_zero {V : Type*} {D : SimpleGraph V} {u v : V}
    (hc : coloringOfDecomp D s(u, v) = 0) : D.Adj u v := by
  by_contra hAdj
  have : s(u, v) ∉ D.edgeSet := by
    intro h
    exact hAdj (by simpa [SimpleGraph.mem_edgeSet] using h)
  rw [coloringOfDecomp_eq_one this] at hc
  exact absurd hc (by decide)

/-- If `c(s(u, v)) = 1` and `G.Adj u v` with `G = B ⊔ D`, then `B.Adj u v`. -/
lemma adj_of_color_one {V : Type*} {B D : SimpleGraph V} {u v : V}
    (hBD : (B ⊔ D : SimpleGraph V).Adj u v)
    (hc : coloringOfDecomp D s(u, v) = 1) : B.Adj u v := by
  -- s(u, v) ∉ D.edgeSet
  have hND : ¬ D.Adj u v := by
    intro hD
    have : s(u, v) ∈ D.edgeSet := by simpa [SimpleGraph.mem_edgeSet] using hD
    rw [coloringOfDecomp_eq_zero this] at hc
    exact absurd hc (by decide)
  rcases hBD with hB | hD
  · exact hB
  · exact absurd hD hND

/-- Bridge theorem (intermediate shape, classical-friendly). -/
theorem erdos_613_bridge :
    False ↔
      ∀ n, 3 ≤ n → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 →
        ∃ (B D : SimpleGraph V),
          G = B ⊔ D ∧ B.IsBipartite ∧ ∀ v, D.degree v < n := by
  refine ⟨fun h => h.elim, ?_⟩
  intro h
  -- Edge count for PikhurkoN5.G:  G.edgeFinset.card = C(11, 2) - C(5, 2) - 1 = 44.
  have hEdgeNum : (PikhurkoN5.G).edgeFinset.card =
      Nat.choose (2 * 5 + 1) 2 - Nat.choose 5 2 - 1 := by
    have h44 : (PikhurkoN5.G).edgeFinset.card = 44 := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
      exact PikhurkoN5.edge_count_44
    rw [h44]; decide
  -- Apply the universal to obtain the (impossible) decomposition.
  obtain ⟨B, D, hGdecomp, hBip, hDeg⟩ :=
    h 5 (by decide) PikhurkoN5.V PikhurkoN5.G hEdgeNum
  -- Define the edge 2-coloring; 0 on D, 1 on B (and on non-edges of G).
  let c : Sym2 PikhurkoN5.V → Fin 2 := coloringOfDecomp D
  -- Apply Tao's main combinatorial step.
  by_cases hStar : hasMonoStar PikhurkoN5.G c 0 5
  · -- 5-star in color 0 ⇒ D has a vertex of degree ≥ 5.
    obtain ⟨x, S, hScard, hxnS, hxNbhd⟩ := hStar
    -- For each y ∈ S, c(s(x, y)) = 0, so D.Adj x y.
    have hSubset : S ⊆ (D.neighborFinset x : Finset PikhurkoN5.V) := by
      intro y hy
      obtain ⟨hAdjG, hCol⟩ := hxNbhd hy
      have hDxy : D.Adj x y := adj_of_color_zero hCol
      simp [SimpleGraph.mem_neighborFinset, hDxy]
    have h5 : 5 ≤ (D.neighborFinset x).card := by
      have := Finset.card_le_card hSubset
      rw [hScard] at this; exact this
    have hdx : 5 ≤ D.degree x := by
      unfold SimpleGraph.degree; exact h5
    exact absurd hdx (by have := hDeg x; omega)
  · -- No 5-star in color 0 ⇒ by Tao, triangle in color 1.
    have hTri := PikhurkoN5.red_triangle_of_no_blue_star c hStar
    obtain ⟨a, b, d, hab, hbd, had, hcab, hcbd, hcad⟩ := hTri
    -- All three triangle edges are in B because they are color 1.
    have hG := hGdecomp
    have hSup : ∀ u v, (B ⊔ D).Adj u v ↔ B.Adj u v ∨ D.Adj u v := by
      intro u v; simp [SimpleGraph.sup_adj]
    -- Build B-adjacencies from G-adjacencies + color-1.
    have hBab : B.Adj a b := by
      have hG_ab : (B ⊔ D).Adj a b := hG ▸ hab
      exact adj_of_color_one hG_ab hcab
    have hBbd : B.Adj b d := by
      have hG_bd : (B ⊔ D).Adj b d := hG ▸ hbd
      exact adj_of_color_one hG_bd hcbd
    have hBad : B.Adj a d := by
      have hG_ad : (B ⊔ D).Adj a d := hG ▸ had
      exact adj_of_color_one hG_ad hcad
    -- B has a triangle; but B is 2-colorable, contradiction.
    -- Use that a 2-colorable graph cannot contain a 3-clique.
    have hABC_dist : a ≠ b ∧ b ≠ d ∧ a ≠ d :=
      ⟨hBab.ne, hBbd.ne, hBad.ne⟩
    -- Extract a 2-coloring of B and derive contradiction on the triangle.
    obtain ⟨φ⟩ := hBip
    have hφab : φ a ≠ φ b := φ.valid hBab
    have hφbd : φ b ≠ φ d := φ.valid hBbd
    have hφad : φ a ≠ φ d := φ.valid hBad
    -- Three vertices in Fin 2 with pairwise distinct images is impossible.
    have ka := φ a
    have kb := φ b
    have kd := φ d
    have : (φ a : ℕ) < 2 := (φ a).isLt
    have : (φ b : ℕ) < 2 := (φ b).isLt
    have : (φ d : ℕ) < 2 := (φ d).isLt
    have hab' : (φ a : ℕ) ≠ (φ b : ℕ) := fun h => hφab (Fin.ext h)
    have hbd' : (φ b : ℕ) ≠ (φ d : ℕ) := fun h => hφbd (Fin.ext h)
    have had' : (φ a : ℕ) ≠ (φ d : ℕ) := fun h => hφad (Fin.ext h)
    omega

end Erdos613Bridge

-- Axiom check
#print axioms Erdos613Bridge.erdos_613_bridge
