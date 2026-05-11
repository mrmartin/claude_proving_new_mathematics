/-
**Track A1 warm-ups for Erdős 64.**

Three concrete small graphs satisfying the Erdős–Gyárfás conclusion.

* `K₄ = completeGraph (Fin 4)` has a 4-cycle.
* `K_{3,3} = completeBipartiteGraph (Fin 3) (Fin 3)` has a 4-cycle.
* The 3-prism (`K₃ □ K₂`) has a 4-cycle.
-/

import Erdos64.Basic

namespace Erdos64

open SimpleGraph SimpleGraph.Walk

/-! ### Warm-up 1: `K₄ = completeGraph (Fin 4)` -/

/-- The 4-cycle `0 → 1 → 2 → 3 → 0` in `K₄`. -/
def K4Cycle : (completeGraph (Fin 4)).Walk 0 0 :=
  Walk.cons (show (completeGraph (Fin 4)).Adj 0 1 by rw [top_adj]; decide) <|
  Walk.cons (show (completeGraph (Fin 4)).Adj 1 2 by rw [top_adj]; decide) <|
  Walk.cons (show (completeGraph (Fin 4)).Adj 2 3 by rw [top_adj]; decide) <|
  Walk.cons (show (completeGraph (Fin 4)).Adj 3 0 by rw [top_adj]; decide) .nil

theorem K4Cycle_length : K4Cycle.length = 4 := by rfl

theorem K4Cycle_isCycle : K4Cycle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · show K4Cycle.edges.Nodup
    unfold K4Cycle
    decide
  · show K4Cycle ≠ .nil
    unfold K4Cycle
    decide
  · show K4Cycle.support.tail.Nodup
    unfold K4Cycle
    decide

/-- `K₄` has a 4-cycle. -/
theorem K4_has_2pow_cycle : Has2PowCycle (completeGraph (Fin 4)) :=
  has_2pow_cycle_of_has_C4 _ ⟨0, K4Cycle, K4Cycle_isCycle, K4Cycle_length⟩

/-! ### Warm-up 2: `K_{3,3} = completeBipartiteGraph (Fin 3) (Fin 3)` -/

/-- Local `DecidableRel` for `completeBipartiteGraph`. -/
private instance K33_decAdj : DecidableRel
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj := fun u v => by
  show Decidable (u.isLeft ∧ v.isRight ∨ u.isRight ∧ v.isLeft)
  infer_instance

/-- The 4-cycle `inl 0 → inr 0 → inl 1 → inr 1 → inl 0` in `K_{3,3}`. -/
def K33Cycle : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk
    (Sum.inl (0 : Fin 3)) (Sum.inl (0 : Fin 3)) :=
  Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) by decide) <|
  Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inr (0 : Fin 3)) (Sum.inl (1 : Fin 3)) by decide) <|
  Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl (1 : Fin 3)) (Sum.inr (1 : Fin 3)) by decide) <|
  Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inr (1 : Fin 3)) (Sum.inl (0 : Fin 3)) by decide) .nil

theorem K33Cycle_length : K33Cycle.length = 4 := by rfl

theorem K33Cycle_isCycle : K33Cycle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · show K33Cycle.edges.Nodup; unfold K33Cycle; decide
  · show K33Cycle ≠ .nil; unfold K33Cycle; decide
  · show K33Cycle.support.tail.Nodup; unfold K33Cycle; decide

theorem K33_has_2pow_cycle :
    Has2PowCycle (completeBipartiteGraph (Fin 3) (Fin 3)) :=
  has_2pow_cycle_of_has_C4 _ ⟨_, K33Cycle, K33Cycle_isCycle, K33Cycle_length⟩

/-! ### Warm-up 3: the 3-prism (`K₃ □ K₂`)

A cubic graph on 6 vertices: two triangles `A0,A1,A2` and `B0,B1,B2`
connected by a perfect matching `Aᵢ ↔ Bᵢ`. -/

/-- Vertices of the 3-prism. -/
inductive Prism3
  | A (i : Fin 3)
  | B (i : Fin 3)
deriving DecidableEq, Repr, Fintype

namespace Prism3

/-- Edges of the 3-prism. -/
def Adj' : Prism3 → Prism3 → Prop
  | A i, A j => i ≠ j
  | B i, B j => i ≠ j
  | A i, B j => i = j
  | B i, A j => i = j

instance : DecidableRel Adj'
  | A _, A _ => inferInstanceAs (Decidable (_ ≠ _))
  | B _, B _ => inferInstanceAs (Decidable (_ ≠ _))
  | A _, B _ => inferInstanceAs (Decidable (_ = _))
  | B _, A _ => inferInstanceAs (Decidable (_ = _))

/-- The 3-prism as a `SimpleGraph`. -/
def G : SimpleGraph Prism3 where
  Adj := Adj'
  symm := by
    intro u v h
    cases u <;> cases v <;> simp [Adj'] at h ⊢ <;> omega
  loopless := ⟨by intro v h; cases v <;> simp [Adj'] at h⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (Adj' u v))

end Prism3

/-- The 4-cycle `A0 → A1 → B1 → B0 → A0` in the 3-prism. -/
def Prism3Cycle : Prism3.G.Walk (.A 0) (.A 0) :=
  Walk.cons (show Prism3.G.Adj (.A 0) (.A 1) by decide) <|
  Walk.cons (show Prism3.G.Adj (.A 1) (.B 1) by decide) <|
  Walk.cons (show Prism3.G.Adj (.B 1) (.B 0) by decide) <|
  Walk.cons (show Prism3.G.Adj (.B 0) (.A 0) by decide) .nil

theorem Prism3Cycle_length : Prism3Cycle.length = 4 := by rfl

theorem Prism3Cycle_isCycle : Prism3Cycle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · show Prism3Cycle.edges.Nodup; unfold Prism3Cycle; decide
  · show Prism3Cycle ≠ .nil; unfold Prism3Cycle; decide
  · show Prism3Cycle.support.tail.Nodup; unfold Prism3Cycle; decide

theorem prism3_has_2pow_cycle : Has2PowCycle Prism3.G :=
  has_2pow_cycle_of_has_C4 _ ⟨_, Prism3Cycle, Prism3Cycle_isCycle, Prism3Cycle_length⟩

end Erdos64

#print axioms Erdos64.K4_has_2pow_cycle
#print axioms Erdos64.K33_has_2pow_cycle
#print axioms Erdos64.prism3_has_2pow_cycle
