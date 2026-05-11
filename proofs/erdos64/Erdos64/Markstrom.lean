/-
**Track A4: small named cubic graphs verified.**

Pikhurko-style encoding of specific cubic graphs, with explicit
`2^k`-cycles. Verifies the Erdős 64 conclusion for each. None of
these are claims of progress on the open conjecture — they are
concrete demonstrations that the cubic graphs the literature
references (Markstrom 2004's catalogue, the (3, g)-cages, etc.)
satisfy the conjecture, in line with our existing computational
verification capability (cf. `proofs/erdos613/Erdos613/Tao.lean`).

This module ships:

* `petersen`: the Petersen graph on 10 vertices, cubic, girth 5,
  with an explicit 8-cycle.

Heawood graph (14 vertices, girth 6) and Möbius–Kantor graph (16
vertices, girth 6) are queued for future commits; their encoding
follows the same template but expands the inductive type.
-/

import Erdos64.Basic

namespace Erdos64

open SimpleGraph SimpleGraph.Walk

/-! ### The Petersen graph -/

namespace Petersen

/-- Vertices of the Petersen graph: 5 outer + 5 inner. -/
inductive V
  | O (i : Fin 5)
  | I (i : Fin 5)
deriving DecidableEq, Repr, Fintype

/-- Adjacency in the Petersen graph: outer 5-cycle, inner pentagram
(`Ii — I(i+2 mod 5)`), and spokes `Oi — Ii`. -/
def Adj' : V → V → Prop
  | V.O i, V.O j => i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
                    (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0)
  | V.I i, V.I j => i.val + 2 = j.val ∨ j.val + 2 = i.val ∨
                    (i.val = 0 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 0) ∨
                    (i.val = 1 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 1)
  | V.O i, V.I j => i = j
  | V.I i, V.O j => i = j

instance : DecidableRel Adj' := fun u v => by
  cases u <;> cases v <;> (unfold Adj'; infer_instance)

/-- The Petersen graph as a `SimpleGraph`. -/
def G : SimpleGraph V where
  Adj := Adj'
  symm := by
    intro u v h
    cases u <;> cases v <;> (simp only [Adj'] at h ⊢; omega)
  loopless := ⟨by
    intro v h
    cases v <;> (simp only [Adj'] at h; omega)⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (Adj' u v))

/-! ### An explicit 8-cycle: O0 → O1 → I1 → I4 → O4 → O3 → I3 → I0 → O0. -/

/-- The 8-cycle `O0 → O1 → I1 → I4 → O4 → O3 → I3 → I0 → O0` in the
Petersen graph. -/
def Cycle8 : G.Walk (.O 0) (.O 0) :=
  Walk.cons (show G.Adj (.O 0) (.O 1) by decide) <|
  Walk.cons (show G.Adj (.O 1) (.I 1) by decide) <|
  Walk.cons (show G.Adj (.I 1) (.I 4) by decide) <|
  Walk.cons (show G.Adj (.I 4) (.O 4) by decide) <|
  Walk.cons (show G.Adj (.O 4) (.O 3) by decide) <|
  Walk.cons (show G.Adj (.O 3) (.I 3) by decide) <|
  Walk.cons (show G.Adj (.I 3) (.I 0) by decide) <|
  Walk.cons (show G.Adj (.I 0) (.O 0) by decide) .nil

theorem Cycle8_length : Cycle8.length = 8 := by rfl

theorem Cycle8_isCycle : Cycle8.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · show Cycle8.edges.Nodup; unfold Cycle8; decide
  · show Cycle8 ≠ .nil; unfold Cycle8; decide
  · show Cycle8.support.tail.Nodup; unfold Cycle8; decide

end Petersen

/-- **The Petersen graph satisfies Erdős 64**: it contains an 8-cycle. -/
theorem petersen_has_2pow_cycle : Has2PowCycle Petersen.G :=
  has_2pow_cycle_of_has_C8 _ ⟨.O 0, Petersen.Cycle8, Petersen.Cycle8_isCycle, Petersen.Cycle8_length⟩

end Erdos64

#print axioms Erdos64.petersen_has_2pow_cycle
