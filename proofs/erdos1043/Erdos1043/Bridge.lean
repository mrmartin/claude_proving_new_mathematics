/-
Bridge from `Erdos1043.Gist.erdos_1043` (¬-form) to upstream
`Erdos1043.erdos_1043` (`answer(False) ↔ ∀ f, ...` form). Composition:
`answer(False) ↔ X` iff `False ↔ X` iff `¬X`; the gist already proves `¬X`.
-/

import Erdos1043.Proof
import Mathlib

namespace Erdos1043

macro "answer(" t:term ")" : term => `($t)

open Polynomial MeasureTheory

/-- Local re-export of the gist's `levelSet` under the file-namespace, to
state the upstream signature without `Gist.` prefix. -/
abbrev levelSet (f : Polynomial ℂ) : Set ℂ := Gist.levelSet f

theorem erdos_1043 :
    answer(False) ↔ ∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjection '' levelSet f) ≤ 2 := by
  refine ⟨fun h => h.elim, fun h => Gist.erdos_1043 h⟩

end Erdos1043
