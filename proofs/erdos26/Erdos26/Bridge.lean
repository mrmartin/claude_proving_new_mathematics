/-
Bridge from plby/Aristotle's `Erdos26.erdos_26.variants.rusza` to the
upstream-shape (using `Set.HasDensity` from upstream's
`FormalConjecturesForMathlib/Data/Set/Density.lean`).

plby's file defines a local `HasDensity` (in the `Erdos26` namespace)
that is term-for-term identical to upstream's `Set.HasDensity` (modulo
the namespace placement). plby's `IsBehrend` uses plby's `HasDensity`;
upstream's `IsBehrend` uses `Set.HasDensity`. Because the underlying
`partialDensity` is the same, the two `IsBehrend` predicates are
definitionally equal, so plby's rusza theorem also closes the
upstream sorry.

This bridge re-creates upstream's `Set.HasDensity` locally (since
mathlib v4.28.0 lacks it; it lives only in upstream's
`FormalConjecturesForMathlib` extensions), defines upstream-shape
`IsBehrend`, and ships the rusza variant with that signature.
-/

import Erdos26.Proof
import Mathlib

open Filter

namespace Erdos26Bridge

open scoped Topology

/-- Same as upstream's `Set.partialDensity`. -/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Set.Iio b).ncard / (A ∩ Set.Iio b).ncard

/-- Same as upstream's `Set.HasDensity`. -/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => partialDensity S A b) atTop (𝓝 α)

/-- Same as upstream's `Erdos26.IsBehrend`. -/
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := HasDensity (Erdos26.MultiplesOf A) 1

/-- plby's `IsBehrend` agrees with our upstream-shape `IsBehrend` by definitional
unfolding: plby's local `HasDensity` and our `HasDensity` are term-for-term identical
(both reduce to `Tendsto (partialDensity (MultiplesOf A) Set.univ) atTop (𝓝 1)` with
the same `partialDensity`, modulo the local-vs-namespaced syntactic spelling). -/
lemma plby_isBehrend_iff_bridge (A : ℕ → ℕ) :
    Erdos26.IsBehrend A ↔ IsBehrend A := by
  unfold Erdos26.IsBehrend IsBehrend Erdos26.HasDensity HasDensity
  rfl

/-- The Ruzsa counterexample in upstream-shape form: a strictly monotone
sequence A with ∑ 1/A_n < ∞ such that for every shift k, the shifted set
A + k does not have density-1 multiples. -/
theorem erdos_26_variants_rusza_upstream : ∃ A : ℕ → ℕ,
    StrictMono A ∧ ¬ Erdos26.IsThick A ∧ ∀ k, ¬ IsBehrend (A · + k) := by
  obtain ⟨A, hMono, hThick, hBehrend⟩ := Erdos26.erdos_26.variants.rusza
  refine ⟨A, hMono, hThick, fun k h => hBehrend k ?_⟩
  exact (plby_isBehrend_iff_bridge _).mpr h

end Erdos26Bridge

-- Axiom check
#print axioms Erdos26Bridge.erdos_26_variants_rusza_upstream
