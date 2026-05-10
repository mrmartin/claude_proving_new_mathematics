/-
Bridge from `Erdos198.Gist.erdos_198` (the plby/Alexeev v4.24.0 file, ported to
v4.28.0 in `Erdos198.Proof`) to the upstream `formal-conjectures` declaration
`Erdos198.erdos_198`. The upstream uses FCM's `IsSidon` (symmetric form);
plby uses a locally-defined `IsSidon` (normalised under `a ≤ b ∧ c ≤ d`).
The two are logically equivalent on ℕ.

This bridge reproduces upstream's `IsSidon` and `Set.IsAPOfLength` verbatim
from `FormalConjecturesForMathlib/Combinatorics/Basic.lean` and `.../AP/Basic.lean`,
proves `plby.IsSidon → upstream.IsSidon` (the only direction needed), and
composes through `Gist.erdos_198`.
-/

import Erdos198.Proof
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical Pointwise

namespace Erdos198

/-- Local re-implementation of the upstream `answer( )` macro. -/
macro "answer(" t:term ")" : term => `($t)

/-- Upstream FCM `IsSidon` (symmetric form). -/
def IsSidon (A : Set ℕ) : Prop := ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- Upstream FCM `Set.IsAPOfLengthWith`. -/
def Set.IsAPOfLengthWith (s : Set ℕ) (l : ℕ∞) (a d : ℕ) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- Upstream FCM `Set.IsAPOfLength`. -/
def Set.IsAPOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
  ∃ a d : ℕ, Set.IsAPOfLengthWith s l a d

/--
Predicate bridge: plby's normalised `IsSidon` implies upstream's symmetric
`IsSidon`. Proof: WLOG `i₁ ≤ i₂` and `j₁ ≤ j₂`; apply plby's; otherwise
swap.
-/
private lemma gist_isSidon_imp {A : Set ℕ} (h : Gist.IsSidon A) : IsSidon A := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  rcases le_or_gt i₁ i₂ with h₁ | h₁
  · rcases le_or_gt j₁ j₂ with h₂ | h₂
    · -- both normalised; apply plby directly
      exact Or.inl (h i₁ hi₁ i₂ hi₂ j₁ hj₁ j₂ hj₂ h₁ h₂ hsum)
    · -- need to swap j₁, j₂
      have h₂' : j₂ ≤ j₁ := le_of_lt h₂
      have hsum' : i₁ + i₂ = j₂ + j₁ := by linarith
      exact Or.inr (h i₁ hi₁ i₂ hi₂ j₂ hj₂ j₁ hj₁ h₁ h₂' hsum')
  · -- need to swap i₁, i₂
    have h₁' : i₂ ≤ i₁ := le_of_lt h₁
    have hsum' : i₂ + i₁ = j₁ + j₂ := by linarith
    rcases le_or_gt j₁ j₂ with h₂ | h₂
    · have := h i₂ hi₂ i₁ hi₁ j₁ hj₁ j₂ hj₂ h₁' h₂ hsum'
      exact Or.inr ⟨this.2, this.1⟩
    · have h₂' : j₂ ≤ j₁ := le_of_lt h₂
      have hsum'' : i₂ + i₁ = j₂ + j₁ := by linarith
      have := h i₂ hi₂ i₁ hi₁ j₂ hj₂ j₁ hj₁ h₁' h₂' hsum''
      exact Or.inl ⟨this.2, this.1⟩

/-- The upstream `Set.IsAPOfLength` matches the gist's definitionally. -/
private lemma set_isAPOfLength_eq_gist (Y : Set ℕ) (l : ℕ∞) :
    Set.IsAPOfLength Y l ↔ Gist.IsAPOfLength Y l := by
  unfold Set.IsAPOfLength Set.IsAPOfLengthWith Gist.IsAPOfLength Gist.IsAPOfLengthWith
  rfl

/--
**Erdős Problem 198** (upstream signature, restated under our v4.28.0 mathlib pin).
Statement matches `formal-conjectures/FormalConjectures/ErdosProblems/198.lean`
character-for-character: every Sidon set in `ℕ` misses some infinite AP.
-/
theorem erdos_198 : (∀ A : Set ℕ, IsSidon A → (∃ Y, Set.IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ)) ↔
    answer(False) := by
  constructor
  · intro h_upstream
    apply Gist.erdos_198.mp
    intro A hA_plby
    -- We need ∃ Y, Gist.IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ from
    -- ∀ A, upstream.IsSidon → ∃ Y, Set.IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ.
    -- Upstream needs upstream.IsSidon; the gist gives plby.IsSidon. Bridge with gist_isSidon_imp.
    obtain ⟨Y, hY_AP, hY_subset⟩ := h_upstream A (gist_isSidon_imp hA_plby)
    exact ⟨Y, (set_isAPOfLength_eq_gist Y ⊤).mp hY_AP, hY_subset⟩
  · intro h
    exact h.elim

end Erdos198
