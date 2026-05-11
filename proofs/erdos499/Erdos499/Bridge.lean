/-
Bridge: wrap plby/Aristotle's `Erdos499.erdos_499` in the upstream
`answer(True) ↔ ...` shape used by `formal-conjectures`.

Upstream signature:

  lemma erdos_499 :
      answer(True) ↔ (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n),
        ∃ σ : Equiv.Perm (Fin n), n ^ (- n : ℤ) ≤ ∏ i, M i (σ i))

`answer(True)` elaborates to `True`, so the iff is equivalent to the
RHS. plby's `erdos_499` already proves the RHS directly.
-/

import Erdos499.Proof
import Mathlib

namespace Erdos499Bridge

/-- Bridge theorem in the exact upstream shape. -/
theorem erdos_499_bridge :
    True ↔ (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n),
      ∃ σ : Equiv.Perm (Fin n), n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) :=
  ⟨fun _ => Erdos499.erdos_499, fun _ => trivial⟩

end Erdos499Bridge

-- Axiom check
#print axioms Erdos499Bridge.erdos_499_bridge
