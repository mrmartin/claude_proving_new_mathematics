/-
Bridge from local `Erdos1148Weaker.witness_spec` to the upstream
`Erdos1148.erdos_1148.variants.weaker` shape.

Upstream definition is

  def erdos_1148_weaker_prop (n : ℕ) : Prop :=
    ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
      (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
      (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
      (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

which is definitionally equal to our local `Weaker`. So the bridge is
trivial: `witness_spec` already has the right shape.
-/

import Erdos1148Weaker.Proof
import Mathlib

namespace Erdos1148Weaker

/-- Restate `witness_spec` in the exact form needed by the upstream
file (`erdos_1148.variants.weaker`). Equal by definition. -/
theorem upstream_weaker : ∀ n : ℕ, ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n :=
  witness_spec

end Erdos1148Weaker

#print axioms Erdos1148Weaker.upstream_weaker
