/-
Bridge from `Erdos645.Gist.erdos_645` (plby/Alexeev v4.24.0, ported in
`Erdos645.Proof`) to the upstream `formal-conjectures` `Erdos645.erdos_645`.
The gist's `erdos_645` already matches the upstream signature
character-for-character; the bridge is a one-line composition.
-/

import Erdos645.Proof
import Mathlib

namespace Erdos645

/--
**Erdős Problem 645** — every 2-colouring of `ℕ` has a monochromatic
3-AP `x, x+d, x+2d` with `d > x`. Upstream signature (unchanged).
-/
theorem erdos_645 (c : ℕ → Bool) : ∃ x d, 0 < x ∧ x < d ∧
    (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C) :=
  Gist.erdos_645 c

end Erdos645
