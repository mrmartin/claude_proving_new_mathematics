/-
Bridge from `Erdos457.Gist.erdos_457` (the Barreto/Aristotle gist's
upstream-shape theorem, in `Erdos457.Proof`) to the upstream
`formal-conjectures` declaration

  Erdos457.erdos_457 : answer(True) ↔ ∃ ε > (0 : ℝ), { ... }.Infinite

This file restates the upstream theorem character-for-character (under the
v4.28.0 mathlib pin) and proves it sorry-free, by directly composing the
gist's `erdos_457` with the trivial `answer(True) ↔ _` outer wrapping.

Mathematics: none new. The Barreto/Aristotle gist already discharges the
upstream-shape conclusion; the bridge is just the `answer(True)` shim.
-/

import Erdos457.Proof
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical Nat
open Nat

namespace Erdos457

/--
Local re-implementation of the upstream `answer( )` macro: identity
reduction `answer(t) = t`, sufficient for `answer(True)` to elaborate
as `True`.
-/
macro "answer(" t:term ")" : term => `($t)

/--
**Erdős Problem 457** (upstream signature, restated under our v4.28.0 mathlib pin).

Statement matches `formal-conjectures/FormalConjectures/ErdosProblems/457.lean`
character-for-character. The proof is a one-liner composition of the
gist's `Gist.erdos_457` with the `answer(True) ↔ _` macro shim.
-/
theorem erdos_457 : answer(True) ↔ ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  exact ⟨fun _ => Gist.erdos_457, fun _ => trivial⟩

end Erdos457
