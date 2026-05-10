/-
Bridge from `Erdos370.Gist.erdos_370` to upstream `Erdos370.erdos_370`.
The gist's local `maxPrimeFac` definition matches FCM's
`Nat.maxPrimeFac` (`sSup {p : ℕ | p.Prime ∧ p ∣ n}`) verbatim; the
bridge restates the upstream signature with FCM's name and the
`answer(True) ↔ _` outer wrapper.
-/

import Erdos370.Proof
import Mathlib

namespace Erdos370

/-- `answer(...)` macro shim. -/
macro "answer(" t:term ")" : term => `($t)

/--
Upstream FCM `Nat.maxPrimeFac` (reproduced — identical to the gist's
`Erdos370.Gist.maxPrimeFac`).
-/
noncomputable def _root_.Nat.maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}

private lemma maxPrimeFac_eq (n : ℕ) : Nat.maxPrimeFac n = Gist.maxPrimeFac n := rfl

/--
**Erdős Problem 370** (upstream signature, restated under our v4.28.0 mathlib pin).
-/
theorem erdos_370 : answer(True) ↔
    { n | Nat.maxPrimeFac n < √n ∧ Nat.maxPrimeFac (n + 1) < √(n + 1) }.Infinite := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  have h := Gist.erdos_370.mpr trivial
  convert h using 2

end Erdos370
