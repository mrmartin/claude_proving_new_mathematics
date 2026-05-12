/-
**Main theorem statement for Erdős Problem 699.**

Parthasarathy's 200-line Lean file never stated this — Bloom flagged
that the file "is not formalising anything like the statement here."
We state it locally with `sorry` to make the target explicit. Closing
this `sorry` would close Erdős #699.

The signature matches upstream
`formal-conjectures/FormalConjectures/ErdosProblems/699.lean`
(modulo the `answer(sorry) ↔ …` wrapper convention).

Per CLAUDE.md, a statement-with-`sorry` is **not** an upstream
contribution — defining-only PRs are forbidden. The point of stating
this here is exclusively to anchor the local proof effort.
-/

import Erdos699.FullyObstructed
import Erdos699.Carry
import Erdos699.CaseB
import Erdos699.Absorption
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- **Erdős Problem 699** (Erdős–Szekeres 1978). For every triple
`1 ≤ i < j ≤ n / 2`, there exists a prime `p ≥ i` such that
`p ∣ gcd(C(n, i), C(n, j))`.

The signature here is identical to upstream's
`FormalConjectures.ErdosProblems.Erdos699.erdos_699`, save for the
`answer(sorry) ↔ …` wrapper. -/
theorem erdos_699_main :
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧
        p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  sorry

end Erdos699
