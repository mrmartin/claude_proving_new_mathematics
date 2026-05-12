/-
**Master identity for binomial coefficients** (Parthasarathy 2026 §2.4).

The identity `C(n,j) · C(j,i) = C(n,i) · C(n-i, j-i)` is the algebraic
backbone of every Case-B sub-argument. Mathlib has this as
`Nat.choose_mul`; we wrap it under `Erdos699.master_identity` for naming
continuity with Parthasarathy's paper / Lean file.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Erdos699

open Nat

/-- The master identity (Parthasarathy §2.4). Equivalent to
`Nat.choose_mul`. (Note: Mathlib's signature needs only `i ≤ j`;
`j ≤ n` is recovered automatically — for `j > n`, both sides are
zero.) -/
theorem master_identity {n i j : ℕ} (hij : i ≤ j) :
    n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) :=
  Nat.choose_mul hij

end Erdos699
