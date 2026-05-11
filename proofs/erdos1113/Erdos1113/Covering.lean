/-
Step 2 of formalizing Sierpiński (1960) `infinitely_many_sierpinski`:
the covering system of residue classes and the reduction lemma that, for
each covering prime `p`, lets us collapse `2^n (mod p)` to `2^a (mod p)`
once we know `n ≡ a (mod orderOf (2 : ZMod p))`.

The seven residue classes
  `1 mod 2, 2 mod 4, 4 mod 8, 8 mod 16, 16 mod 32, 32 mod 64, 0 mod 64`
cover every natural number; `omega` discharges the disjunction directly.
-/

import Mathlib
import Erdos1113.Orders

namespace Erdos1113

open Nat

/-! ## The seven-class covering system -/

/-- The residue classes `1 mod 2`, `2 mod 4`, `4 mod 8`, `8 mod 16`,
`16 mod 32`, `32 mod 64`, `0 mod 64` cover every natural number. -/
lemma covering_system_nat (n : ℕ) :
    n % 2 = 1 ∨ n % 4 = 2 ∨ n % 8 = 4 ∨ n % 16 = 8 ∨
    n % 32 = 16 ∨ n % 64 = 32 ∨ n % 64 = 0 := by
  omega

/-! ## Reduction `2^n = 2^(n % m)` once `orderOf 2 = m` -/

/-- If `orderOf (2 : ZMod p) = m` and `n % m = a`, then
`(2 : ZMod p) ^ n = (2 : ZMod p) ^ a`. -/
lemma two_pow_mod_of_orderOf {p : ℕ} [NeZero p] {m a : ℕ}
    (hord : orderOf (2 : ZMod p) = m) {n : ℕ} (hn : n % m = a) :
    (2 : ZMod p) ^ n = (2 : ZMod p) ^ a := by
  conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul,
    show (2 : ZMod p) ^ m = 1 from hord ▸ pow_orderOf_eq_one (2 : ZMod p)]
  simp [hn]

end Erdos1113
