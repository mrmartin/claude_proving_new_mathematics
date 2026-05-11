/-
Step 1 of formalizing Sierpiński (1960) `infinitely_many_sierpinski`:
compute the multiplicative order of `2` modulo each of the seven covering
primes `{3, 5, 17, 257, 65537, 641, 6700417}`.

For each prime `p` and target order `2^k`, the key reduction is
`Nat.orderOf_eq_prime_pow`: if `x ^ (2 ^ (k - 1)) ≠ 1` and `x ^ (2 ^ k) = 1`,
then `orderOf x = 2 ^ k`. We discharge each premise with `decide` on `ZMod p`,
which evaluates the modular exponentiation directly.
-/

import Mathlib

namespace Erdos1113

open Nat

/-! ## Multiplicative orders of `2` modulo the seven covering primes -/

lemma orderOf_two_mod_3 : orderOf (2 : ZMod 3) = 2 ^ 1 := by
  refine orderOf_eq_prime_pow (n := 0) ?_ ?_
  · decide
  · decide

lemma orderOf_two_mod_5 : orderOf (2 : ZMod 5) = 2 ^ 2 := by
  refine orderOf_eq_prime_pow (n := 1) ?_ ?_
  · decide
  · decide

lemma orderOf_two_mod_17 : orderOf (2 : ZMod 17) = 2 ^ 3 := by
  refine orderOf_eq_prime_pow (n := 2) ?_ ?_
  · decide
  · decide

lemma orderOf_two_mod_257 : orderOf (2 : ZMod 257) = 2 ^ 4 := by
  refine orderOf_eq_prime_pow (n := 3) ?_ ?_
  · decide
  · decide

lemma orderOf_two_mod_65537 : orderOf (2 : ZMod 65537) = 2 ^ 5 := by
  refine orderOf_eq_prime_pow (n := 4) ?_ ?_
  · decide
  · decide

lemma orderOf_two_mod_641 : orderOf (2 : ZMod 641) = 2 ^ 6 := by
  refine orderOf_eq_prime_pow (n := 5) ?_ ?_
  · decide
  · decide

lemma orderOf_two_mod_6700417 : orderOf (2 : ZMod 6700417) = 2 ^ 6 := by
  refine orderOf_eq_prime_pow (n := 5) ?_ ?_
  · decide
  · decide

end Erdos1113
