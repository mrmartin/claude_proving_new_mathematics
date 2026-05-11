/-
Step 3 of formalizing Sierpiński (1960) `infinitely_many_sierpinski`:
the CRT witness. The eight moduli `{2, 3, 5, 17, 257, 65537, 641, 6700417}`
are pairwise coprime (distinct primes), so the system

  k ≡ 1 (mod 2), 1 (mod 3), 1 (mod 5), 1 (mod 17),
  k ≡ 1 (mod 257), 1 (mod 65537), 1 (mod 641),
  k ≡ -1 (mod 6700417)

has a solution by the Chinese Remainder Theorem. We compute one explicit
witness numerically (k₀ = 15511380746462593381) and discharge each
congruence with plain `decide`. No `native_decide`.
-/

import Mathlib

namespace Erdos1113

/-- An explicit witness `k₀ = 15511380746462593381` satisfying the eight
congruences `k₀ ≡ 1 (mod p)` for `p ∈ {2, 3, 5, 17, 257, 65537, 641}` and
`k₀ ≡ -1 ≡ 6700416 (mod 6700417)`. Computed by CRT. -/
lemma exists_witness :
    ∃ k₀ : ℕ,
      k₀ % 2 = 1 ∧
      k₀ % 3 = 1 ∧
      k₀ % 5 = 1 ∧
      k₀ % 17 = 1 ∧
      k₀ % 257 = 1 ∧
      k₀ % 65537 = 1 ∧
      k₀ % 641 = 1 ∧
      k₀ % 6700417 = 6700416 :=
  ⟨15511380746462593381,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

end Erdos1113
