/-
Local copy of the Wu/Aristotle Lean formalisation of Somani's disproof of
Erdős Problem 397.

Original source: https://gist.github.com/llllvvuu/40d68cfa9de9f43eece07ff4fdc3b0ef
Original generation header (preserved):
  Lean version: leanprover/lean4:v4.24.0
  Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
  This project request had uuid: 85bb77a4-160d-4c93-b255-24aea4451e62

Verbatim port to mathlib v4.28.0, wrapped in `namespace Erdos397.Gist` so the
bridge file in this same project can prove the upstream `Erdos397.erdos_397`
signature alongside (without symbol clashes on `c`, `is_solution`, etc.).
The mathematical content and proof tactics are unchanged.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Erdos397
namespace Gist

noncomputable section

/--
Define `c a = 8 a² + 8 a + 1`, the third index in Somani's family.
-/
def c (a : ℕ) : ℕ := 8 * a^2 + 8 * a + 1

/--
The product of central binomial coefficients for indices `a, 2a+2, c a`
equals the product for indices `a+1, 2a, c a + 1`.
-/
theorem central_binom_identity (a : ℕ) (h : a ≥ 2) :
  Nat.centralBinom a * Nat.centralBinom (2 * a + 2) * Nat.centralBinom (c a) =
  Nat.centralBinom (a + 1) * Nat.centralBinom (2 * a) * Nat.centralBinom (c a + 1) := by
    have h_simp : (Nat.choose (2 * a) a : ℚ) / (Nat.choose (2 * (a + 1)) (a + 1) : ℚ) * (Nat.choose (2 * (2 * a + 2)) (2 * a + 2) : ℚ) / (Nat.choose (2 * (2 * a)) (2 * a) : ℚ) * (Nat.choose (2 * (c a)) (c a) : ℚ) / (Nat.choose (2 * (c a + 1)) (c a + 1) : ℚ) = 1 := by
      have h_ratios : (Nat.choose (2 * a) a : ℚ) / (Nat.choose (2 * (a + 1)) (a + 1) : ℚ) = (a + 1) / (2 * (2 * a + 1)) ∧
                       (Nat.choose (2 * (2 * a + 2)) (2 * a + 2) : ℚ) / (Nat.choose (2 * (2 * a)) (2 * a) : ℚ) = (2 * (4 * a + 3) * (4 * a + 1)) / ((a + 1) * (2 * a + 1)) ∧
                       (Nat.choose (2 * (c a)) (c a) : ℚ) / (Nat.choose (2 * (c a + 1)) (c a + 1) : ℚ) = (c a + 1) / (2 * (2 * c a + 1)) := by
                         refine' ⟨ _, _, _ ⟩;
                         · rw [ div_eq_div_iff ] <;> norm_cast <;> norm_num [ Nat.succ_mul_choose_eq ];
                           · have := Nat.succ_mul_choose_eq ( 2 * a ) a; have := Nat.succ_mul_choose_eq ( 2 * a + 1 ) a; have := Nat.succ_mul_choose_eq ( 2 * a + 2 ) ( a + 1 ) ; norm_num [ Nat.choose_succ_succ, mul_add ] at * ; linarith;
                           · exact ne_of_gt <| Nat.choose_pos <| by linarith;
                         · rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
                           norm_num [ two_mul, Nat.factorial ];
                           field_simp
                           ring;
                           rw [ show 2 + a * 4 = a * 4 + 2 by ring ] ; norm_num [ Nat.factorial_succ ] ; ring;
                         · rw [ div_eq_div_iff ] <;> norm_cast <;> norm_num [ Nat.succ_mul_choose_eq ];
                           · have := Nat.succ_mul_choose_eq ( 2 * c a ) ( c a ) ; ( have := Nat.succ_mul_choose_eq ( 2 * c a + 1 ) ( c a ) ; ( norm_num [ Nat.choose_succ_succ, Nat.mul_succ ] at * ; nlinarith; ) );
                           · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ show c a ≥ 0 from Nat.zero_le _ ] ;
      simp_all +decide only [mul_div_assoc];
      field_simp [c] at *;
      rw [ show c a = 8 * a ^ 2 + 8 * a + 1 by rfl ] ; push_cast ; ring;
    field_simp at h_simp;
    rw [ div_eq_iff ] at h_simp <;> norm_cast at * <;> aesop

/--
A pair of lists of naturals `(M, N)` is a solution if all elements (across
both lists, treated as a multiset) are distinct and the products of central
binomials match.
-/
def is_solution (M N : List ℕ) : Prop :=
  (M ++ N).Nodup ∧
  (M.map Nat.centralBinom).prod = (N.map Nat.centralBinom).prod

/--
Somani's family of solutions, parameterised by `a ∈ ℕ` (and used for `a ≥ 2`).
-/
def sol_family (a : ℕ) : List ℕ × List ℕ := ([a, 2 * a + 2, c a], [a + 1, 2 * a, c a + 1])

/-- For `a ≥ 2`, `sol_family a` is a valid solution. -/
theorem sol_family_is_solution (a : ℕ) (h : a ≥ 2) : is_solution (sol_family a).1 (sol_family a).2 := by
  constructor <;> norm_num [ sol_family ];
  · unfold c; omega;
  · convert central_binom_identity a h using 1 <;> ring

/--
The set of `(M, N) : List ℕ × List ℕ` satisfying `is_solution` is infinite.
-/
theorem infinite_solutions : Set.Infinite { s : List ℕ × List ℕ | is_solution s.1 s.2 } := by
  have h_infinite : Set.Infinite {s | ∃ a ≥ 2, s = (sol_family a)} := by
    exact Set.infinite_of_injective_forall_mem ( fun a b h => by cases h; aesop ) fun n => ⟨ n + 2, by linarith, rfl ⟩;
  exact h_infinite.mono fun s hs => by obtain ⟨ a, ha, rfl ⟩ := hs; exact sol_family_is_solution a ha;

end

end Gist
end Erdos397
