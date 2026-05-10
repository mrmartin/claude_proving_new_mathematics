/-
Bridge from `Erdos397.Gist.infinite_solutions` (the list-form Wu/Aristotle
proof in `Erdos397.Proof`) to the upstream `formal-conjectures` declaration

  Erdos397.erdos_397 : answer(False) ↔ <Finset-form solution set>.Finite

This file restates the upstream theorem character-for-character (under the
v4.28.0 mathlib pin) and proves it sorry-free, by constructing an explicit
injection `ℕ → S` where `S` is the upstream solution set, using Somani's
parametric family `(a+2, 2(a+2)+2, c(a+2))` vs `(a+3, 2(a+2), c(a+2)+1)`.

Mathematics: none new. Wu/Aristotle's `central_binom_identity` does all the
mathematical work; this file's contribution is purely the restatement and
the bridge to the Finset/Disjoint container form.
-/

import Erdos397.Proof
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical Nat
open Nat

namespace Erdos397

/--
Local re-implementation of the upstream `answer( )` macro: in this project we
don't carry the full `FormalConjectures.Util.Answer` infrastructure, so we
provide the simplest reduction `answer(t) = t`. For `answer(False)` this
yields exactly `False`, matching the upstream `alwaysTrue`-mode behaviour
when the placeholder is a concrete `Prop`.
-/
macro "answer(" t:term ")" : term => `($t)

/-- `Gist.c (a+2) = 8a² + 40a + 49`, expanded. -/
private lemma c_expand (a : ℕ) : Gist.c (a + 2) = 8 * a^2 + 40 * a + 49 := by
  unfold Gist.c
  ring

/-- The three indices in the first finset are pairwise distinct. -/
private lemma fst_three_distinct (a : ℕ) :
    (a + 2 ≠ 2 * (a + 2) + 2) ∧ (a + 2 ≠ Gist.c (a + 2)) ∧
    (2 * (a + 2) + 2 ≠ Gist.c (a + 2)) := by
  refine ⟨by omega, ?_, ?_⟩ <;> rw [c_expand] <;> nlinarith [sq_nonneg a, sq_nonneg (a + 1)]

/-- Same for the second finset. -/
private lemma snd_three_distinct (a : ℕ) :
    ((a + 2) + 1 ≠ 2 * (a + 2)) ∧ ((a + 2) + 1 ≠ Gist.c (a + 2) + 1) ∧
    (2 * (a + 2) ≠ Gist.c (a + 2) + 1) := by
  refine ⟨by omega, ?_, ?_⟩ <;> rw [c_expand] <;> nlinarith [sq_nonneg a, sq_nonneg (a + 1)]

private lemma not_mem_pair_fst (a : ℕ) :
    (a + 2 : ℕ) ∉ ({2 * (a + 2) + 2, Gist.c (a + 2)} : Finset ℕ) := by
  obtain ⟨h12, h13, _⟩ := fst_three_distinct a
  intro h
  rw [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact h12 h
  · exact h13 h

private lemma not_mem_singleton_fst (a : ℕ) :
    (2 * (a + 2) + 2 : ℕ) ∉ ({Gist.c (a + 2)} : Finset ℕ) := by
  obtain ⟨_, _, h23⟩ := fst_three_distinct a
  intro h
  rw [Finset.mem_singleton] at h
  exact h23 h

private lemma not_mem_pair_snd (a : ℕ) :
    ((a + 2) + 1 : ℕ) ∉ ({2 * (a + 2), Gist.c (a + 2) + 1} : Finset ℕ) := by
  obtain ⟨h12, h13, _⟩ := snd_three_distinct a
  intro h
  rw [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact h12 h
  · exact h13 h

private lemma not_mem_singleton_snd (a : ℕ) :
    (2 * (a + 2) : ℕ) ∉ ({Gist.c (a + 2) + 1} : Finset ℕ) := by
  obtain ⟨_, _, h23⟩ := snd_three_distinct a
  intro h
  rw [Finset.mem_singleton] at h
  exact h23 h

/-- Sum of the first finset has a closed form, monotone in `a`. -/
private lemma sum_fst (a : ℕ) :
    ({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)} : Finset ℕ).sum id
    = 8 * a^2 + 43 * a + 57 := by
  rw [show ({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)} : Finset ℕ)
        = insert (a + 2) (insert (2 * (a + 2) + 2) ({Gist.c (a + 2)} : Finset ℕ)) from rfl,
      Finset.sum_insert (not_mem_pair_fst a),
      Finset.sum_insert (not_mem_singleton_fst a),
      Finset.sum_singleton, c_expand]
  simp only [id]
  ring

/-- The injection `ℕ → Finset ℕ × Finset ℕ` realising Somani's family. -/
private noncomputable def F (a : ℕ) : Finset ℕ × Finset ℕ :=
  ({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)},
   {(a + 2) + 1, 2 * (a + 2), Gist.c (a + 2) + 1})

private lemma F_injective : Function.Injective F := by
  intro a b hab
  have h1 : (F a).1 = (F b).1 := congrArg Prod.fst hab
  have hsum : (F a).1.sum id = (F b).1.sum id := by rw [h1]
  rw [F, F] at hsum
  rw [sum_fst, sum_fst] at hsum
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : 8 * a ^ 2 + 43 * a < 8 * b ^ 2 + 43 * b := by nlinarith
    omega
  · have : 8 * b ^ 2 + 43 * b < 8 * a ^ 2 + 43 * a := by nlinarith
    omega

private lemma F_disjoint (a : ℕ) :
    Disjoint
      (({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)} : Finset ℕ))
      (({(a + 2) + 1, 2 * (a + 2), Gist.c (a + 2) + 1} : Finset ℕ)) := by
  rw [Finset.disjoint_left]
  intro x hM hN
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hM
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hN
  rw [c_expand] at hM hN
  rcases hM with h | h | h <;> rcases hN with h' | h' | h' <;> omega

private lemma F_prod_eq (a : ℕ) :
    ∏ i ∈ ({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)} : Finset ℕ), Nat.centralBinom i =
    ∏ j ∈ ({(a + 2) + 1, 2 * (a + 2), Gist.c (a + 2) + 1} : Finset ℕ), Nat.centralBinom j := by
  rw [show ({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)} : Finset ℕ)
        = insert (a + 2) (insert (2 * (a + 2) + 2) ({Gist.c (a + 2)} : Finset ℕ)) from rfl,
      show ({(a + 2) + 1, 2 * (a + 2), Gist.c (a + 2) + 1} : Finset ℕ)
        = insert ((a + 2) + 1) (insert (2 * (a + 2)) ({Gist.c (a + 2) + 1} : Finset ℕ)) from rfl,
      Finset.prod_insert (not_mem_pair_fst a),
      Finset.prod_insert (not_mem_singleton_fst a),
      Finset.prod_singleton,
      Finset.prod_insert (not_mem_pair_snd a),
      Finset.prod_insert (not_mem_singleton_snd a),
      Finset.prod_singleton]
  have hid := Gist.central_binom_identity (a + 2) (by omega)
  linear_combination hid

/--
**Erdős Problem 397** (upstream signature, restated under our v4.28.0 mathlib pin).

Statement matches `formal-conjectures/FormalConjectures/ErdosProblems/397.lean`
character-for-character. Proof works by constructing an explicit `ℕ`-indexed
infinite injection into the upstream solution set, using Somani's family
`(a+2, 2(a+2)+2, c(a+2))` vs `(a+3, 2(a+2), c(a+2)+1)`, with the product
equality discharged by `Erdos397.Gist.central_binom_identity`.
-/
theorem erdos_397 :
    answer(False) ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
       ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  refine ⟨fun h => h.elim, fun hfin => ?_⟩
  apply Set.not_infinite.mpr hfin
  refine Set.infinite_of_injective_forall_mem (f := F) F_injective ?_
  intro a
  exact ⟨F_disjoint a, F_prod_eq a⟩

end Erdos397
