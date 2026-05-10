/-
Authors: claude_proving_new_mathematics project (bridge file).
Released under Apache 2.0 license.

The definitions `Set.IsWeakAddBasisOfOrder`, `Set.IsWeakAddBasis`, and the
`answer(...)` syntax are reproduced from the upstream `formal-conjectures`
repository (Copyright 2025 The Formal Conjectures Authors, Apache 2.0)
so that the restated theorem `Erdos38.erdos_38` matches the upstream
signature character-for-character.

This file bridges the locally-proved `erdos_problem_38` (in `Erdos38.Proof`,
mathlib v4.28.0) to the upstream `Erdos38.erdos_38` signature
(`formal-conjectures/FormalConjectures/ErdosProblems/38.lean`, mathlib v4.27.0).

No new mathematics is produced here — only formal-engineering plumbing
(predicate translation, cardinality coercion, and edge-case patching for
`α ∈ {0, 1}` and `N = 0`).
-/

import Erdos38.Proof
import Erdos38.ProofBridgeLemmas

open scoped BigOperators Pointwise
open Classical Real Filter

namespace Set
variable {M : Type*} [AddCommMonoid M]

/-- A set `A : Set M` is a weak additive basis of order `n` if for any element
`a : M`, it can be expressed as a sum of at most `n` elements lying in `A`. -/
def IsWeakAddBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, ∃ m ≤ n, a ∈ m • A

/-- A weak additive basis of some order. -/
def IsWeakAddBasis (A : Set M) : Prop := ∃ n, A.IsWeakAddBasisOfOrder n

end Set

/-- Standalone implementation of the upstream `answer(_)` elaborator,
sufficient for the `answer(True)` form used in `Erdos38.erdos_38`.
The upstream elaborator's `alwaysTrue` mode reduces `answer(t)` to `t`
when `t` elaborates as a term, which is exactly what this macro does. -/
syntax (name := answerMacro) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos38

/-! ## Predicate bridge — `¬ Set.IsWeakAddBasis (constructB d)` -/

/-- For sparse `B : Set ℕ` (in the sense that `(countIn B N + 1)^h / N → 0`
for every `h`), the set `B` is not a weak additive basis. -/
lemma not_isWeakAddBasis_of_sparse {B : Set ℕ}
    (hsparse : ∀ h : ℕ, Tendsto
      (fun N : ℕ => ((countIn B N + 1 : ℕ) : ℝ) ^ h / N) atTop (nhds 0)) :
    ¬ B.IsWeakAddBasis := by
  rintro ⟨n, hn⟩
  -- Goal: derive contradiction from the weak-basis hypothesis hn and sparsity hsparse.
  -- For each N: [1,N] ⊆ ⋃_{m ≤ n} hSumset m B, so N ≤ ∑ countIn (hSumset m B) N
  --             ≤ ∑ (countIn B N + 1)^m ≤ (n+1)(countIn B N + 1)^n.
  -- This contradicts (countIn B N + 1)^n / N → 0.
  have h_count_bound : ∀ N : ℕ, N ≤ (n + 1) * (countIn B N + 1) ^ n := by
    intro N
    classical
    -- |Ioc 0 N ∩ ⋃_{m ≤ n} hSumset m B| ≥ N
    have h_cover :
        (Finset.Ioc 0 N) ⊆
          (Finset.range (n + 1)).biUnion
            (fun m => (Finset.Ioc 0 N).filter (fun a => a ∈ hSumset m B)) := by
      intro a ha
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      obtain ⟨m, hmn, hm⟩ := hn a
      refine ⟨m, by omega, ha, ?_⟩
      rw [hSumset_eq_nsmul]; exact hm
    have h_card_le := Finset.card_le_card h_cover
    rw [show (Finset.Ioc 0 N).card = N by simp] at h_card_le
    refine le_trans h_card_le ?_
    refine le_trans Finset.card_biUnion_le ?_
    -- ∑_{m < n+1} countIn (hSumset m B) N ≤ ∑_{m < n+1} (countIn B N + 1)^m ≤ (n+1)*(countIn B N + 1)^n
    refine le_trans (Finset.sum_le_sum (fun m _ => countIn_hSumset_le_pow B m N)) ?_
    -- ∑_{m=0}^{n} (c+1)^m ≤ (n+1)(c+1)^n by upper bounding each term
    refine le_trans (Finset.sum_le_sum (s := Finset.range (n + 1))
      (g := fun _ => (countIn B N + 1) ^ n) (fun m hm => ?_)) ?_
    · refine Nat.pow_le_pow_right ?_ ?_
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    · simp
  -- Now derive contradiction from hsparse and h_count_bound.
  -- (countIn B N + 1)^n / N → 0, but (countIn B N + 1)^n ≥ N / (n+1) ⇒ (countIn B N + 1)^n / N ≥ 1/(n+1).
  have h_lower : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) / (n + 1) ≤ ((countIn B N + 1 : ℕ) : ℝ) ^ n / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
    have h_bound_real : (N : ℝ) ≤ (n + 1 : ℕ) * ((countIn B N + 1 : ℕ) : ℝ) ^ n := by
      exact_mod_cast h_count_bound N
    have hn1pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos _
    rw [le_div_iff₀ hN_pos]
    have hn1' : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hn1']
    rw [div_mul_eq_mul_div]
    have h_le_mul : (1 : ℝ) * (N : ℝ) ≤
        ((countIn B N + 1 : ℕ) : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) := by
      rw [one_mul, mul_comm]; exact h_bound_real
    exact (div_le_iff₀ hn1pos).mpr h_le_mul
  -- (countIn B N + 1)^n / N → 0, so eventually < 1/(n+1) (contradiction with lower bound).
  have hsp_n := hsparse n
  have h_close : ∀ᶠ N : ℕ in atTop,
      ((countIn B N + 1 : ℕ) : ℝ) ^ n / N < (1 : ℝ) / (n + 1) := by
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by
      apply div_pos one_pos
      exact_mod_cast Nat.succ_pos _
    rcases (Metric.tendsto_atTop.mp hsp_n (1 / (n + 1)) h_pos) with ⟨N₀, hN₀⟩
    refine eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩
    have := hN₀ N hN
    rw [Real.dist_eq] at this
    have h_nn : (0 : ℝ) ≤ ((countIn B N + 1 : ℕ) : ℝ) ^ n / N := by positivity
    have : |((countIn B N + 1 : ℕ) : ℝ) ^ n / N - 0| < 1 / (n + 1) := this
    rw [sub_zero, abs_of_nonneg h_nn] at this
    exact this
  obtain ⟨N, h1, h2⟩ := (h_lower.and h_close).exists
  linarith

/-- The constructed `B` is not a weak additive basis. -/
lemma not_isWeakAddBasis_constructB (d : ShiftApproxData) :
    ¬ (constructB d).IsWeakAddBasis := by
  apply not_isWeakAddBasis_of_sparse
  intro h
  -- (countIn B N + 1)^h / N → 0 from constructB_sparse via binomial expansion.
  have h_base := constructB_sparse d
  -- Want: ((countIn B N + 1 : ℕ) : ℝ)^h / N → 0
  -- ((c + 1 : ℕ) : ℝ)^h = (c + 1 : ℝ)^h = ∑_i (h choose i) * c^i
  -- Each term tendsto 0 (using h_base i for i ≤ h, base case is 1/N → 0).
  have h_zero : (0 : ℝ) = ∑ i ∈ Finset.range (h + 1), 0 := by simp
  have h_sum_zero :
      Tendsto
        (fun N : ℕ => ∑ i ∈ Finset.range (h + 1),
          (Nat.choose h i : ℝ) * ((countIn (constructB d) N : ℝ) ^ i / N))
        atTop (nhds 0) := by
    rw [h_zero]
    refine tendsto_finset_sum _ ?_
    intro i _
    simpa using (h_base i).const_mul (Nat.choose h i : ℝ)
  refine h_sum_zero.congr (fun N => ?_)
  push_cast
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Cardinality bridge -/

/-- Translation `(· + b) '' A` matches the pointwise sum `A + {b}`. -/
lemma translateSet_eq_add_singleton (A : Set ℕ) (b : ℕ) :
    translateSet A b = A + {b} := by
  ext x
  unfold translateSet
  simp

/-- Bridge between local `unionTranslateCount` and the upstream `Set.ncard` form. -/
lemma unionTranslateCount_eq_ncard (A : Set ℕ) (b N : ℕ) :
    (unionTranslateCount A b N : ℕ) = (Set.Ioc 0 N ∩ (A ∪ (A + {b}))).ncard := by
  classical
  unfold unionTranslateCount countIn
  rw [translateSet_eq_add_singleton]
  have h_eq : Set.Ioc 0 N ∩ (A ∪ (A + {b})) =
      ↑((Finset.Ioc 0 N).filter (fun a => a ∈ A ∪ (A + {b}))) := by
    ext x
    simp [Set.mem_Ioc, Finset.mem_Ioc]
  rw [h_eq, Set.ncard_coe_finset]
  apply Finset.card_bij (fun a _ => a)
  all_goals aesop

/-! ## Edge case helpers -/

private lemma mem_of_schnirelmannDensity_eq_one
    {A : Set ℕ} (hA : schnirelmannDensity A = 1) {n : ℕ} (hn : 0 < n) : n ∈ A := by
  classical
  have h := schnirelmannDensity_eq_one_iff.mp hA
  -- h : {0}ᶜ ⊆ A
  exact h (by simp [Set.mem_compl_iff, Nat.pos_iff_ne_zero.mp hn])

/-! ## Restated upstream theorem `Erdos38.erdos_38` -/

open Set in
theorem erdos_38 : answer(True) ↔
    ∃ B : Set ℕ, ¬ B.IsWeakAddBasis ∧ ∃ f : ℝ → ℝ, (∀ α, 0 < α → α < 1 → f α > 0) ∧
      ∀ (A : Set ℕ) (N : ℕ),
        let α := schnirelmannDensity A
        ∃ b ∈ B, (Ioc 0 N ∩ (A ∪ (A + {b}))).ncard ≥ (α + f α) * N := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  obtain ⟨d⟩ := shift_approx_exists
  refine ⟨constructB d, not_isWeakAddBasis_constructB d, ?_⟩
  -- Define f' that is f on (0, 1) and 0 elsewhere.
  classical
  let f' : ℝ → ℝ := fun α => if 0 < α ∧ α < 1 then erdos_f α else 0
  refine ⟨f', ?_, ?_⟩
  · -- ∀ α, 0 < α → α < 1 → f' α > 0
    intro α hα0 hα1
    show f' α > 0
    have hcond : 0 < α ∧ α < 1 := ⟨hα0, hα1⟩
    simp only [f', if_pos hcond]
    exact erdos_f_pos hα0 hα1
  · -- Density increment, with edge cases
    intro A N
    -- We need to exhibit b ∈ constructB d such that the inequality holds.
    -- Always pick b = 1 ∈ constructB d as a fallback.
    have h1_mem : (1 : ℕ) ∈ constructB d := by
      unfold constructB; left; rfl
    set α := schnirelmannDensity A with hα_def
    -- Case split.
    by_cases hN : 0 < N
    · by_cases hα0 : 0 < α
      · by_cases hα1 : α < 1
        · -- Main case: 0 < α < 1 and 0 < N — apply erdos_problem_38.
          obtain ⟨b, hbB, hb⟩ := density_increment d A N hN hα0 hα1
          refine ⟨b, hbB, ?_⟩
          show ((Set.Ioc 0 N ∩ (A ∪ (A + {b}))).ncard : ℝ) ≥ (α + f' α) * N
          have hcond : 0 < α ∧ α < 1 := ⟨hα0, hα1⟩
          have hf'_eq : f' α = erdos_f α := by simp only [f', if_pos hcond]
          rw [hf'_eq]
          rw [ge_iff_le]
          rw [show ((Set.Ioc 0 N ∩ (A ∪ (A + {b}))).ncard : ℝ) =
                  ((unionTranslateCount A b N : ℕ) : ℝ) by
            rw [unionTranslateCount_eq_ncard]]
          exact hb
        · -- α ≥ 1.  Since α ≤ 1 always, α = 1.  Then [1,N] ⊆ A so ncard = N.
          push_neg at hα1
          have hα_one : α = 1 := le_antisymm (schnirelmannDensity_le_one) hα1
          refine ⟨1, h1_mem, ?_⟩
          show ((Set.Ioc 0 N ∩ (A ∪ (A + {(1 : ℕ)}))).ncard : ℝ) ≥ (α + f' α) * N
          have hf'_zero : f' α = 0 := by
            simp only [f', hα_one]
            have : ¬ ((0 : ℝ) < 1 ∧ (1 : ℝ) < 1) := by norm_num
            rw [if_neg this]
          rw [hf'_zero, hα_one]
          have h_count_eq_N : (Set.Ioc 0 N ∩ (A ∪ (A + {(1 : ℕ)}))).ncard = N := by
            have hAcontains : ∀ n, 0 < n → n ∈ A := fun n hn =>
              mem_of_schnirelmannDensity_eq_one hα_one hn
            have h_eq : Set.Ioc 0 N ∩ (A ∪ (A + {(1 : ℕ)})) = Set.Ioc 0 N := by
              ext x
              simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_union]
              constructor
              · rintro ⟨h1, _⟩; exact h1
              · rintro ⟨hx0, hxN⟩
                refine ⟨⟨hx0, hxN⟩, Or.inl (hAcontains x hx0)⟩
            rw [h_eq]
            rw [show (Set.Ioc 0 N : Set ℕ) = ↑(Finset.Ioc 0 N) by simp]
            rw [Set.ncard_coe_finset]
            simp
          rw [h_count_eq_N, ge_iff_le]
          have hcomp : ((1 : ℝ) + 0) * (N : ℝ) = N := by ring
          rw [hcomp]
      · -- α ≤ 0.  Since α ≥ 0 always, α = 0.
        push_neg at hα0
        have hα_zero : α = 0 := le_antisymm hα0 schnirelmannDensity_nonneg
        refine ⟨1, h1_mem, ?_⟩
        show ((Set.Ioc 0 N ∩ (A ∪ (A + {(1 : ℕ)}))).ncard : ℝ) ≥ (α + f' α) * N
        have hf'_zero : f' α = 0 := by
          simp only [f', hα_zero]
          have : ¬ ((0 : ℝ) < 0 ∧ (0 : ℝ) < 1) := by norm_num
          rw [if_neg this]
        rw [hf'_zero, hα_zero]
        rw [ge_iff_le]
        have : ((0 : ℝ) + 0) * (N : ℝ) = 0 := by ring
        rw [this]
        exact_mod_cast Nat.zero_le _
    · -- N = 0
      push_neg at hN
      interval_cases N
      refine ⟨1, h1_mem, ?_⟩
      have h_zero : (Set.Ioc 0 0 ∩ (A ∪ (A + {(1 : ℕ)}))).ncard = 0 := by
        rw [show (Set.Ioc 0 0 : Set ℕ) = ∅ by ext; simp]
        rw [Set.empty_inter, Set.ncard_empty]
      rw [h_zero, ge_iff_le]
      simp

end Erdos38
