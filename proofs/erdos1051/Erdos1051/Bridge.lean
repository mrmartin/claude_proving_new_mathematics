/-
Bridge from `Erdos1051.Gist.erdos_1051_irrational` (ℕ-valued) to upstream
`Erdos1051.erdos_1051` (ℤ-valued).
-/

import Erdos1051.Proof
import Mathlib

open Filter Topology

namespace Erdos1051

macro "answer(" t:term ")" : term => `($t)

def GrowthCondition (a : ℕ → ℤ) : Prop :=
  Filter.liminf (fun n => ((a n : ℝ) ^ (1 / 2 ^ n : ℝ))) Filter.atTop > 1

noncomputable def ErdosSeries (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))

private lemma strictMono_int_ge (a : ℕ → ℤ) (h : StrictMono a) (n : ℕ) :
    a 0 + n ≤ a n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : a k < a (k + 1) := h k.lt_succ_self
    push_cast
    linarith

private lemma exists_tail_ge_two (a : ℕ → ℤ) (h : StrictMono a) :
    ∃ N, ∀ n ≥ N, 2 ≤ a n := by
  refine ⟨(2 - a 0).toNat, fun n hn => ?_⟩
  have h1 := strictMono_int_ge a h n
  have h2 : ((2 - a 0).toNat : ℤ) ≥ 2 - a 0 := by
    rcases le_or_gt (2 - a 0) 0 with hh | hh
    · simp [Int.toNat_of_nonpos hh]; linarith
    · rw [Int.toNat_of_nonneg hh.le]
  have hn' : (n : ℤ) ≥ 2 - a 0 := le_trans h2 (by exact_mod_cast hn)
  linarith

theorem erdos_1051 :
    answer(True) ↔ ∀ (a : ℕ → ℤ), StrictMono a → GrowthCondition a →
      Irrational (ErdosSeries a) := by
  refine ⟨fun _ a h_mono h_growth => ?_, fun _ => trivial⟩
  -- Step 1: extract N₀.
  obtain ⟨N₀, hN₀⟩ := exists_tail_ge_two a h_mono
  -- Step 2: define b : ℕ → ℕ.
  set b : ℕ → ℕ := fun m => (a (m + N₀)).toNat with hb_def
  have ha_ge_two : ∀ m, 2 ≤ a (m + N₀) := fun m => hN₀ (m + N₀) (Nat.le_add_left N₀ m)
  have hb_int_eq : ∀ m, (b m : ℤ) = a (m + N₀) := fun m => by
    simp [hb_def, Int.toNat_of_nonneg (by linarith [ha_ge_two m] : 0 ≤ a (m + N₀))]
  have hb_real_eq : ∀ m, (b m : ℝ) = (a (m + N₀) : ℝ) := fun m => by
    have := hb_int_eq m; exact_mod_cast this
  -- Step 3: b properties.
  have hb_ge_two : ∀ m, 2 ≤ b m := fun m => by
    have : (2 : ℤ) ≤ (b m : ℤ) := by rw [hb_int_eq]; exact ha_ge_two m
    exact_mod_cast this
  have hb_pos : ∀ m, 0 < b m := fun m => by linarith [hb_ge_two m]
  have hb_mono : StrictMono b := fun m₁ m₂ h => by
    have : (b m₁ : ℤ) < (b m₂ : ℤ) := by
      rw [hb_int_eq, hb_int_eq]; exact h_mono (Nat.add_lt_add_right h N₀)
    exact_mod_cast this
  -- Step 4: shifted liminf > 1, using gist's lemma `erdos_1051_liminf_shift_pow`.
  -- Define u_safe = max 0 ((a n)^(1/2^n)), which is ∀ ≥ 0 and eventually = (a n)^(1/2^n).
  set u_safe : ℕ → ℝ := fun n => max 0 ((a n : ℝ) ^ (1 / 2 ^ n : ℝ)) with hu_safe_def
  have hu_safe_pos : ∀ n, 0 ≤ u_safe n := fun n => le_max_left _ _
  have hu_safe_eq : ∀ᶠ n in Filter.atTop, u_safe n = (a n : ℝ) ^ (1 / 2 ^ n : ℝ) := by
    refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
    have h_a_pos : (0 : ℝ) ≤ (a n : ℝ) := by
      have := hN₀ n hn; exact_mod_cast (by linarith : (0 : ℤ) ≤ a n)
    simp [hu_safe_def, max_eq_right (Real.rpow_nonneg h_a_pos _)]
  have hu_safe_liminf : 1 < Filter.atTop.liminf u_safe := by
    rw [Filter.liminf_congr hu_safe_eq]; exact h_growth
  have h_shift_pow_liminf :
      1 < Filter.atTop.liminf (fun m ↦ (u_safe (m + N₀)) ^ (2 ^ N₀ : ℝ)) :=
    Gist.erdos_1051_liminf_shift_pow u_safe hu_safe_pos hu_safe_liminf N₀
  have hb_liminf : 1 < Filter.atTop.liminf (fun m ↦ (b m : ℝ) ^ ((1 : ℝ) / 2 ^ m)) := by
    refine lt_of_lt_of_le h_shift_pow_liminf (le_of_eq ?_)
    apply Filter.liminf_congr
    refine Filter.eventually_atTop.mpr ⟨0, fun m _ => ?_⟩
    -- u_safe (m + N₀) = (a (m+N₀))^(1/2^(m+N₀)) since a (m+N₀) ≥ 0.
    have hu_eq : u_safe (m + N₀) = (a (m + N₀) : ℝ) ^ (1 / 2 ^ (m + N₀) : ℝ) := by
      have h_a_pos : (0 : ℝ) ≤ (a (m + N₀) : ℝ) := by
        have := ha_ge_two m; exact_mod_cast (by linarith : (0 : ℤ) ≤ a (m + N₀))
      simp [hu_safe_def, max_eq_right (Real.rpow_nonneg h_a_pos _)]
    rw [hu_eq, ← hb_real_eq m]
    -- ((b m : ℝ) ^ (1 / 2^(m+N₀)))^(2^N₀ : ℝ) = (b m : ℝ) ^ (1/2^m)
    rw [← Real.rpow_mul (by exact_mod_cast (hb_pos m).le)]
    congr 1
    field_simp [pow_add]
    ring
  -- Step 5: apply gist's main theorem.
  have h_gist : Irrational (∑' m, 1 / ((b m : ℝ) * (b (m + 1) : ℝ))) :=
    Gist.erdos_1051_irrational b hb_mono hb_pos hb_liminf
  -- Step 6: series decomposition.
  have hb_summable : Summable (fun m ↦ 1 / ((b m : ℝ) * (b (m + 1) : ℝ))) :=
    Gist.summable_of_ge_two b hb_mono hb_ge_two
  set f : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) with hf_def
  have h_shift : ∀ m, f (m + N₀) = 1 / ((b m : ℝ) * (b (m + 1) : ℝ)) := fun m => by
    show 1 / ((a (m + N₀) : ℝ) * (a (m + N₀ + 1) : ℝ)) = _
    rw [← hb_real_eq m]
    have : (a (m + N₀ + 1) : ℝ) = (b (m + 1) : ℝ) := by
      rw [hb_real_eq (m + 1)]; congr 1; ring
    rw [this]
  have hf_tail_summable : Summable (fun m => f (m + N₀)) := by
    refine (summable_congr ?_).mpr hb_summable
    intro m; exact h_shift m
  have hf_summable : Summable f := (summable_nat_add_iff N₀).mp hf_tail_summable
  have h_decomp : ErdosSeries a =
      (∑ n ∈ Finset.range N₀, f n) + ∑' m, 1 / ((b m : ℝ) * (b (m + 1) : ℝ)) := by
    show ∑' n, f n = (∑ n ∈ Finset.range N₀, f n) + _
    rw [← hf_summable.sum_add_tsum_nat_add N₀]
    congr 1
    exact tsum_congr h_shift
  -- Step 7: rational prefix + irrational tail = irrational.
  have h_prefix_rat : ∃ q : ℚ, (q : ℝ) = ∑ n ∈ Finset.range N₀, f n := by
    refine ⟨∑ n ∈ Finset.range N₀, 1 / ((a n : ℚ) * (a (n + 1) : ℚ)), ?_⟩
    push_cast
    rfl
  obtain ⟨q, hq⟩ := h_prefix_rat
  rw [h_decomp, ← hq]
  exact h_gist.ratCast_add q

end Erdos1051
