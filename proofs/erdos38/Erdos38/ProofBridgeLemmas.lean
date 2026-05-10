/-
Authors: claude_proving_new_mathematics project (helpers for `Erdos38.Bridge`).
Released under Apache 2.0 license.

Helper lemmas exposing facts that the proof of
`Erdos38.Proof.constructB_not_basis` already establishes internally
(sparsity bound, h-fold sumset cardinality bound), repackaged as
self-contained public lemmas so `Erdos38.Bridge` can re-use them.
No new mathematics; pure formal-engineering plumbing.
-/

import Erdos38.Proof

open scoped BigOperators Pointwise
open Filter

namespace Erdos38

set_option maxHeartbeats 800000

/-! ## hSumset = mathlib's pointwise nsmul -/

lemma hSumset_eq_nsmul (B : Set ℕ) : ∀ h, hSumset h B = h • B
  | 0 => by
      simp only [hSumset, zero_smul]; rfl
  | h + 1 => by
      rw [hSumset, hSumset_eq_nsmul B h, succ_nsmul]

/-! ## h-fold sumset cardinality bound -/

/-- For any `B : Set ℕ`, the count of elements of the h-fold sumset that lie in
`(0, N]` is at most `(|B ∩ (0, N]| + 1)^h`.
This is the same bound proved internally inside `not_basis_of_sparse` in
`Erdos38.Proof`, repackaged as a public lemma. -/
lemma countIn_hSumset_le_pow (B : Set ℕ) (h N : ℕ) :
    countIn (hSumset h B) N ≤ (countIn B N + 1) ^ h := by
  classical
  rw [hSumset_eq_nsmul]
  -- Define the Finset of B-elements ≤ N
  set B' : Finset ℕ := (Finset.Icc 0 N).filter (fun x => x ∈ B) with hB'_def
  -- Step 1: each element of `(0,N] ∩ h • B` is in `↑(h • B')` (Finset coercion)
  have h_le : ((Finset.Ioc 0 N).filter (fun a => a ∈ h • B)).card ≤ (h • B').card := by
    refine Finset.card_le_card ?_
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
    obtain ⟨⟨ha1, ha2⟩, ha3⟩ := ha
    rw [Set.mem_nsmul_iff_sum] at ha3
    obtain ⟨f, hfB, hfsum⟩ := ha3
    -- f i ≤ a ≤ N for each i (because all summands are ≤ total in ℕ)
    have h_each_le_N : ∀ i, f i ≤ N := by
      intro i
      calc f i ≤ ∑ j, f j := Finset.single_le_sum (f := f)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = a := hfsum
        _ ≤ N := ha2
    -- So f maps into B'
    have hfB' : ∀ i, f i ∈ B' := by
      intro i
      simp only [hB'_def, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.zero_le _, h_each_le_N i⟩, hfB i⟩
    rw [show h • B' = h • B' from rfl, Finset.mem_nsmul]
    refine ⟨fun i => ⟨f i, hfB' i⟩, ?_⟩
    -- Convert ∑ to List.ofFn ... |>.sum
    rw [show (List.ofFn fun i => ((⟨f i, hfB' i⟩ : B') : ℕ)).sum =
          (List.ofFn fun i => f i).sum from rfl]
    rw [List.sum_ofFn]
    convert hfsum using 1
  refine le_trans h_le ?_
  -- Step 2: (h • B').card ≤ B'.card ^ h
  refine le_trans (Finset.card_nsmul_le) ?_
  -- Step 3: B'.card ≤ countIn B N + 1
  have h_card_B' : B'.card ≤ countIn B N + 1 := by
    -- B' = filter (· ∈ B) (Icc 0 N).  Split off 0.
    have hsplit : B' ⊆ insert 0 ((Finset.Ioc 0 N).filter (fun x => x ∈ B)) := by
      intro x hx
      simp only [hB'_def, Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨⟨_, hxN⟩, hxB⟩ := hx
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc]
      rcases Nat.eq_zero_or_pos x with rfl | hxpos
      · left; rfl
      · right; exact ⟨⟨hxpos, hxN⟩, hxB⟩
    have h1 := Finset.card_le_card hsplit
    have h2 := Finset.card_insert_le (0 : ℕ)
        ((Finset.Ioc 0 N).filter (fun x => x ∈ B))
    -- countIn B N = ((Finset.Ioc 0 N).filter (· ∈ B)).card by definition
    have h3 : countIn B N = ((Finset.Ioc 0 N).filter (fun x => x ∈ B)).card := rfl
    omega
  exact Nat.pow_le_pow_left h_card_B' h

/-! ## Sparsity of `constructB d` -/

/-- The "shifts" component of `constructB d`: union of `d.shifts m` for `m ≥ 1`. -/
def shiftSet (d : ShiftApproxData) : Set ℕ := {n | ∃ m, 0 < m ∧ n ∈ d.shifts m}

/-- `countIn (constructB d) N` is at most one more than the count of shift elements. -/
lemma countIn_constructB_le_succ (d : ShiftApproxData) (N : ℕ) :
    countIn (constructB d) N ≤ countIn (shiftSet d) N + 1 := by
  classical
  -- {a ∈ Ioc 0 N | a ∈ {1} ∪ A} ⊆ insert 1 ({a ∈ Ioc 0 N | a ∈ A})
  have hsub :
      (Finset.Ioc 0 N).filter (fun a => a ∈ constructB d) ⊆
        insert 1 ((Finset.Ioc 0 N).filter (fun a => a ∈ shiftSet d)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc, constructB,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
    obtain ⟨⟨hx0, hxN⟩, hxchoice⟩ := hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc, shiftSet,
      Set.mem_setOf_eq]
    rcases hxchoice with rfl | hxA
    · left; rfl
    · right; exact ⟨⟨hx0, hxN⟩, hxA⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le (1 : ℕ)
      ((Finset.Ioc 0 N).filter (fun a => a ∈ shiftSet d))
  have h3 : countIn (constructB d) N =
      ((Finset.Ioc 0 N).filter (fun a => a ∈ constructB d)).card := rfl
  have h4 : countIn (shiftSet d) N =
      ((Finset.Ioc 0 N).filter (fun a => a ∈ shiftSet d)).card := rfl
  omega

/-- The shift set is sparse: `(countIn (shiftSet d) N)^h / N → 0`. -/
lemma shiftSet_sparse (d : ShiftApproxData) (h : ℕ) :
    Tendsto (fun N : ℕ => (countIn (shiftSet d) N : ℝ) ^ h / N) atTop (nhds 0) := by
  classical
  -- Reduce countIn (shiftSet d) N to ((Icc 1 N).filter (∃ m, ...)).card
  have hd := d.sparse h
  refine Filter.Tendsto.congr (fun N => ?_) hd
  have h_eq : countIn (shiftSet d) N =
      ((Finset.Icc 1 N).filter (fun n => ∃ m, 0 < m ∧ n ∈ d.shifts m)).card := by
    unfold countIn shiftSet
    apply Finset.card_bij (fun a _ => a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at ha
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ha.1.1, ha.1.2⟩, ha.2⟩
    · intros; assumption
    · intro b hb
      refine ⟨b, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hb
      simp only [Finset.mem_filter, Finset.mem_Ioc, Set.mem_setOf_eq]
      exact ⟨⟨hb.1.1, hb.1.2⟩, hb.2⟩
  rw [h_eq]

/-- The constructed set `constructB d` is sparse: `(countIn (constructB d) N)^h / N → 0`. -/
lemma constructB_sparse (d : ShiftApproxData) (h : ℕ) :
    Tendsto (fun N : ℕ => (countIn (constructB d) N : ℝ) ^ h / N) atTop (nhds 0) := by
  -- countIn (constructB d) N ≤ 1 + countIn (shiftSet d) N
  have h_shift := shiftSet_sparse d
  -- (1 + countIn (shiftSet d) N)^h / N → 0 via binomial expansion
  have h_expand :
      Tendsto (fun N : ℕ => ((countIn (shiftSet d) N + 1 : ℕ) : ℝ) ^ h / N) atTop (nhds 0) := by
    have h_sum_zero : (0 : ℝ) = ∑ i ∈ Finset.range (h + 1), 0 := by simp
    have h_sum :
        Tendsto
          (fun N : ℕ => ∑ i ∈ Finset.range (h + 1),
            (Nat.choose h i : ℝ) * ((countIn (shiftSet d) N : ℝ) ^ i / N))
          atTop (nhds 0) := by
      rw [h_sum_zero]
      refine tendsto_finset_sum _ ?_
      intro i _
      simpa using (h_shift i).const_mul (Nat.choose h i : ℝ)
    refine h_sum.congr (fun N => ?_)
    push_cast
    rw [add_pow, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Squeeze
  refine squeeze_zero (fun N => by positivity) ?_ h_expand
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · apply div_le_div_of_nonneg_right _ (by exact_mod_cast Nat.zero_le N)
    exact_mod_cast Nat.pow_le_pow_left (countIn_constructB_le_succ d N) h

end Erdos38
