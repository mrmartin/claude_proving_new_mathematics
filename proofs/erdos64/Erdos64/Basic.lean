/-
**Basic definitions and reformulations for Erdős Problem 64 (Erdős–Gyárfás).**

Upstream statement (`formal-conjectures/FormalConjectures/ErdosProblems/64.lean`):

  ∀ (V : Type*) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
          k ≥ 2 ∧ c.IsCycle ∧ c.length = 2^k

This module establishes:

* `IsCounterexample64` — the negation: a finite graph with `minDegree ≥ 3`
  and no `2^k`-cycle for any `k ≥ 2`. Useful as a predicate for the
  per-graph theorems shipped in `WarmUp.lean`, `Markstrom.lean`, etc.
* `Has2PowCycle` — the positive existence statement on a single graph.
* `erdos64_of_has_C4` — having a 4-cycle suffices; this is the most common
  way Track A's per-graph theorems close.
* `erdos64_of_has_C8` — analogously for 8-cycles (Carr 2026 et al. use this).

Nothing here is original mathematics; this is the predicate scaffolding the
rest of the project sits on.
-/

import Mathlib

namespace Erdos64

open SimpleGraph

/-- The positive form of the Erdős 64 conclusion for a single graph: there exists
some `k ≥ 2` and a cycle of length `2^k`. -/
def Has2PowCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- A counterexample to Erdős–Gyárfás: a finite graph with `minDegree ≥ 3`
that has no cycle of length `2^k` for any `k ≥ 2`. -/
def IsCounterexample64 (V : Type*) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  G.minDegree ≥ 3 ∧ ¬ Has2PowCycle G

universe u

/-- Equivalence between the upstream universal form and the
"no counterexample exists" form, parameterised by a single universe `u`.
This is the form we'll specialise as `u = 0` for concrete `Fin n` proofs.
-/
theorem erdos64_iff_no_counterexample :
    (∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
        G.minDegree ≥ 3 → Has2PowCycle G) ↔
    (∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
        ¬ IsCounterexample64 V G) := by
  constructor
  · intro h V G _ _ ⟨hmin, hnc⟩
    exact hnc (h V G hmin)
  · intro h V G _ _ hmin
    by_contra hnc
    exact h V G ⟨hmin, hnc⟩

/-- If a graph has a 4-cycle, then it has a `2^k` cycle for some `k ≥ 2` (with `k = 2`). -/
theorem has_2pow_cycle_of_has_C4 {V : Type*} (G : SimpleGraph V)
    (h : ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 4) :
    Has2PowCycle G := by
  obtain ⟨v, c, hcyc, hlen⟩ := h
  refine ⟨2, v, c, le_refl 2, hcyc, ?_⟩
  rw [hlen]; norm_num

/-- If a graph has an 8-cycle, then it has a `2^k` cycle for some `k ≥ 2` (with `k = 3`). -/
theorem has_2pow_cycle_of_has_C8 {V : Type*} (G : SimpleGraph V)
    (h : ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 8) :
    Has2PowCycle G := by
  obtain ⟨v, c, hcyc, hlen⟩ := h
  refine ⟨3, v, c, by norm_num, hcyc, ?_⟩
  rw [hlen]; norm_num

/-- Disjunctive form used in many sub-case proofs (e.g. Carr 2026 diameter-2:
`C₄ ∨ C₈`). -/
theorem has_2pow_cycle_of_has_C4_or_C8 {V : Type*} (G : SimpleGraph V)
    (h : (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 4) ∨
         (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 8)) :
    Has2PowCycle G :=
  h.elim (has_2pow_cycle_of_has_C4 G) (has_2pow_cycle_of_has_C8 G)

end Erdos64

-- Axiom check (run on the most-used theorem so a clean build implies clean axioms).
#print axioms Erdos64.erdos64_iff_no_counterexample
