# Erdős 64 Phase 4 Case 2C — explicit 8-cycle via `walk8_isCycle`

**Kind:** proof
**Status:** shipped
**Date:** 2026-05-12
**Related:** 0037 (Carr 2026 per-claim breakdown), 0045 (Phase 4
prereq `walk4_isCycle`), commit `bae557b`.

## Goal

Discharge **Case 2C** of Carr's 2026 diameter-2 argument
(`arXiv:2508.19302`) in Lean. Case 2C is the cleanest of the
remaining four cases because it produces an explicit 8-cycle from 8
distinct, named vertices.

## What Case 2C says (Carr 2026)

Setup (the `Case 2: zero shared neighbours` branch):

- `v₁v₂` is an edge.
- `v₃, v₄ ∈ N(v₁) \ {v₂}`, distinct.
- `v₅, v₆ ∈ N(v₂) \ {v₁}`, distinct.
- Zero shared: `{v₃,v₄} ∩ {v₅,v₆} = ∅`.
- `v₇ ∈ N(v₃) ∩ N(v₅)`, `v₇ ∉ {v₁,...,v₆}`.
- `v₈ ∈ N(v₄) ∩ N(v₆)`, `v₈ ∉ {v₃, v₅, v₇}`.

**Case 2C:** `v₈ ∉ {v₁, v₂}`, so all eight vertices are pairwise
distinct. The 8-cycle is

  `v₇ — v₃ — v₁ — v₄ — v₈ — v₆ — v₂ — v₅ — v₇`.

## What we shipped

### `Erdos64.CycleHelpers` extension (~120 lines added)

- `walk8` (already existed): the 8-cycle walk constructor.
- `walk8_inner` (new, private): the 7-walk `v₂ → v₃ → … → v₈ → v₁`.
- `walk8_inner_isPath` (new, private): support is Nodup (28
  pairwise distinctness obligations) → `IsPath`. Proof pattern
  matches `walk4_inner_isPath`: `Walk.isPath_def` + `simp` of
  `Walk.support_cons`, `List.nodup_cons`, etc., then a single
  `refine ⟨..., ..., ..., ..., ..., ..., ...⟩` discharging the
  7-fold nested conjunction.
- `walk8_inner_edge_not_mem` (new, private): the cycling edge
  `s(v₁, v₂)` is not in the inner walk's edge list (7 edges).
  Uses `Sym2_ne_of_pairwise_distinct` for the 5 "fully-disjoint"
  comparisons and manual `Sym2.eq_iff` case-split for the 2
  "shared-vertex" comparisons (s(v₁,v₂) vs s(v₂,v₃) and
  s(v₁,v₂) vs s(v₈,v₁)).
- `walk8_isCycle` (new, public): assembles via
  `Walk.cons_isCycle_iff`.
- `has_2pow_cycle_of_chain8` (new, public): convenience wrapper —
  given 8 pairwise-distinct vertices + 8 cyclic adjacencies,
  conclude `Has2PowCycle G`. Mirrors `has_2pow_cycle_of_chain4`.

All five new declarations are axiom-clean: only `[propext,
Classical.choice, Quot.sound]`.

### `Erdos64.DiamTwo` extension (~60 lines added)

- `carr2026_case_2C_eightCycle`: takes the 8 Case-2C adjacencies
  and the 28 pairwise distinctness hypotheses (in Carr's `v₁..v₈`
  labelling), reorders them to the cycle order
  `(u₁..u₈) = (v₇, v₃, v₁, v₄, v₈, v₆, v₂, v₅)`, and applies
  `has_2pow_cycle_of_chain8`.

  The 28 distinctness arguments are mapped to the cycle order via
  `.symm` where needed — the relabelling is mechanical but
  error-prone, so each `exact` is annotated with its `u_i ≠ u_j`
  meaning.

Axiom-clean.

## Current `DiamTwo.lean` status

| Case | Status |
|---|---|
| Pre-case (two shared neighbours → C₄) | ✅ `carr2026_precase_two_shared_neighbours` |
| Case 1 (one shared neighbour) | ⬜ |
| Case 2A (zero shared, v₈ = v₁) | ⬜ |
| Case 2B (zero shared, v₈ = v₂) | ⬜ |
| Case 2C (zero shared, v₈ ∉ {v₁, v₂}) | ✅ `carr2026_case_2C_eightCycle` |
| Main theorem body | `sorry` (3 cases remain) |

## Lessons

- The `walk4` template scales cleanly to `walk8` with the same
  case-bash pattern. ~120 lines vs the projected ~150 in memo 0037.
- `Sym2_ne_of_pairwise_distinct` from the original CycleHelpers is
  the right unit-of-reuse: it handles 5 of the 7 edge inequalities;
  only the two cases with a shared vertex need manual `Sym2.eq_iff`
  splitting.
- The 28-argument boilerplate in `has_2pow_cycle_of_chain8` and
  `carr2026_case_2C_eightCycle` is tedious but mechanical. A more
  polished version would package the 28 pairwise distinctness as a
  single `List.Pairwise (· ≠ ·) [v₁, ..., v₈]` hypothesis, but
  destructuring it back at the use site costs almost as many lines.
  Worth revisiting if Cases 1, 2A, 2B also end up duplicating this.
- Each `exact h_ij[.symm]` line for the 28 distinctness needs a
  one-line comment with its `u_i ≠ u_j` meaning. Without the
  comments, the reordering is unreadable.

## Next

- Cases 2A and 2B (`v₈ ∈ {v₁, v₂}` sub-cases): each is a 4-cycle
  construction (the cycle collapses to `v₁ - v₃ - v₇ - v₅ - v₂ -
  v_? - v₁` of length 6, but careful examination shows it produces
  a C₄ through a different sub-path). Carr's paper has the
  per-case sketches; ~50–100 lines each in Lean.
- Case 1 (one shared neighbour): Carr's longest case, ~250 lines
  per memo 0037. Defers indefinitely.

After all four cases close, the main `carr2026_diam_two_minDegree_three`
body can be filled by a case split on the size of `N(v₁) \ {v₂} ∩
N(v₂) \ {v₁}` (2 / 1 / 0 elements → pre-case / Case 1 / Case 2),
each branch invoking the corresponding lemma.

## Honest framing

This is **Goal-2 work, partial** (Carr 2026's diameter-2 sub-case of
Erdős 64). Carr's parent argument is published; we are translating
it to Lean. This is not a Goal-3 contribution — it does not advance
the **parent** Erdős 64 conjecture, only one of its solved sub-cases.
