# Erdős 64 / Phase 4 prereq — `CycleHelpers.lean`

**Kind:** proof / infra
**Status:** shipped (local), axiom-clean.
**Date:** 2026-05-12
**Related:** 0037 (Carr 2026 deferred body), 0036 (bipartite cubic
girth-6 open sub-case), plan at
`~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-3-adjacent infrastructure. Doesn't itself advance the
conjecture, but unblocks **two** of the most valuable next-step
deliverables:

1. Carr 2026 diameter-2 case translation (Phase 4 of the plan).
2. Lean certificates for any candidate counterexample that Phase 2
   or Phase 3A turns up — once decoded to a Pikhurko-style
   `inductive V`, the explicit `C₄` / `C₈` witness uses these
   helpers.

## What this commit ships

`proofs/erdos64/Erdos64/CycleHelpers.lean` (~115 lines, axiom-clean):

- `Sym2_ne_of_pairwise_distinct` (private helper):
  `s(a,b) ≠ s(c,d)` whenever `{a, b}` and `{c, d}` are disjoint
  pairs of distinct vertices.

- `walk4`: the explicit 4-walk `a → b → c → d → a` built from four
  adjacency hypotheses.

- `walk4_length`: `(walk4 _ _ _ _).length = 4` (by `rfl`).

- `walk4_inner_isPath` (private): the inner 3-walk `b → c → d → a`
  is a path when `a, b, c, d` pairwise distinct.

- `walk4_inner_edge_not_mem` (private): the edge `s(a, b)` is not
  among the inner walk's edges.

- **`walk4_isCycle`**: given pairwise distinct `a, b, c, d` and the
  chain of edges `a ~ b ~ c ~ d ~ a`, the 4-walk is a `Walk.IsCycle`.
  Proof via `Walk.cons_isCycle_iff` + the two private helpers.

- **`has_2pow_cycle_of_chain4`**: wrapper closing through
  `has_2pow_cycle_of_has_C4` from `Basic.lean`. Six distinctness
  hypotheses + four adjacency hypotheses ⇒ `Has2PowCycle G`. The
  prime API for any future caller (Carr 2026 pre-case, counterexample
  certificates).

`lake build` clean. `#print axioms` reports only the standard three.

## Lean discipline notes

- `Walk.cons_isCycle_iff` is the right entry point: split into
  `(inner walk).IsPath ∧ s(_,_) ∉ inner.edges`. Don't try to discharge
  `Walk.IsCycle` directly via `rw [isCycle_def, isTrail_def]` plus
  generic-type `decide` (it doesn't work; `decide` can't reduce
  through an opaque vertex type).

- `Sym2.eq_iff` gives `s(a,b) = s(c,d) ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)`.
  This is the cleanest way to derive `s ≠ s'` from pairwise-distinctness:
  `intro h; rcases (Sym2.eq_iff).mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩; tauto`.
  Watch the ordering — the `(a = c ∧ b = d)` case puts `ha` and `hb`
  in *that order*, so the second case is `(a = d ∧ b = c)` which
  swaps.

- The full simp lemma set for `support.Nodup`:
  `[Walk.support_cons, Walk.support_nil, List.nodup_cons,
    List.mem_cons, List.mem_singleton, List.not_mem_nil,
    List.nodup_nil, or_false, not_or, not_false_eq_true,
    and_true]`. Less than this leaves `True ∧ X` residues that
  break refine patterns.

## Why this is Phase 4 prereq

The Carr 2026 proof (Phase 4) hits a clean "two shared neighbours
form a `C₄`" case immediately at its Pre-case. Without
`has_2pow_cycle_of_chain4`, that's a 50-line per-sub-case Lean
distraction. With the helper, the pre-case becomes a ~10-line
call. The Case 2C 8-cycle construction will need a `walk8`
analogue; not built yet.

## Next

- Build `walk8` / `has_2pow_cycle_of_chain8` (analogous, but for
  8 vertices and 8 edges). ≈ 200 lines (each pair of vertices
  generates a `Sym2` inequality; for 8 vertices that's `C(8, 2) = 28`
  pairs).
- Slot the pre-case of Carr 2026 into `DiamTwo.lean` using
  `has_2pow_cycle_of_chain4`. ≈ 30 lines.
- Continue Phase 3A empirically — Phase 4 work is parallel.
