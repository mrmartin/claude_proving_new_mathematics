# Erdős 64 — Track A3: diameter-2 case (Carr 2026)

**Kind:** target / partial-shipped
**Status:** statement + setup helper shipped; main proof body deferred.
**Date:** 2026-05-11
**Related:** 0031 (Erdős 64 target), plan at
`~/.claude/plans/zesty-launching-origami.md`, Carr 2026 PDF cached
locally.

## 2×2 cell

Goal-2 (Carr's proof exists in the literature) shipped on an open
parent (Erdős 64) — Goal-3-adjacent partial per the HARD GATING RULE
in `CLAUDE.md`.

## Theorem to formalise

**Carr 2026, Theorem 1.1** (`arXiv:2508.19302`, 12 pages):

> Let `G` be a graph with `diam(G) = 2` and `δ(G) ≥ 3`. Then `G`
> contains a cycle of length 4 or 8.

Upstream-compatible Lean shape (in
`proofs/erdos64/Erdos64/DiamTwo.lean`):

```lean
theorem carr2026_diam_two_minDegree_three
    (_hδ : 3 ≤ G.minDegree) (_hd : G.diam ≤ 2) (_hd_pos : G.diam ≠ 0) :
    Has2PowCycle G := by
  sorry
```

## What's shipped

`proofs/erdos64/Erdos64/DiamTwo.lean` (~65 lines):

- `exists_two_other_neighbours`: from `δ ≥ 3` and one edge `v₁ v₂`,
  extract two other neighbours of `v₁` distinct from `v₂` (and each
  other). Proof: `G.minDegree ≤ G.degree v₁`, so `|N(v₁)| ≥ 3`, so
  `|N(v₁) \ {v₂}| ≥ 2`. Used by every case of Carr's argument.
- `carr2026_diam_two_minDegree_three`: theorem statement, `sorry`
  body.

`lake build` clean. `#print axioms exists_two_other_neighbours`
reports only the standard three.

## Carr's proof — per-claim breakdown for the deferred body

The body of Carr's proof is a case analysis on whether `N(v₁) \ {v₂}`
and `N(v₂) \ {v₁}` share two, one, or zero common elements.

### Pre-case: two shared (immediate `C₄`)

If `|N(v₁) \ {v₂} ∩ N(v₂) \ {v₁}| ≥ 2`, the two shared neighbours
`w₁ ≠ w₂` give the 4-cycle `v₁ - w₁ - v₂ - w₂ - v₁`. Lean status:
prototype proof in an earlier draft of this file ran into
`cons_isCycle_iff` plumbing issues for *generic* `V`; deferred until
we have a `mkCycle4` helper. Estimated 50 lines once the helper is in.

### Case 1: exactly one shared neighbour (`v₃ = v₅`)

Vertex chain (Carr §Case 1): `v₁, v₂, v₃, v₄, v₆` ∈ `V(G')`, plus
new vertices `v₇` (common neighbour of `v₄, v₆`), `v₈` (common
neighbour of `v₃, v₇`), `v₉` (third neighbour of `v₈`), `v₁₀`
(common neighbour of `v₉` and one of `v₂, v₄`).

Claims 1.1–1.6 of the paper formalise as separate lemmas:
- 1.1: `v₄v₆ ∉ E(G)` (else `C₄`).
- 1.2: `v₇ ∉ {v₁, v₂, v₃}`.
- 1.3: `v₈ ∉ V(G')`.
- 1.4: `v₉ ∉ V(G')`.
- 1.5: `v₉` adj to any of `{v₁,v₂,v₄,v₆}` → `C₄`.
- 1.6: ∃ `v₁₀` in `(N(v₉) ∩ N(v₄)) ∪ (N(v₉) ∩ N(v₂))` with
  `v₁₀ ∉ ({v₇, v₈} ∪ V(G'))`.

Final cycle: `v₁₀ - v₂ - v₃ - v₁ - v₄ - v₇ - v₈ - v₉ - v₁₀` or
`v₁₀ - v₄ - v₁ - v₂ - v₆ - v₇ - v₈ - v₉ - v₁₀` (length 8).

Line budget: ~250 lines (each claim is a `decide`-friendly
contradiction from a hypothetical 4-cycle).

### Case 2: zero shared neighbours (`v₃ ≠ v₅`)

Vertex chain: `v₁, ..., v₆` (no sharing), then `v₇ ∈ N(a) ∩ N(b)`
for some `a ∈ {v₃,v₄}`, `b ∈ {v₅,v₆}`, with `v₇ ∉ V(G')`. WLOG
`a = v₃, b = v₅`. Then `v₈ ∈ N(v₄) ∩ N(v₆)`, with `v₈ ∉ {v₃,v₅,v₇}`.

Subcases:
- 2A `v₈ = v₁`: need extra `x ∈ N(v₆) ∩ N(v₇)` and
  `y ∈ N(v₄) ∩ N(v₅)`, both avoiding earlier vertices; 8-cycle
  `x - v₇ - v₅ - y - v₄ - v₁ - v₂ - v₆ - x`. Line budget ~150.
- 2B `v₈ = v₂`: symmetric to 2A. Line budget ~150 (or reuse via
  graph-automorphism `v_i ↔ v_{i±whatever}`).
- 2C `v₈ ∉ {v₁, v₂}`: direct 8-cycle
  `v₇ - v₃ - v₁ - v₄ - v₈ - v₆ - v₂ - v₅ - v₇`. Line budget ~100.

### Total estimate

~650 lines of Lean, spread over the four subcases plus the shared
helpers. Realistic 2-week effort if shared `cons_isCycle_iff` cycle-
construction infrastructure is built first (a ~150-line helper file).

## Why this is partial-shipped, not deferred outright

Two reasons:

1. The statement and the setup lemma are independently useful: the
   `exists_two_other_neighbours` helper will appear verbatim in
   Cases 1, 2A, 2B, 2C, so it's worth banking now.
2. Surfacing the theorem statement upstream-compatibly lets future
   sessions slot the proof body in without re-architecting.

## Honest framing

This is **not** a partial proof of Erdős 64. It is *infrastructure
for formalising Carr 2026's diameter-2 sub-case*, which is itself a
known-informal-proof result on an open conjecture. Goal-2-style work
shipped as Goal-3-adjacent partial.

## Next

Per plan, move to Track A4 (`Markstrom.lean`: Petersen + small named
cubic graphs) and Track B1 (SAT-counterexample search infrastructure).
Returning to fill the A3 sorries is queued for a focused 2-week
session.
