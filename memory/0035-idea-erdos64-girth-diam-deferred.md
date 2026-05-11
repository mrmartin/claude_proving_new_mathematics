# Erdős 64 — deferred: `girth ≤ 2 · diam + 1` mathlib gap-fill

**Kind:** idea
**Status:** deferred. Attempt aborted; partial obstruction documented
below for the next session that picks this up.
**Date:** 2026-05-11
**Related:** 0034 (the pivot to bipartite-no-odd-cycle).

## The TODO

Mathlib `Combinatorics/SimpleGraph/Girth.lean:17-21` lists:

```
## TODO
- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1`
  when the diameter is non-zero.
```

This is also Track C1 in our Erdős 64 plan
(`~/.claude/plans/zesty-launching-origami.md`).

## Textbook proof

Pick a cycle `c` realising `girth = c.length =: g` (via
`exists_girth_eq_length` once `¬ G.IsAcyclic`). Pick vertices `u, v`
on `c` at *cycle-distance* `⌊g/2⌋`. Then:

1. `G.dist u v ≤ G.diam` (when ediam is finite, via `dist_le_diam`).
2. `G.dist u v ≥ ⌊g/2⌋`. **This is the hard step.**

For (2): suppose `G.dist u v = d < ⌊g/2⌋`. Take a shortest `G`-path `P`
from `u` to `v`. Concatenate `P` with the shorter half of `c` from `v`
back to `u` (length `⌊g/2⌋`). The result is a closed walk `W` of
length `d + ⌊g/2⌋ < 2 · ⌊g/2⌋ ≤ g`. Since `g` is the girth, *every*
cycle in the graph has length `≥ g`, so the closed walk `W` of length
`< g` cannot contain any cycle — but every closed walk of length ≥ 3
*does* contain a cycle (decompose at the first repeated vertex). So
either `W.length < 3`, which contradicts `d + ⌊g/2⌋ ≥ 1 + 2 = 3` when
`g ≥ 4` (girth ≥ 3 gives at least `1 + 1 = 2`, hmm edge case), or `W`
contains a strictly shorter cycle, contradicting girth-minimality.

## The obstruction in mathlib v4.28.0

The crucial dependency is:

> Every closed walk of length ≥ 3 contains a cycle of length ≤ that
> walk's length.

Mathlib v4.28.0 has:

- `SimpleGraph.Walk.bypass : G.Walk u v → G.Walk u v` — produces an
  `IsPath`. For `u = v`, this collapses any closed walk to
  `Walk.nil`. Useless for our purposes.
- `Walk.IsCircuit` (closed walk with edges nodup) and `Walk.IsCycle`
  (also vertices nodup). No direct "circuit-to-cycle" lemma.
- `Walk.Rotate`, `Walk.dart`, `Walk.support` API for manipulating
  walks. Could be used to write the iterative shortcut argument, but
  needs ~150–200 lines and isn't a one-liner.

We attempted the proof and got blocked at this step. Pivoted to the
sister TODO (bipartite → no odd cycle, memo 0034) which avoids the
closed-walk-to-cycle dependency.

## Picking this up later

Two routes:

1. **Build the closed-walk-to-cycle helper.** Write
   `SimpleGraph.Walk.exists_isCycle_le_length` (~150 lines): given
   `w : Walk u u` with `w.length ≥ 3`, produce `(a, c : Walk a a)
   with c.IsCycle ∧ c.length ≤ w.length`. Decompose at the first
   repeated vertex (mathlib has `List.idxOf` etc. on `support`). Then
   the `girth ≤ 2·diam + 1` proof follows in ~50 lines.

2. **Find an existing proof in another mathlib-adjacent project.**
   Yaël Dillies (the `Girth.lean` author) may have a draft in a
   downstream PR. Search `leanprover-community/mathlib4` open PRs for
   "girth" / "diameter".

For our project: route (1) is preferable since the helper is itself a
reusable mathlib gap-fill. Estimate: ~1 week of focused work.

## What blocks shipping a partial result

The diameter-2 case (Track A3 / Carr 2026) could in principle be
proved without the general `girth ≤ 2·diam + 1` lemma — Carr's actual
argument is more direct (it constructs the C₄ / C₈ explicitly from
common neighbours). So Track A3 can proceed without this gap-fill.

## Stop condition

Only revisit this when:

- A Track A milestone *requires* the lemma (none so far do; Carr
  2026 works around it).
- We have ≥ 1 week of focused time available.
- The closed-walk-to-cycle helper is the priority (it's an
  independent mathlib-level contribution).
