# Erdős 64 — `Bipartite.lean`: bipartite graphs have no odd cycle

**Kind:** proof
**Status:** shipped (local). Axiom-clean.
**Date:** 2026-05-11
**Related:** 0031 (target), 0032 (skeleton), 0033 (warmups),
plan at `~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-2 (the result is folklore) shipped as a Goal-3-adjacent
**mathlib gap-fill**. The lemma feeds Track A2 (bipartite cubic
sub-case) and Track C2 (mathlib donate-back).

## Why this is a gap-fill (and a pivot)

The plan originally targeted `SimpleGraph.girth_le_two_mul_diam_add_one`
(an explicit TODO at mathlib `Girth.lean:19`). I attempted this and
ran into a dependency: the standard textbook proof needs a "closed
walk of length < girth contains a strictly shorter cycle" lemma, which
mathlib v4.28.0 does not provide directly (only `Walk.bypass`
producing a *path*, which collapses a closed walk to `Walk.nil`).
Building that closed-walk-to-cycle machinery is itself a substantial
~150–200 line task.

I pivoted to the **other** TODO in `Girth.lean`/`Bipartite.lean`:

> `Bipartite.lean:63`: "Prove that `G.IsBipartite` iff `G` does not
> contain an odd cycle."

We ship the **easy direction** (`IsBipartite → no odd cycle`), which
is the one Track A2 needs. The converse direction requires a BFS-based
coloring construction; deferred.

## What this commit ships

`proofs/erdos64/Erdos64/Bipartite.lean` (~90 lines):

- `colour_eq_iff_even` (helper): for a proper 2-colouring `C` and any
  walk `w : G.Walk u v`, `C u = C v ↔ Even w.length`. Induction on
  the walk; the `cons` step uses `C.valid` to flip colour at each
  edge, then `omega` on `Fin 2` arithmetic.
- `even_length_of_isBipartite_of_closed`: every closed walk `u → u`
  in a bipartite graph has even length.
- `IsCycle.even_length_of_isBipartite`: specialisation of the above
  to `IsCycle`.
- `not_isCycle_of_odd_length_of_isBipartite`: contrapositive form.

`lake build` clean, no warnings. `#print axioms` reports only the
standard three.

## Lean discipline

- `induction w with | nil => … | @cons a b c h_adj p ih => …` —
  use `@cons` to bind the intermediate vertices `a, b, c` explicitly.
  Initially I used `(u := u) (v := x) (w := y)` named-binders syntax,
  which conflicted with the outer `u` binding.
- `Nat.not_even_iff_odd.mp` / `.mpr` is the lemma name pair for
  flipping evenness and oddness in v4.28.0 (older
  `Nat.odd_iff_not_even` doesn't exist as a top-level name).
- The `Fin 2` case-bash at the end uses `Fin.ext` + `omega` on
  `(C a).val < 2`, `(C b).val < 2`, `(C c).val < 2` and the inequality
  hypotheses — `decide` can't reduce because `C a` is opaque.

## Why this lemma matters for Erdős 64

In a bipartite graph, every cycle has even length. So:

- A bipartite min-deg-3 graph cannot contain a 5-cycle or 7-cycle.
- Its girth (if finite) is even.
- For Track A2: a bipartite cubic graph of girth ≤ 8 has girth in
  `{4, 6, 8}`. Girth = 4 ⇒ a 4-cycle = `2²` exists. Girth = 8 ⇒
  the girth cycle itself is `8 = 2³`. Girth = 6 is the residual
  case where we need a stronger argument (BFS-layer Moore bound +
  pigeonhole). The bipartite cycle parity lemma is exactly the
  reduction that pins down the girth to `{4, 6, 8}`.

## What's NOT proved here (and queued)

- `SimpleGraph.girth_le_two_mul_diam_add_one` (original Commit 3
  target). Deferred until we have the closed-walk-to-cycle helper or
  find a slicker proof. Memo `0035-idea-mathlib-gap-girth-diam.md`
  records the partial attempt and the obstruction.
- Converse `no_odd_cycle → IsBipartite`. Needs BFS-layer coloring;
  Track C extension.

## Next

- Memo `0035` (idea): record the deferred `girth ≤ 2 · diam + 1` work.
- Track A2: start the bipartite cubic sub-case in
  `Erdos64/BipartiteCubic.lean` using the lemma proved here.
- Or push Track B (SAT-counterexample search) on a separate branch.
