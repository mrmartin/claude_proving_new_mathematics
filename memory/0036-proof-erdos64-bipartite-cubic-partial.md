# Erdős 64 — `BipartiteCubic.lean`: bipartite girth-∈-{4, 8} case

**Kind:** proof
**Status:** shipped (local), partial — girth-6 sub-case deferred.
**Date:** 2026-05-11
**Related:** 0031 (target), 0034 (bipartite cycle parity), 0035
(deferred girth-diam), plan at `~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-3-adjacent partial result on Erdős 64 (the parent is OPEN per
the HARD GATING RULE in `CLAUDE.md`).

## Scope

The plan's Track A2 milestone was *"bipartite cubic with girth ≤ 8
contains a `C₄` or `C₈`"*. The structural breakdown:

- bipartite + ¬ acyclic ⇒ girth is even (≥ 4)  *(memo 0034)*
- girth ≤ 8 ⇒ girth ∈ {4, 6, 8}
- girth = 4 ⇒ the girth cycle IS a `C₄` ✓
- girth = 8 ⇒ the girth cycle IS a `C₈` ✓
- **girth = 6 ⇒ ?** — must locate a `C₈` somewhere else in the graph.
  Not obvious; the cubic hypothesis is essential here. Deferred.

So this module ships the **two easy thirds** of A2: girth = 4 and
girth = 8. The girth = 6 case is exposed as a hypothesis to the
combining theorem, not assumed.

## Theorems shipped

`proofs/erdos64/Erdos64/BipartiteCubic.lean` (~110 lines):

- `has_2pow_cycle_of_girth_eq_four`: `¬ G.IsAcyclic ∧ G.girth = 4 ⇒
  Has2PowCycle G`. (Trivial — `exists_girth_eq_length` gives the
  cycle of length girth, then `has_2pow_cycle_of_has_C4`.)
- `has_2pow_cycle_of_girth_eq_eight`: same with `8`.
- `girth_even_of_isBipartite`: bipartite + cycle ⇒ girth even.
- `girth_eq_four_of_isBipartite_girth_le_five`: bipartite + cycle +
  girth ≤ 5 ⇒ girth = 4. Useful for diameter-2 case (where Carr 2026
  gives girth ≤ 5).
- `girth_mem_four_six_eight_of_isBipartite_girth_le_eight`:
  bipartite + cycle + girth ≤ 8 ⇒ girth ∈ {4, 6, 8}.
- `has_2pow_cycle_of_isBipartite_girth_le_five`: bipartite + cycle +
  girth ≤ 5 ⇒ `Has2PowCycle`.
- `has_2pow_cycle_of_isBipartite_girth_eq_eight`: bipartite + cycle +
  girth = 8 ⇒ `Has2PowCycle`.
- `has_2pow_cycle_of_isBipartite_girth_le_eight`: bipartite + cycle +
  girth ≤ 8 + *(hypothesis: girth = 6 case settled)* ⇒
  `Has2PowCycle`. The hypothesis surfaces the open piece.

`lake build` clean, no warnings. `#print axioms` reports only the
standard three on all three exported theorems.

## The girth-6 open case

For a bipartite cubic graph G with `girth(G) = 6`, does G have a
`C₈`?

**Sub-status of this question.** I do not know whether this is true
*in general*. The Heawood graph (the (3, 6)-cage on 14 vertices) has
8-cycles, but a generic bipartite cubic graph of girth 6 might not.
A counterexample would need:

- bipartite, cubic;
- contains a 6-cycle (so girth ≥ 6);
- contains no cycle whose length is a power of 2.

Nowbandegani-Esfandiari 2011 [NoEs11] proved any bipartite
counterexample to Erdős 64 has ≥ 32 vertices. So if a bipartite-cubic
girth-6 counterexample exists, it has ≥ 32 vertices.

This is a Track-B target: **search for bipartite cubic girth-6 graphs
on 14, 18, 22, …, 30 vertices and verify they all have a 2^k-cycle**.
If they all do, that's strong (computational) evidence for the
girth-6 sub-case. If we find one without — that's a partial
counterexample to Erdős 64 itself, settling the conjecture in the
negative direction! (Almost. We'd still need its minimum degree to be
exactly 3, which is the cubic hypothesis.)

So the girth-6 piece is the most tantalising specific Track-B target
that comes out of this module.

## What this commit does *not* claim

- Does not claim "Track A2 complete". A2 has three sub-cases (girth
  4, 6, 8); we shipped two.
- Does not claim any progress on the *general* Erdős 64.
- The `has_2pow_cycle_of_isBipartite_girth_le_eight` theorem requires
  an explicit hypothesis `girth = 6 → Has2PowCycle G` — it is a
  conditional theorem, not a free-standing one.

## Next

Per plan, move to Track A3 (`DiamTwo.lean`, Carr 2026 diameter-2
case) and/or Track B1 (SAT-counterexample search infrastructure).
The girth-6 bipartite-cubic question is now a sharp, actionable
sub-target for Track B.
