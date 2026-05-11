# Erdős 64 — `Markstrom.lean`: Petersen graph verified

**Kind:** proof
**Status:** shipped (local), partial — Petersen done; Heawood and
Möbius–Kantor queued.
**Date:** 2026-05-11
**Related:** 0031 (target), 0033 (warmups), plan at
`~/.claude/plans/zesty-launching-origami.md`.

## 2×2 cell

Goal-3-adjacent partial result on the open conjecture. Verifying the
conjecture for a specific named graph is not progress on the general
problem, but it is a concrete sanity check and a useful entry in the
Markstrom-style catalogue.

## What this commit ships

`proofs/erdos64/Erdos64/Markstrom.lean` (~95 lines):

- `Petersen.V`: `inductive V | O (i : Fin 5) | I (i : Fin 5)` —
  10 vertices, outer and inner.
- `Petersen.Adj'`: pattern-match adjacency. Outer: 5-cycle
  `Oi ~ O(i±1 mod 5)`. Inner: pentagram `Ii ~ I(i±2 mod 5)`. Spokes
  `Oi ~ Ii`.
- `Petersen.G`: the `SimpleGraph` instance, with `symm` and
  `loopless` proved by `cases u <;> cases v <;> omega`.
- `Petersen.Cycle8`: explicit walk
  `O0 → O1 → I1 → I4 → O4 → O3 → I3 → I0 → O0` of length 8.
- `Cycle8_isCycle`: proved via `Walk.isCycle_def` + `unfold + decide`.
- `petersen_has_2pow_cycle`: `Has2PowCycle Petersen.G`.

`lake build` clean. `#print axioms petersen_has_2pow_cycle` reports
only the standard three.

## Significance

The Petersen graph is the smallest non-trivial cubic graph: 10
vertices, girth 5, vertex-transitive, edge-transitive, distance-
regular. It is the smallest example forcing the *girth-5* regime of
the Erdős–Gyárfás conjecture (no 4-cycle), and the conjecture for
Petersen is verified by exhibiting an 8-cycle = `2³`.

Markstrom 2004's lower-bound search would have hit Petersen as one
of the few cubic graphs on ≤ 10 vertices. Our verification is the
Lean-level analogue: one named graph, axiom-clean.

## Pattern for follow-up

The same template scales to:

- **Heawood graph** (14 vertices, the (3, 6)-cage, girth 6). Bipartite
  cubic; has 8-cycles. Encoding: `inductive Heawood | A (Fin 7) | B
  (Fin 7)`, `Adj'` via the Heawood incidence graph of the Fano plane.
  ~80 lines.
- **Möbius–Kantor** (16 vertices, girth 6). Vertex-transitive cubic.
  Encoding: `inductive MK | inner (Fin 8) | outer (Fin 8)` with
  appropriate skip pattern. ~80 lines.
- **The (3, 7)-cage** (24 vertices, McGee graph, girth 7). Larger.

Each instance: define `inductive V`, define `Adj'` by pattern match,
prove `symm` and `loopless`, supply `DecidableRel`, build an explicit
8-cycle walk, prove `IsCycle` via `unfold + decide`. ~80–100 lines
per graph.

## Honest framing

This commit verifies Erdős 64 *for the Petersen graph*. It does
**not** verify the conjecture for any other graph — Markstrom 2004's
30-vertex lower bound comes from a much more comprehensive search
than one named example. Our contribution here is a single
Lean-checked data point, useful as a regression check and as a
template for the rest of the Markstrom catalogue.

## Next

Per plan, move to Track B1 (SAT-counterexample search infrastructure).
Possibly add Heawood / Möbius–Kantor in a follow-up commit, sharing
this module.
