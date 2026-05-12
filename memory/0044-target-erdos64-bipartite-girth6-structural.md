# Erdős 64 / Phase 3B — bipartite cubic girth-6: structural target

**Kind:** target
**Status:** in-progress (target memo); proof attempts queued post-3A.
**Date:** 2026-05-12
**Related:** 0036 (open sub-case), 0043 (Phase 3A empirical), plan
at `~/.claude/plans/zesty-launching-origami.md`.

## The structural conjecture

> Let `G` be a finite bipartite cubic graph with `G.girth = 6`.
> Then `G` contains a cycle of length 8.

If true, this discharges the `h_girth_6_case` hypothesis of our
shipped `Erdos64.has_2pow_cycle_of_isBipartite_girth_le_eight`,
collapsing that conditional theorem into an unconditional Lean-
verified sub-case of Erdős 64.

## Evidence so far

**Empirical (Phase 3A).** All 43 bipartite cubic girth-6 graphs on
`n ∈ {14, 16, 18, 20, 22}` contain a `C_8`. See memo 0043. The
search is in flight for `n ∈ {24, 26, 28, 30, 32}`.

**Literature.** I am not aware of a published statement of this
specific sub-case for the cubic case at small `n`.
Nowbandegani–Esfandiari 2011 [NoEs11] proves any *bipartite*
counterexample to Erdős–Gyárfás has `n ≥ 32`, but does not
specifically address girth-6.

## Attempted BFS-layer / Moore-bound argument (sketch + obstacle)

Let `G` be bipartite cubic, girth 6, vertex `v`. By bipartiteness +
girth-6:

- Layer 0: `{v}` (size 1).
- Layer 1: `N(v)` (size 3, in opposite part of `v`).
- Layer 2: 6 vertices.
  - **Why exactly 6:** each layer-1 vertex `u` has degree 3; one
    neighbour is `v`, the other two go to layer 2 (cannot stay in
    layer 1, since layer 1 vertices are in the same part, hence
    non-adjacent). No two layer-1 vertices share a layer-2
    neighbour (else `u_i — w — u_j — v — u_i` is a 4-cycle,
    contradicting girth 6). Hence `|layer 2| = 2 · 3 = 6`.
- Layer 3: each layer-2 vertex has 2 unvisited neighbours; possible
  overlap counted by girth-6 constraints.

For a `C_8` from `v`, the vertices alternate: `v` (A), then
B, A, B, A, B, A, B. The first and last "B"s must be in `N(v)`
(adjacent to `v`); the middle "A"s and "B"s must be at distances
≤ 4 from `v`, and bipartite parity forces them to be in even/odd
layers respectively.

**Where the argument stalls.** A `C_8` from `v` requires three
distinct layer-1 vertices on the cycle (positions 1, *3 or 5*, and
7). The candidate "middle position" is forced to come from the
*third* `N(v)` neighbour, and the structural constraints (girth-6
forbidding 4-cycles, bipartiteness forbidding odd-length local
closures) prune most placements. A case-bash on which layer the
mid-cycle vertices belong to (layer 2 vs layer 4) closes some
sub-cases but leaves a residual where the cycle would need to
traverse layer 4 and return — and girth-6 doesn't immediately rule
that out.

The structural BFS argument is *not* an immediate proof; the
empirical claim *could* be specific to small `n`.

## Sub-targets for the Lean proof

If we eventually close the structural argument in
`proofs/erdos64/Erdos64/BipartiteCubicGirth6.lean`:

1. **BFS-layer cardinality lemma**: layers 1 and 2 have sizes 3 and
   6 respectively. ≈ 80 lines.
2. **No layer-1-internal edges**: bipartite + same-part forbids. ≈ 30
   lines.
3. **No two layer-1 vertices share a layer-2 neighbour**: girth-6
   forbids the resulting `C_4`. ≈ 40 lines.
4. **Case analysis on `C_8` placement**: position 3 vs position 5
   being layer 1 vs layer 3. ≈ 200 lines.
5. **Construction in each surviving case**: explicit walk via
   `cons_isCycle_iff`. ≈ 100 lines.

Total ≈ 450 lines, assuming the structural argument closes.

## Alternative: classify failure-candidates

Push Phase 3A to `n = 32`. If empirical holds:

- Ship `theorem bipartite_cubic_girth6_has_C8_up_to_32 : ∀ G, ...`
  with the per-`n` certificates encoded à la `Markstrom.lean`. ~150
  lines per `n` × 5 levels = 750 lines (heavy, but routine).
- This discharges the `h_girth_6_case` premise for `n ≤ 32`,
  shipping a conditional-becomes-unconditional Lean theorem for
  that range.

If empirical *fails* on some `n ≤ 32`:

- The failing graph is a candidate counterexample to **Erdős 64
  itself** (after checking `C_16`, `C_32` also absent — same
  graph, additional SAT call). Quadruple-check before any
  "counterexample" language.

## Stop conditions

- Empirical search clean to `n = 32` → start the structural attack
  in earnest (Phase 3B Lean attempt). Time-box: 2 weeks.
- Empirical search finds a candidate → halt all forward work,
  enter quadruple-check protocol per the 4-phase plan.
- Structural attack hits BFS-layer dead-end at `n ≥ 4` levels →
  donate the cardinality lemmas to Track C and memo a `fail-*`.

## Honest framing

Phase 3B's structural attempt would be a **net-new sub-case proof
of an open conjecture** if it closes — a strong-claim deliverable.
The empirical Phase 3A is supporting evidence and a fallback. The
parent Erdős 64 itself stays open in either outcome unless a
counterexample emerges.
