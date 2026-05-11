# Erdős 64 / Track B1 — counterexample search

This directory hosts the offline computational pipeline for the
B1 stretch of the plan (`~/.claude/plans/zesty-launching-origami.md`):
*search for a small cubic graph that violates Erdős 64*. Even a null
result (everything in our search space satisfies the conjecture)
extends Markstrom 2004's 30-vertex bound.

## What's here now (B1.0)

`check_cubic.py` — verify Erdős 64 for a **named** list of small
cubic graphs (Petersen, Heawood, Möbius–Kantor, Pappus, Desargues,
…) using `networkx`. Run:

```bash
python3 check_cubic.py
```

Current output: every named graph in the list passes, with the
smallest `2^k` cycle found per graph reported. Petersen, Heawood,
Möbius–Kantor, Pappus, Desargues each have `2^3 = 8`-cycles; smaller
graphs and prisms have `2^2 = 4`-cycles.

## What's NOT here yet (B1 full)

The full B1 plan calls for **exhaustive** enumeration of cubic
graphs on `n ∈ {10, 12, …, 60}` vertices (up to isomorphism), then a
SAT-encoded check for `C_4 ∨ C_8 ∨ C_16 ∨ C_32` per graph. This
needs:

1. **`nauty` / `geng -d3 -D3 n`** (external tool, ~10 MB install).
   Generates cubic graphs on `n` vertices, one canonical form per
   isomorphism class. Output: `graph6` format, ~28 million graphs
   for `n = 30`.
2. **A SAT encoder** translating "G has a `C_L` for some `L ∈
   {4, 8, 16, 32}`" into DIMACS CNF.
3. **`kissat` or `cadical`** (modern SAT solver, ~5 MB install) to
   check satisfiability of the negation per graph.
4. **A Lean decoder** that takes a `graph6` string + a candidate
   `L`-cycle, encodes the graph as `inductive V` + `Adj'` pattern
   match in Lean, and verifies the cycle via `decide +native`.

Neither `nauty` nor a modern SAT solver is currently installed in
this environment. Path forward:

- `apt install nauty cadical` (Ubuntu) or build from source.
- Then this `Search/` directory grows three sibling scripts:
  `enumerate_cubic.sh` (calls `geng`), `encode_sat.py` (writes
  DIMACS), and `decode_to_lean.py` (translates `graph6` ↔ Lean
  encoding).

## What we'd flag

If `check_cubic.py` (or the future SAT search) finds a graph that
**fails** the `2^k` cycle check, that graph is a *candidate
counterexample to Erdős 64*. Before any memo language stronger than
"candidate, verification in progress":

1. Run a hand-check of the graph's adjacency.
2. Encode in Lean via Pikhurko-style `inductive V`.
3. Verify `IsCounterexample64 _ G` via `decide +native`.
4. *Quadruple-check* before any "counterexample" claim.

## See also

- `proofs/erdos64/Erdos64/Markstrom.lean` — Lean-verified twin of
  `check_cubic.py` for the Petersen graph (Goal-3-adjacent partial).
- Memo `0039-infra-erdos64-search-b1.md` for the design narrative.
