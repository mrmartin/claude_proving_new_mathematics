# Erdős 64 / Track B1 — counterexample search infrastructure (B1.0)

**Kind:** infra
**Status:** B1.0 shipped (named-graph computational check). B1 full
deferred pending external SAT tooling.
**Date:** 2026-05-11
**Related:** 0031 (Erdős 64 target), 0038 (Petersen Lean
verification), plan at `~/.claude/plans/zesty-launching-origami.md`
(Track B1).

## 2×2 cell

Goal-3-adjacent. The infrastructure itself isn't mathematical
content; it's the search machinery that could *plausibly* find a
counterexample (= solve Erdős 64 negatively) or extend Markstrom
2004's empirical bound.

## What this commit ships

`proofs/erdos64/Search/`:

- `check_cubic.py` — verify Erdős 64 for a named list of small
  cubic graphs using `networkx`. Iterates K₄, K₃,₃, 3-prism, Q₃,
  Petersen, 5-prism, Möbius–Kantor, Heawood, Pappus, Desargues, and
  the Tutte (46-vertex) graph. For each: checks the cubic property
  and finds the smallest `2^k` cycle. Output:

  ```
  K_4                     4     YES  length 4 = 2^2
  K_{3,3}                 6     YES  length 4 = 2^2
  3-prism                 6     YES  length 4 = 2^2
  Q_3 (3-cube)            8     YES  length 4 = 2^2
  Petersen               10     YES  length 8 = 2^3
  5-prism                10     YES  length 4 = 2^2
  Möbius-Kantor          16     YES  length 8 = 2^3
  Heawood                14     YES  length 8 = 2^3
  Pappus                 18     YES  length 8 = 2^3
  Desargues              20     YES  length 8 = 2^3
  Tutte (46v)            46     YES  length 4 = 2^2
  ```

  All pass. No candidate counterexample.

- `README.md` — documents B1.0 (what's here) and B1 full (what
  needs `nauty` + `kissat`/`cadical`, currently not installed).

## Why "B1.0", not "B1 full"

The full B1 plan requires:

1. **`nauty` / `geng -d3 -D3`** for exhaustive cubic-graph
   enumeration on `n ∈ {10, …, 60}` vertices.
2. **A SAT encoder** for the per-graph `C_{2^k}`-existence query.
3. **`kissat` or `cadical`** SAT solver.

None of these are installed in the current environment. Installing
them is straightforward (`apt install nauty cadical`) but out of
scope for the current session. The B1.0 deliverable is the
sub-pipeline that can run *now* with `networkx` alone, on a
hand-curated list of named graphs.

## What's substantively new

Beyond the Lean A4 module (which verifies a single named graph,
Petersen), this script verifies *11 named cubic graphs*
computationally. Each pass is an additional data point — no Lean
verification cost. The pass-set includes every well-known small
cubic graph relevant to the Markstrom 2004 bound for `n ≤ 20`.

## Why we run this *and* the Lean A4 version

The two pipelines play different roles:

- **`check_cubic.py`** (this directory): cheap, batch, *empirical*.
  Catches obvious counterexample candidates fast. Output is a
  Python report, not a Lean theorem.
- **`Markstrom.lean`** (`Erdos64/Markstrom.lean`): expensive,
  per-graph, *certified*. Once a candidate counterexample appears,
  encode it in Lean for a kernel-checked certificate.

When the full B1 pipeline lights up, `check_cubic.py` becomes the
*first filter*; SAT runs become the *second filter*; Lean
verification becomes the *certifier*. Only the certifier produces a
publishable counterexample.

## Honest-language reminder

This commit does **not** progress Erdős 64. It is search
*infrastructure*. The headline outcome of running the full B1
pipeline could be:

- **Null result** (most likely): every cubic graph on `n ≤ 60`
  satisfies Erdős 64 → extends Markstrom 2004's bound to `n ≤ 60`.
  *Partial progress*.
- **Candidate counterexample** (very unlikely but possible): a
  cubic graph that fails. *Would solve Erdős 64 negatively after
  quadruple-checking and Lean certification.*

## Next

- **B1.1**: install `nauty` + `cadical` and run the full pipeline
  on `n = 10`, `n = 12` (small, exhaustive). Calibrate.
- **B1.2**: scale to `n = 14, 16, 18, 20` (already covered
  empirically by computational record; serves to validate our
  pipeline).
- **B1.3**: push to `n = 22, …, 30` (within Markstrom's bound; null
  result confirms the pipeline).
- **B1.4**: `n = 32, 34, …, 60` (frontier; this is where a
  candidate might live).
