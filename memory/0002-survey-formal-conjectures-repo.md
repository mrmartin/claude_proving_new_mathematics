# 0002 — `formal-conjectures` survey: structure, conventions, attack vectors

**Kind:** survey
**Status:** shipped
**Date:** 2026-05-10
**Related:** 0001
**Upstream:** https://github.com/google-deepmind/formal-conjectures

## Goal

Understand what `google-deepmind/formal-conjectures` actually is, what kinds
of contributions it accepts, where the unproven theorems live, and which
attack vector best matches Claude Code's strengths. Output: a strategic
verdict the user can ratify and that future sessions can build on without
re-reading the whole repo.

## Context

The user wants to make "strong PRs" into the upstream repo, aiming at
**proving unproven theorems** — explicitly not low-hanging fruit, but also
not Fields-medal-level results. The survey here drives the Phase 1 strategy
recorded in `CLAUDE.md`. Done in the founding session immediately after
memo `0001`.

## Work

### Repo facts

- Lean 4 project, mathlib pinned at `v4.27.0`, toolchain
  `leanprover/lean4:v4.27.0`.
- Top-level Lean directories (file counts):
  - `FormalConjectures/` — 685+ files of stated conjectures, organized
    by source:
    - `ErdosProblems/` (413 files — dominant)
    - `Wikipedia/` (119)
    - `GreensOpenProblems/` (42)
    - `WrittenOnTheWallII/` (26)
    - `Paper/` (22)
    - `OEIS/` (21)
    - `Arxiv/` (14)
    - `Mathoverflow/` (10)
    - `Other`, `Books`, `OpenQuantumProblems`, `Millenium`,
      `HilbertProblems`, `Kourovka`, `OptimizationConstants`,
      `Subsets`, `Util` (small)
  - `FormalConjecturesForMathlib/` — supporting definitions intended for
    upstream to mathlib. **No `sorry` allowed here.**
  - `FormalConjecturesTest/` — test driver.

### Counts that drove the strategy

- Files with `category research solved` and at least one `sorry`: **389**.
- Files with `category textbook` and at least one `sorry`: **77**.
- Files with `category research open`: **559**.
- The official site (https://google-deepmind.github.io/formal-conjectures/)
  reports the global tallies: 1,052 `research open`, 849 `research solved`,
  128 `textbook`, 471 `test`, 159 `API`, total 1,901 problems. Only 112
  problems have an attached `formal_proof` annotation today — i.e.,
  ~94% of the corpus has no formal proof of any kind.

### Contribution mechanics

- **Three valid contribution shapes** (from upstream `README.md`,
  `AGENTS.md`, `CONTRIBUTING.md`):
  1. New formalisation of a conjecture (statement + sanity tests, often
     with the main theorem itself left as `:= by sorry`).
  2. Short inline proof of an existing `sorry`. Cap is **25–50 lines**.
  3. Long proof in a separate repo, linked back via
     `@[formal_proof using lean4 at "<url>"]` (or `using
     formal_conjectures` for a same-repo link, or `using other_system`
     for non-Lean systems).
- A signed Google CLA is required for any merged PR. The user owns this.
- `lake --wfail build` must pass — warnings break the build.
- `native_decide` is banned in `FormalConjecturesForMathlib/` and
  case-by-case elsewhere; prefer `decide` (or `decide +kernel`).
- Every theorem has exactly one `@[category ...]`, at least one
  `@[AMS ...]`, and (for `research open` / `research solved` /
  `textbook`) a docstring with a concise description and source link.

### The `Subsets/` benchmark

Two important files:

- `FormalConjectures/Subsets/FC100OpenSet1.lean` — 100 random *open*
  problems. Proving these is Phase 2 territory (or Fields medals).
- `FormalConjectures/Subsets/FC100SolvedSet1.lean` — 100 random
  *non-open* problems (50 `research solved`, 34 `test`, 9 `API`,
  7 `textbook`). **Every sorry we eliminate from this set directly
  improves the published benchmark.** Phase 1 should bias toward names
  in this list.

### Tactical observations

- Many `research solved` claims are 5–50 page papers (Apéry's theorem,
  Helfgott's ternary Goldbach, Mihailescu's Catalan, Schoenberg's
  distribution function, Cambie's lcm result). These cannot fit in 25–50
  lines and either need a separate-repo linked proof or stay sorry'd.
- Several files already record a `formal_proof using lean4 at "<gist or
  fork URL>"` — the actual proof exists outside the main repo and the
  inline `sorry` remains. This means the "long proof in our own repo"
  pattern is well-trodden.
- Some `research solved` *variants* are short and elementary (e.g.
  `BealConjecture.flt_of_beal_conjecture` is already inline-proved in
  ~15 lines, deriving FLT from Beal). These are plausible Phase 1
  targets.
- Computational `category test` proofs (e.g.
  `Erdos1052.isUnitaryPerfect_60`, the Hadamard `H12` example,
  `EulerSumOfPowers.false_for_k4`) sometimes use `decide` /
  `decide +kernel` / `decide +native`. These are honest but the upstream
  README warns against routine `native_decide`, so we treat them as
  contributions only when the underlying definition makes the
  computation worth recording.

### Open `good first issue` tickets (snapshot 2026-05-10)

Twelve open formalisation requests. None are claimed except
`#2247 Giuga Numbers Conjecture` (assigned to `@eyang07`). The rest are
"up for grabs":

- #3688 Fortune's conjecture on Fortunate numbers
- #3687 Elliott–Halberstam conjecture
- #3686 Asymptotic density of powerful numbers
- #3626 Catalan's Mersenne conjecture
- #3476 Fuglede's conjecture
- #2364 Ramsey number R(5,5)
- #2286 Van der Waerden numbers
- #2282 Rudin's conjecture on squares in APs
- #2280 Map folding growth rate
- #2257 Is 10 a solitary number?
- #2249 Odd noncototient conjecture
- #2247 Giuga numbers infinitude *(claimed)*

These are all formalisation asks (Pattern 1 in the contribution
mechanics above) — most accept the main theorem as a sorry plus
sanity-check lemmas.

### Upstream copyright header (current year)

```lean
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
```

## Outcome

User-ratified plan:

- **Phase 1.** Convert `:= by sorry` placeholders into real proofs
  inline, biased toward names in `FC100SolvedSet1` and toward
  `category research solved` *variants* whose informal proof is
  classical and ≤ ~10 pages of mathematics. Avoid pure `decide`
  testcases (low-value), Fields-medal headlines (out of reach), and
  any proof that needs `native_decide`.
- **Phase 2.** Genuinely new mathematics. Deferred until Phase 1 has
  produced merged PRs and we know the review cadence.

The user originally asked us to start with Pattern 1 (new
formalisation + tests), but pivoted to "formalize known work that is
written as 'sorry'" — i.e., Pattern 2 (inline proof of an existing
sorry) — at the message that triggered creation of the memory
infrastructure. **CLAUDE.md and this memo encode that pivot.**

## Lessons

- The repo is unusually well-instrumented for benchmarking: the
  `Subsets/` files and the `formal_proof` attribute give us a
  measurable definition of "shipped." Optimise for benchmark deltas.
- The 25–50-line cap is the binding constraint on Phase 1 target
  selection. Anything that needs more ambient lemmas than mathlib has
  is out unless we are willing to add to `FormalConjecturesForMathlib/`
  in the same PR — and that subdirectory bans `sorry`, which raises
  the bar.
- "`research solved`" is a *very* uneven category. Some entries are
  one-line set-theory exercises; others are 50-page papers. Always
  read the file before promising a target memo.
- Several variants of open conjectures *are* tractable Phase 1
  targets even when the headline conjecture is not. Look at
  `*.variants.*` declarations specifically.
- Some `research solved` problems already have a
  `formal_proof using formal_conjectures at "<fork URL>"` annotation
  pointing to a fork. Those are *not* targets — the fork's owner
  presumably plans to upstream it.

## Next

- Memo `0003` should be the first `target-...` memo: the result of
  scanning concrete sorry candidates against the criteria above and
  picking one to attempt. Bias toward `Subsets/FC100SolvedSet1`
  members. Specifically promising names noted during the survey:
  - `Erdos50.erdos_50_schoenberg` (Schoenberg's distribution-function
    existence — but probably too deep for inline)
  - `BealConjecture.flt_of_beal_conjecture` (already proved; useful
    template)
  - Various `WrittenOnTheWallII.Test.*` graph computations
  - `Wikipedia.Hadamard.isHadamard_H12` (12×12 determinant + ±1
    check; needs a clever route, not pure `decide`)
  - `Wikipedia.EulerSumOfPowers.false_for_k4/k5` (already proved by
    `decide` + witness; useful template, not a target)
  - `Erdos26.variants.rusza` (counterexample construction —
    plausibly tractable if the construction is short in the literature)
  - Several `Erdos*.variants.*` solved entries with short statements
    that we have not yet read.
- Before writing memo `0003`, re-check upstream for any newly merged
  PRs touching the candidate file — we don't want to step on someone
  else's work.
