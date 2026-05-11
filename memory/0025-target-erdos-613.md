# Erdős 613 — target evaluation (parent disproof, bridging Tao's Lean file)

**Status:** in-progress
**Date:** 2026-05-11
**Related:** 0013 (bridge pipeline), 0024 (just-shipped 1148 weaker)
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/613.lean`

## 2×2 cell

**Known proof × Solving a sorry → Goal 2.**

Parent problem `erdosproblems.com/613` is DISPROVED (status label
"DISPROVED (LEAN)"). Pikhurko [Pi01] showed the conjecture fails for
all sufficiently large `n`, and Pikhurko noted the *specific case
`n = 5`* already fails by an explicit 16-vertex, 44-edge graph.

Tao formalised the `n = 5` counterexample in
[`teorth/analysis/Analysis/Misc/erdos_613.lean`](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
(1131 lines, "Hugely inelegant…but gets the job done", per the forum
post). The file is permissively licensed.

Per the forum thread (`erdosproblems.com/forum/thread/613`) the
formalisation was done by Tao with "vibe-coded" help, inspired by
the parallel work on Erdős 707.

Our work is **the bridge**: adapt Tao's gist into a local Lake
project and translate his `Pikhurko_n5_statement` into the upstream
`Erdos613.erdos_613` signature.

## Upstream sorry

```lean
@[category research solved, AMS 5]
theorem erdos_613 :
    answer(False) ↔
      ∀ n ≥ 3, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V), [DecidableRel G.Adj] →
        G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 →
        ∃ (B D : SimpleGraph V), [DecidableRel B.Adj] → [DecidableRel D.Adj] →
          G = B ⊔ D ∧ B.IsBipartite ∧ ∀ v, D.degree v < n := by
  sorry
```

For `n = 5`: edge count = `C(11, 2) - C(5, 2) - 1 = 55 - 10 - 1 = 44`.
To negate the universal, exhibit `n = 5` and a 44-edge graph `G` that
is **not** a union `B ⊔ D` with `B` bipartite and `D` of max degree
< 5.

## Tao's local statement

```lean
def Pikhurko_n5_statement : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1
```

(Where `hasMonoStar G c col k` says the edge-color `col` class
contains a `K_{1,k}`, and `hasMonoTriangle G c col` says it contains
a `K_3`.)

## Bridge logic (Tao ⇒ upstream-negation)

Suppose `G = B ⊔ D` with `B` bipartite and `D` of max degree < 5.
Define an edge 2-colouring `c(e) = 0` if `e ∈ D`, else `1` (for
`e ∈ B`). Apply Tao:

- `hasMonoStar G c 0 5`: color-0 (= `D`) contains `K_{1,5}`, i.e.,
  some vertex has degree ≥ 5 in `D`. Contradicts `∀v, D.deg v < 5`.
- `hasMonoTriangle G c 1`: color-1 (= `B`) contains `K_3`, an odd
  cycle. Contradicts `B.IsBipartite`.

Either branch gives a contradiction, so the decomposition cannot
exist. Hence `n = 5`, our `G` is a counterexample. ✓

## Format

Long proof (1131 lines): stays in `proofs/erdos613/` of this repo.
Upstream replacement would be a one-line
`@[formal_proof using lean4 at "<our-url>"]` annotation, requested
when the user gives the go-ahead.

Local toolchain: mathlib v4.28.0. Tao's file imports `Mathlib`
wholesale and builds cleanly out-of-the-box (`lake build` succeeds
in 24s on cached mathlib).

## Verdict

**Go.** Tao's proof builds in-place; the bridge is short (one
contradiction by cases). Standing user rule: small commits, push
after each addition.
