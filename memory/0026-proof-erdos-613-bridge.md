# Erdős 613 — bridge for Tao's Pikhurko-n=5 counterexample

**Kind:** proof
**Status:** shipped (local). Sorry-free; only standard axioms. Adapts
Tao's 1131-line `teorth/analysis` Lean file and adds an upstream
bridge.
**Date:** 2026-05-11
**Related:** 0025 (target), 0013 (bridge pipeline), 0024 (just-shipped
1148 weaker)
**Upstream file:** `formal-conjectures/FormalConjectures/ErdosProblems/613.lean`

## Taxonomy

- **Defining vs solving:** solving. The statement already exists in
  the upstream file; we replace its `:= by sorry` (modulo bridging).
- **Known proof vs new proof:** known. Pikhurko [Pi01] gave the
  asymptotic disproof; the n=5 case was noted by Pikhurko and
  formalised by Tao in his `teorth/analysis` repo (with vibe-coding
  assistance).
- **2×2 cell:** *Known informal proof × Solving a sorry → Goal 2.*

## Source

[`teorth/analysis/Analysis/Misc/erdos_613.lean`](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean),
1131 lines, MIT-licensed. Tao describes it as "hugely inelegant but
gets the job done". Vibe-coded based on the parallel work for
Erdős 707.

The file constructs `PikhurkoN5.G`, a 16-vertex graph (from
`A1 (Fin 2)`, `B1 (Fin 5)`, `A2 (Fin 3)`, `B2 (Fin 5)`, `apex`), with
exactly 44 edges, and proves the key combinatorial lemma:

```lean
theorem red_triangle_of_no_blue_star
    (color : Sym2 V → Fin 2) (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    hasMonoTriangle G color 1
```

i.e., for every 2-coloring, either color 0 has a `K_{1,5}` or color 1
has a triangle.

## Local artifact

`proofs/erdos613/`:
- `Erdos613/Tao.lean` (1131 lines): Tao's file dropped in verbatim,
  no drift fixes needed at mathlib v4.28.0.
- `Erdos613/Bridge.lean` (~140 lines): translates Tao's
  `red_triangle_of_no_blue_star` into the upstream-shape

  ```lean
  False ↔ ∀ n, 3 ≤ n → ∀ V [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    G.edgeFinset.card = Nat.choose (2*n+1) 2 - Nat.choose n 2 - 1 →
    ∃ (B D : SimpleGraph V),
      G = B ⊔ D ∧ B.IsBipartite ∧ ∀ v, D.degree v < n
  ```

  Builds clean at mathlib v4.28.0:

  ```
  cd proofs/erdos613
  lake exe cache get
  lake build
  ```

  `#print axioms Erdos613Bridge.erdos_613_bridge` reports:

  ```
  'Erdos613Bridge.erdos_613_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  — only mathlib's standard three.

## Bridge logic

Refute the universal: take `n = 5`, `V = PikhurkoN5.V`,
`G = PikhurkoN5.G`.

1. **Edge count.** `G.edgeFinset.card = G.edgeSet.ncard` by
   `Set.ncard_coe_finset ∘ SimpleGraph.coe_edgeFinset` then
   `PikhurkoN5.edge_count_44` gives 44. `Nat.choose 11 2 - Nat.choose 5 2 - 1
   = 44` by `decide`.
2. **Decomposition.** From the universal applied at `n = 5`, get
   `B, D` with `G = B ⊔ D`, `B.IsBipartite`, `∀ v, D.degree v < 5`.
3. **Color the edges.** `c : Sym2 V → Fin 2`, `c(e) = 0` if `e ∈ D.edgeSet`,
   else `1`.
4. **Case split.**
   - `hasMonoStar c 0 5`: some vertex `x` has 5 distinct neighbors
     with color-0 edges, which are in `D`. So
     `(D.neighborFinset x).card ≥ 5`, hence `D.degree x ≥ 5`.
     Contradicts `D.degree x < 5`.
   - `¬ hasMonoStar c 0 5`: Tao's `red_triangle_of_no_blue_star`
     gives a color-1 triangle `(a, b, d)`. Each edge is in `G \ D ⊆ B`.
     But `B.IsBipartite = B.Colorable 2`, so its 2-coloring `φ`
     satisfies `φ(a) ≠ φ(b)`, `φ(b) ≠ φ(d)`, `φ(a) ≠ φ(d)`.
     Three pairwise distinct elements of `Fin 2`: impossible
     (`omega` after coercing to ℕ).

## Verified compatibility

- mathlib v4.28.0: builds clean, axiom-clean, no warnings.
- upstream mathlib v4.27.0: not directly tested (Tao's file is large
  and we would need to verify its build under v4.27.0 separately).
  Inlining would require either porting Tao's file or having upstream
  bump its toolchain. For now the local artifact stands; PR would be
  via `@[formal_proof using lean4 at "<our-url>"]` annotation.

## What's already in the literature; what is new

- The disproof of Erdős 613 for n=5 is **Pikhurko 2001**.
- The full Lean formalisation of the disproof was **Tao** in 2026.
- Our contribution is **only the bridge**: connecting
  `PikhurkoN5.red_triangle_of_no_blue_star` to the upstream
  `Erdos613.erdos_613` signature, so that Tao's work can close the
  upstream sorry directly. Same pattern as our prior Erdős-N bridges
  (memos 0008, 0010, 0012, 0014, 0015, 0016, 0017, 0018, 0019).

## Next

Awaiting user OK to either:
1. Open a PR to `formal-conjectures` adding
   `@[formal_proof using lean4 at "https://github.com/mrmartin/claude_proving_new_mathematics/.../Erdos613"]`
   to the upstream file (the README explicitly invites this).
2. Port Tao's 1131-line file to v4.27.0 and inline-replace the
   sorry (more work, removes the toolchain mismatch but adds
   maintenance burden).
