# Erdős 1148 `.variants.weaker` — proof

**Kind:** proof
**Status:** shipped (local). Sorry-free; only standard axioms. Verified
to compile both at mathlib v4.28.0 (local) and v4.27.0 (inlined into
upstream `FormalConjectures/ErdosProblems/1148.lean`).
**Date:** 2026-05-11
**Related:** 0023 (target), 0006 (catalogue), 0013 (bridge pipeline)
**Upstream file:** `formal-conjectures/FormalConjectures/ErdosProblems/1148.lean`

## Taxonomy

- **Defining vs solving:** solving. The statement was already in the
  upstream file; we replaced its `:= by sorry` with a working proof.
- **Known proof vs new proof:** known. The result is the [Va99]
  "obvious" weakening of Erdős 1148. Our work is the formal translation;
  no new mathematics is being claimed.
- **2×2 cell:** *Known informal proof × Solving a sorry* → Goal 2.

## Goal

Replace the sorry on `Erdos1148.erdos_1148.variants.weaker`:

```lean
def erdos_1148_weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

@[category research solved, AMS 11]
theorem erdos_1148.variants.weaker : ∀ n, erdos_1148_weaker_prop n := by sorry
```

## What we proved

`proofs/erdos1148weaker/` is a standalone Lake project containing:

- `Erdos1148Weaker/Proof.lean` (201 lines including comments) — the
  full proof of `Weaker n` for every `n : ℕ`, where `Weaker` is the
  exact upstream `erdos_1148_weaker_prop` definition.
- `Erdos1148Weaker/Bridge.lean` (32 lines) — restates the result with
  the upstream signature so plugging into the upstream file is a
  one-line replacement.

`lake build` succeeds clean (no warnings) at mathlib v4.28.0.

`#print axioms Erdos1148Weaker.witness_spec` reports:

```
'Erdos1148Weaker.witness_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— the standard three. No `sorryAx`, no `Lean.ofReduceBool`.

We also verified the proof inlines cleanly into the upstream file at
mathlib v4.27.0: `lake --wfail build FormalConjectures.ErdosProblems.«1148»`
succeeded with the proof body inlined, after annotating the two private
helper lemmas with `@[category test, AMS 11]` to satisfy upstream's
lint rule that every theorem/lemma carry both attributes. We did not
keep that edit; the file remains upstream-original locally.

## Proof strategy

Constructive, by case-split on `r = n - q²  (mod 4)` where
`q = Nat.sqrt n`. Each case provides explicit witnesses:

| `r mod` | precondition | `(x, y, z)` |
| ------- | ------------ | ----------- |
| `r = 0` | — | `(q, 0, 0)` |
| `r` odd | `r ≤ 2q - 1` | `(q, (r+1)/2, (r-1)/2)` |
| `r ≡ 0 (mod 4)` | `r ≥ 4`, `q ≥ 2` | `(q, r/4 + 1, r/4 - 1)` |
| `r ≡ 2 (mod 4)` | `r ≥ 2`, `q ≥ 1` | `(q + 1, q - r/2, q + 1 - r/2)` |

Each case is verified by:

1. **Equation** `n = x² + y² - z²` in ℕ. Cases B, C, D produce a
   subtraction; the rewrite via `obtain ⟨k, hk⟩ : ∃ k, r = …` (or
   substitution `k = k₀ + 1` for Case C) plus `ring` / `omega` closes
   it. Case D uses `zify` with `m ≤ q` and `m ≤ q + 1` to translate
   the polynomial identity through ℤ.
2. **Real bounds** `x², y², z² ≤ n + 2 √n`. The cheap chains are:
   * `q² ≤ n ≤ n + 2 √n`,
   * In Case D, `(q+1)² ≤ n + 2 √n` follows from `r ≥ 2` and
     `q ≤ √n`: `(q+1)² - q² = 2q + 1 ≤ 2 √n + r`.
   * All `y`, `z` witnesses are ≤ `q`, so `y², z² ≤ q² ≤ n`.

Mathlib helpers used:

- `Nat.sqrt_le n : Nat.sqrt n * Nat.sqrt n ≤ n`.
- `Nat.lt_succ_sqrt n : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1)`.
- `Real.sqrt_le_sqrt`, `Real.sqrt_sq` (for `q ≤ √n` in ℝ).
- `omega`, `nlinarith`, `push_cast`, `zify`, `ring` for the arithmetic.

## Why the upstream "Va99 obvious" matches

The construction above is the standard four-case argument: `q = ⌊√n⌋`
gives `n - q² ∈ [0, 2q]`, and `(y - z)(y + z) = m` is solvable for any
`m ≢ 2 (mod 4)`. The single obstruction `r ≡ 2 (mod 4)` is repaired
by lifting `x` from `q` to `q + 1`, which absorbs `r → r + 2q + 1 - r = 2q + 1`
(now odd), giving a representation with one extra unit of slack — and
`r ≥ 2` ensures that unit is paid back by the slack term `2 √n`.

## Local artifact

The local project lives in `proofs/erdos1148weaker/`. To re-verify:

```
cd proofs/erdos1148weaker
lake exe cache get
lake build
```

This produces `Erdos1148Weaker.Proof.olean` and
`Erdos1148Weaker.Bridge.olean`. Standard mathlib axiom triple only.

## What was already in the literature; what is new

The result and its informal proof outline were already known
(documented in [Va99] as "obvious"). The corner-case structure (the
mod-4 obstruction, the `(q+1, q - r/2, q + 1 - r/2)` Case-D witness)
is folklore. **Our contribution is the formal translation only.** No
new mathematics is being claimed.

## Next

1. Wait for user OK to either:
   - upstream the inlined proof as a PR to `formal-conjectures`
     (128 lines body + ~10 lines helpers; longer than the 25-50-line
     soft ceiling but precedented by `602.lean`), or
   - upstream a `@[formal_proof using lean4 at "<our-url>"]` annotation
     pointing to `proofs/erdos1148weaker/`.
2. Update `catalogue/formal_conjectures_erdos.jsonl` regen path to
   pick up the resolved entry (mechanical; happens when the catalogue
   is re-run).
