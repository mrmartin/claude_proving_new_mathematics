# Erdős 26 `.variants.rusza` — target evaluation

**Status:** in-progress
**Date:** 2026-05-11
**Related:** 0013 (pipeline), 0028 (just-shipped Erdős 499)

## 2×2 cell

**Known proof × Solving a sorry → Goal 2.**

Parent problem `erdosproblems.com/26` is DISPROVED (LEAN). The
parent `Erdos26.erdos_26` is already shipped upstream with a
`formal_proof_link` to plby. The naked sorry remains on
`Erdos26.erdos_26.variants.rusza`: when we weaken the hypothesis from
`IsThick` (∑1/a_i = ∞) to its complement (∑1/a_i < ∞), Ruzsa found
an explicit counterexample (no shift makes the multiples set
density-1).

A Lean formalisation exists in plby/lean-proofs covering exactly this
variant (alongside the main theorem).

## Source

[`plby/lean-proofs/src/latest/ErdosProblems/Erdos26.lean`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos26.lean),
502 lines, authored by Aristotle from Harmonic (auto-formalising
Ruzsa's classical counterexample).

## Upstream sorry

```lean
@[category research solved, AMS 11]
theorem erdos_26.variants.rusza : ∃ A : ℕ → ℕ,
    StrictMono A ∧ ¬IsThick A ∧ ∀ k, ¬IsBehrend (A · + k) := by
  sorry
```

plby's version of the same theorem (same name, same shape, same
namespace) is fully proved, axiom-clean.

## Definitional caveat

plby redefines `HasDensity`, `IsThick`, `MultiplesOf`, `IsBehrend`
locally in its own `Erdos26` namespace. Upstream defines the same
predicates also in `Erdos26`, but `IsBehrend` uses
`Set.HasDensity` from `FormalConjecturesForMathlib/Data/Set/Density.lean`,
which is **not in mathlib**. plby's `HasDensity` and upstream's
`Set.HasDensity` are *term-for-term identical* modulo namespace
(both unfold to `Tendsto (partialDensity ·) atTop (𝓝 α)` with the
same `partialDensity`).

So plby's `IsBehrend` and upstream's `IsBehrend` are *definitionally
equal*; the bridge just unfolds and applies `rfl`. The transfer of
the rusza theorem is a one-line `(plby_isBehrend_iff_bridge _).mpr`.

## Construction (from plby's file)

Witness `A_n := 2^(2^n)`. The proof:

1. **Strictly monotone.** `pow_lt_pow_right` twice.
2. **Not thick.** `∑ 1/A_n = ∑ 1/2^(2^n)` is dominated by the
   geometric series `∑ 1/2^n`, hence summable.
3. **Not Behrend after any shift k.** For each fixed `k`, the upper
   density of `MultiplesOf (A + k)` is at most
   `∑ 1/(2^(2^i) + k)`, which is bounded above by `∑ 1/2^(2^i)`,
   which is `< ∑ 1/2^(i+1) = 1/2 + 1/4 + ... ≤ 1`. So the upper
   density is `< 1`, contradicting `IsBehrend`.

## Format

502-line local artifact + ~50-line bridge. PR would be via
`@[formal_proof using lean4 at "<our-url>"]`.

## Verdict

**Go.** Build clean at mathlib v4.28.0 with zero drift (plby
targets v4.29.1).
