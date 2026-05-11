# Erdős 26 `.variants.rusza` — bridge for plby/Aristotle's Ruzsa counterexample

**Kind:** proof
**Status:** shipped (local). Sorry-free; standard axioms only.
**Date:** 2026-05-11
**Related:** 0029 (target), 0013 (pipeline)
**Upstream file:** `formal-conjectures/FormalConjectures/ErdosProblems/26.lean`

## Taxonomy

- **Defining vs solving:** solving. Replaces a naked sorry.
- **Known proof vs new:** known. Ruzsa's classical counterexample;
  Aristotle wrote the Lean version.
- **2×2 cell:** Goal 2.

## Source

[`plby/lean-proofs/src/latest/ErdosProblems/Erdos26.lean`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos26.lean),
502 lines, by Aristotle from Harmonic.

## Local artifact

`proofs/erdos26/`:

- `Erdos26/Proof.lean` (502 lines) — plby verbatim, attribution
  header replaced. Builds clean at mathlib v4.28.0, no drift fixes
  needed.
- `Erdos26/Bridge.lean` (~70 lines) — recreates upstream's
  `Set.HasDensity` locally (since mathlib v4.28.0 lacks it; it lives
  only in upstream's `FormalConjecturesForMathlib`), defines the
  bridge's `IsBehrend` matching upstream's signature, proves
  `Erdos26.IsBehrend A ↔ Erdos26Bridge.IsBehrend A` via `rfl`
  (the underlying predicates are term-for-term identical), and
  transfers plby's rusza theorem to the upstream signature.

`lake build` clean. `#print axioms Erdos26Bridge.erdos_26_variants_rusza_upstream`
reports `[propext, Classical.choice, Quot.sound]` — standard three only.

## Bridge key idea

plby's `HasDensity` and upstream's `Set.HasDensity` are
**term-for-term identical**: both unfold to
`Tendsto (fun b => partialDensity S Set.univ b) atTop (𝓝 α)` with
the same `partialDensity (S ∩ A ∩ Iio b).ncard / (A ∩ Iio b).ncard`.
The only "difference" is namespace placement (plby's is bare,
upstream's is in `Set`). So definitionally,
`Erdos26.IsBehrend A = Erdos26Bridge.IsBehrend A` holds by `rfl`
after unfolding `IsBehrend → HasDensity → partialDensity` on both
sides.

This means the bridge file effectively asserts
`plby.rusza ↔ upstream.rusza` and proves the equivalence by `rfl`.
plby's theorem closes the upstream sorry one-for-one.

## What's already in the literature; what is new

- Ruzsa's counterexample for Erdős 26 (the original problem and its
  weakening).
- Aristotle's Lean version (auto-formalising Ruzsa's construction).
- Our contribution is **only the bridge**: re-stating the result
  with upstream's `Set.HasDensity` (since plby uses local).

## Next

Awaiting user OK to PR a `@[formal_proof using lean4 at "<our-url>"]`
annotation on the upstream `Erdos26.erdos_26.variants.rusza` sorry.
(The user has indicated no PR for now; this stays a local artifact.)
