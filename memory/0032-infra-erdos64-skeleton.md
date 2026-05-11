# Erdős 64 — project skeleton + `Basic.lean`

**Kind:** infra
**Status:** shipped (local).
**Date:** 2026-05-11
**Related:** 0031 (target), plan at `~/.claude/plans/zesty-launching-origami.md`.

## What this commit ships

`proofs/erdos64/`:

- `lakefile.toml`, `lean-toolchain` — mirror of `proofs/erdos613/`, pins
  mathlib v4.28.0.
- `Erdos64.lean` — top-level import.
- `Erdos64/Basic.lean` (~95 lines) — definitions and reformulations
  every later module depends on:
  - `Has2PowCycle G` — the positive form of the Erdős 64 conclusion
    on a single graph.
  - `IsCounterexample64 V G` — the predicate that `G` is a finite
    counterexample (`minDegree ≥ 3` plus `¬ Has2PowCycle G`).
  - `erdos64_iff_no_counterexample` — universe-parameterised
    equivalence between the universal form and the "no counterexample"
    form.
  - `has_2pow_cycle_of_has_C4`, `has_2pow_cycle_of_has_C8`,
    `has_2pow_cycle_of_has_C4_or_C8` — the standard reductions every
    Track-A sub-case closes through. The disjunctive form
    `C₄ ∨ C₈` matches Carr 2026 exactly.

`lake build` clean. `#print axioms Erdos64.erdos64_iff_no_counterexample`:

```
'Erdos64.erdos64_iff_no_counterexample' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

— the standard three, no `sorryAx`, no `Lean.ofReduceBool`.

## Universe handling

Upstream `Erdos64.erdos_64` uses `∀ (V : Type*)` (universe-polymorphic).
A naive iff-reformulation that quantifies twice over `Type*` triggers
universe mismatch when applying the hypothesis. We resolved this by
introducing a single `universe u` and quantifying over `Type u` on both
sides of the iff. Concrete Track-A and -B per-graph theorems will
specialise to `u = 0` via explicit `Fin n` or `inductive V` types.

This means the bridge file (eventually `Erdos64/Bridge.lean`) will
discharge upstream's `Type*` universal by accepting any universe `u`
and applying the iff at that universe.

## What's next

- **Commit 2:** `Erdos64/WarmUp.lean` with `K₄`, `K_{3,3}`, 3-prism
  satisfying Erdős 64 (memo `0033-proof-erdos64-warmup.md`).
- **Commit 3:** `Erdos64/GirthDiam.lean` proving
  `SimpleGraph.girth_le_two_mul_diam_add_one` (memo
  `0034-proof-erdos64-girth-diam.md`, plus idea memo `0035` for
  upstream mathlib donation).
