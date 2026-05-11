# Erdős 499 — bridge for plby/Aristotle's Marcus-Minc proof

**Kind:** proof
**Status:** shipped (local). Sorry-free; only standard axioms.
**Date:** 2026-05-11
**Related:** 0027 (target), 0013 (pipeline)
**Upstream file:** `formal-conjectures/FormalConjectures/ErdosProblems/499.lean`

## Taxonomy

- **Defining vs solving:** solving (replaces `:= by sorry`).
- **Known proof vs new:** known. Marcus & Minc 1962; Aristotle wrote
  the Lean version.
- **2×2 cell:** Goal 2.

## Source

[`plby/lean-proofs/src/latest/ErdosProblems/Erdos499.lean`](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos499.lean),
229 lines, authored by Aristotle from Harmonic.

## Local artifact

`proofs/erdos499/`:

- `Erdos499/Proof.lean` (229 lines): plby's file verbatim, only
  header replaced with attribution comment. **No drift fixes needed**
  — builds cleanly at mathlib v4.28.0 (plby targets v4.29.1).
- `Erdos499/Bridge.lean` (~20 lines): wraps `erdos_499` in the
  upstream `answer(True) ↔ ...` shape:

  ```lean
  theorem erdos_499_bridge :
      True ↔ (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n),
        ∃ σ : Equiv.Perm (Fin n), n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) :=
    ⟨fun _ => Erdos499.erdos_499, fun _ => trivial⟩
  ```

`lake build` succeeds clean. `#print axioms Erdos499Bridge.erdos_499_bridge`
reports `[propext, Classical.choice, Quot.sound]` — the standard
three, no `sorryAx`, no `native_decide`.

## What's already in the literature; what is new

- The theorem is Marcus & Minc 1962.
- The Lean proof is Aristotle's (via plby/lean-proofs).
- Our contribution is **only the bridge**: connecting plby's
  `erdos_499` to the upstream `answer(True) ↔ ...` shape so the
  upstream sorry can be closed directly. Same pattern as memos
  0014/0015/0016/0017/0018/0019.

## Next

Awaiting user OK to open a PR with
`@[formal_proof using lean4 at "https://github.com/mrmartin/claude_proving_new_mathematics/.../Erdos499"]`
on the upstream file.
