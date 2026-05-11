# Erdős 1113 (`infinitely_many_sierpinski`) — misclassified target, parent is OPEN

**Status:** abandoned — target was off-limits under the (now-explicit) Goal 2 gating rule on parent-problem status.
**Date:** 2026-05-11.
**Related:** 0020 (Erdős 1054 misclassification), 0021 (Erdős 399 sum_two_squares partial).
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/1113.lean`, the `Erdos1113.erdos_1113.variants.infinitely_many_sierpinski` declaration.
**erdosproblems.com status:** [`https://www.erdosproblems.com/1113`](https://www.erdosproblems.com/1113) — **OPEN.**

## Goal (as I framed it, wrongly)

After the user asked me to "identify the ideal candidate" for a solved-but-not-in-Lean Erdős problem, I picked `Erdos1113.erdos_1113.variants.infinitely_many_sierpinski`. My rationale: Sierpiński's 1960 covering-system proof of the infinitude of Sierpiński numbers is a clean classical result, mathlib has all the order/CRT API we need, and the variant carries a `category research solved` (or equivalent) upstream tag. Five-step plan: orders → covering → CRT witness → AP compositeness → infinite set.

## Context

The user had previously caught two misclassifications in the same channel:
- `Erdos1054.f_undefined_at_2` was a definitional triviality, not a solution (memo 0020).
- `Erdos399.variants.sum_two_squares` is only partially provable because Bertrand-in-AP is missing from mathlib (memo 0021).

That should have been a louder signal that "variant has a known proof" ≠ "problem is solved". I shipped Steps 1–3 of the Sierpiński infinitude proof and was about to dispatch Step 4 when the user pointed out:

> "I can see this problem is OPEN <https://www.erdosproblems.com/1113>. So this is not what I want to be formalizing!"

## What was shipped before the stop (all axiom-clean, no `native_decide`)

`proofs/erdos1113/` is a Lake subproject (mathlib v4.28.0) with three modules:

1. **`Erdos1113/Orders.lean`** (commit `f62b8f1`, ~60 lines). Seven `orderOf_two_mod_p` lemmas for `p ∈ {3, 5, 17, 257, 65537, 641, 6700417}`, all via `Nat.orderOf_eq_prime_pow` + plain `decide`.
2. **`Erdos1113/Covering.lean`** (commit `0bcc015`, 39 lines).
   - `covering_system_nat : ∀ n : ℕ, n % 2 = 1 ∨ n % 4 = 2 ∨ … ∨ n % 64 = 0` (one `omega`).
   - `two_pow_mod_of_orderOf {p} [NeZero p] {m a} (hord : orderOf (2 : ZMod p) = m) {n} (hn : n % m = a) : (2 : ZMod p) ^ n = (2 : ZMod p) ^ a`.
3. **`Erdos1113/Witness.lean`** (commit `13ceb92`, 33 lines). `exists_witness : ∃ k₀, k₀ % 2 = 1 ∧ k₀ % 3 = 1 ∧ k₀ % 5 = 1 ∧ k₀ % 17 = 1 ∧ k₀ % 257 = 1 ∧ k₀ % 65537 = 1 ∧ k₀ % 641 = 1 ∧ k₀ % 6700417 = 6700416` with explicit witness `15511380746462593381` (CRT modulus `36893488147419103230 = 2·3·5·17·257·65537·641·6700417`). Lemma does not depend on any axioms.

The math is correct and the files build. They are off-target.

## Outcome

Steps 4 and 5 of the planned proof were not started. The shipped subproject is left in place as a record of the work, but should not be cited as a Goal-2 contribution. If it is ever salvageable, the venue would be a hypothetical `Sierpinski/InfinitelyMany.lean` upstream file targeting the Sierpiński theorem in its own right rather than as a variant of Erdős 1113.

## The misclassification — what I got wrong, exactly

Upstream's category tag on `infinitely_many_sierpinski` describes the *variant* (which Sierpiński proved). I read it as licensing Goal-2 work. But Erdős 1113 itself — "is 78557 the smallest Sierpiński number?", the "Seventeen or Bust" problem — is open. Sierpiński's theorem is a side note inside an open Erdős problem's file, not a stand-alone solved Erdős problem.

The general pattern: `FormalConjectures/ErdosProblems/N.lean` is organised around *one* problem; everything in it is contextually tied to that problem. Working a solved variant of an open file still leaves the project's Goal 2 KPI ("solve an Erdős problem that's marked solved on erdosproblems.com but not yet in Lean") at zero. The user does not want this.

## Lessons (now codified in `CLAUDE.md`)

* **First action on any candidate:** `WebFetch erdosproblems.com/N`. If status is OPEN, the file is off-limits — every variant, every sub-statement, regardless of upstream `category` tags. This is now the explicit "HARD GATING RULE" in `CLAUDE.md` under Goal 2.
* **Upstream `category research solved` on a variant of an OPEN problem is not enough.** It describes the variant, not the parent. The parent-problem status is the load-bearing check.
* **Three misclassifications in a row (1054, 399, 1113) means the project's selection heuristic was leaky.** The fix is the gating rule above plus a project-wide "no Goal-2 target memo without an `erdosproblems.com` status quote" expectation.
* The shipped Lean work is technically correct math but does not advance any project goal. Leaving it as record only — not citing it as a contribution.

## Next

* No follow-up Lean work on Erdős 1113.
* When the user picks a new Goal-2 candidate, the first step in the corresponding `target-` memo must be the `erdosproblems.com/<N>` status quote with timestamp.
* If desired, the `proofs/erdos1113/` files could later be removed from the repo — but the user did not ask to delete them, and keeping them as a record (cross-referenced from this memo) makes the misclassification visible to future sessions rather than silently erased.
