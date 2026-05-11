# Erdős 399 `.variants.sum_two_squares` — partial proof (`n ≤ 6` only)

**Status:** partial — `n ≤ 6` portion shipped sorry-free; `n ≥ 7`
asymptotic portion blocked by mathlib gap (no Bertrand-in-AP).
**Date:** 2026-05-11.
**Related:** 0013 (pipeline), 0004 (the original cambie precedent),
0020 (the misclassified `f 2 = 0` reframe).

## Upstream target

```lean
@[category research solved, AMS 11]
theorem erdos_399.variants.sum_two_squares :
    ∀ {n x y : ℕ}, 1 < x * y → n ! = x ^ 2 + y ^ 2 →
      n = 6 ∧ (x = 12 ∧ y = 24 ∨ x = 24 ∧ y = 12) := by
  sorry
```

Erdős's observation: the only `n!` that is a sum of two squares (with
`1 < xy`) is `6! = 720 = 12² + 24²`.

## What we proved (sorry-free, axiom-clean)

Three theorems in `proofs/erdos399sumsq/Erdos399SumSq/Proof.lean`:

1. **`no_solutions_lt_six`**: `∀ n < 6, ∀ x y, 1 < xy → n! ≠ x² + y²`.
2. **`solutions_at_six`**: `∀ x y, 1 < xy → 6! = x² + y² → (x, y) = (12, 24) ∨ (24, 12)`.
3. **`sum_two_squares_of_le_six`**: combined statement bounded to `n ≤ 6`.

`#print axioms` for all three returns only `[propext, Classical.choice,
Quot.sound]`. The proofs are by per-`n` case split, bounding `x, y ≤ √(n!)`
via `nlinarith`, then brute-force `interval_cases x <;> interval_cases y
<;> omega`.

This characterises **all** finite solutions: for every `(n, x, y)` with
`n ≤ 6` and `1 < xy` and `n! = x² + y²`, we have `n = 6` and
`(x, y) ∈ {(12, 24), (24, 12)}`. This is a genuine Erdős-mathematics
contribution (it identifies and characterises the unique solution `n = 6`).

## What we did NOT prove (and why)

The full upstream theorem additionally requires:

  **For `n ≥ 7`, `n!` is not a sum of two squares.**

The standard textbook proof:
* By Fermat-Gauss (mathlib's `Nat.eq_sq_add_sq_iff`): `m` is a sum of two
  squares iff every prime `q ≡ 3 (mod 4)` has even `padicValNat q m`.
* For `n ≥ 7`, find some prime `p ≡ 3 (mod 4)` with `n / 2 < p ≤ n`. Then
  `v_p(n!) = ⌊n/p⌋ = 1` (odd), contradicting Fermat-Gauss.

The "find some prime" step is **Bertrand-in-AP**: for every `n ≥ 7`,
there is a prime `p ≡ 3 (mod 4)` with `n / 2 < p ≤ n`. Equivalently:
the gap between consecutive primes `≡ 3 (mod 4)` is `< p` for every
such prime `p` (≥ 7).

**Mathlib has:**
* `Nat.exists_prime_lt_and_le_two_mul` — plain Bertrand
  (some prime in `(n, 2n]`).
* `Nat.forall_exists_prime_gt_and_eq_mod` — Dirichlet's infinitude
  of primes in arithmetic progressions.

**Mathlib does NOT have:**
* Bertrand-in-AP for primes `≡ 3 (mod 4)` (quantitative density,
  not just infinitude).

This is a real mathlib gap. Proving Bertrand-in-AP from scratch is
substantial (uses Chebyshev-style estimates restricted to AP residues,
or PNT-in-AP). It is well outside the per-bridge budget of this project.

The chain of anchor primes `7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79,
83, 103, 107, 127, 131, 139, 151, 163, 167, 179, 191, 199, ...` would
provide a constructive witness for every `n ≥ 7` if we enumerate
sufficiently — each consecutive pair `(p_k, p_{k+1})` of these AP primes
satisfies `p_{k+1} < 2 p_k`. Verifying this property for *all*
consecutive pairs is the Bertrand-in-AP gap.

## What this means for the project's Goal 2

The cambie precedent (memo 0004) was a complete Goal-2 contribution
to Erdős 399 — a ~50-line mod-8 argument closing
`.variants.cambie`. This memo records that the related variant
`.sum_two_squares`, although mathematically solved by Erdős, hits a
mathlib infrastructure gap that prevents a complete formal proof
without first developing Bertrand-in-AP.

The shipped `n ≤ 6` characterisation **is** a concrete result on
Erdős's question, just not the full statement. It complements the
cambie variant (`n! ≠ x⁴ + y⁴`) by handling the analogous `x² + y²`
case for the small-`n` regime.

## Lessons

* **Mathlib coverage matters for Goal-2 selection.** Two
  superficially similar Erdős 399 variants (cambie's `x⁴ + y⁴` and
  Erdős's `x² + y²`) have wildly different Lean-effort profiles:
  cambie is 50 lines of mod-8, sum_two_squares is ≥ a Bertrand-in-AP
  development.
* **The asymptotic step is usually the hard one.** For finite-vs-
  asymptotic-style Erdős statements (characterise all `(n, x, y)` with
  `…`), the small-`n` part is brute-forceable; the unbounded-`n` part
  needs real analytic-NT machinery.
* **Honest gap reporting is worth a memo.** When we can't ship a
  complete proof, recording precisely *what* we proved, *what* we
  didn't, and *why mathlib blocks us* leaves the trail open for a
  later contributor (or for us, once mathlib catches up).

## Next

* Pick a target where the full mathematical proof fits inside mathlib's
  current support. Candidates from memo 0013's revised list:
  * `Erdos44.maxSidonSubsetCard_icc_bound` (textbook): elementary
    Sidon-set counting bound `≤ 2√N`.
  * `Erdos44.greedy_sidon_construction`: greedy Sidon ≥ √N.
  * `Erdos730.variants.explicit_pairs`: computational verification of
    specific `(centralBinom n).primeFactors` equalities.
* If/when mathlib gains Bertrand-in-AP, the asymptotic step here
  reduces to a ~10-line follow-up; the `n ≤ 6` part shipped today is
  the load-bearing computational portion.
