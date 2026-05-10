# Erdős 457 — target evaluation (next bridge candidate after Erdős 397)

**Kind:** target
**Status:** go
**Date:** 2026-05-10
**Related:** 0006 (Lean-side Erdős catalogue), 0009–0010 (Erdős 397 — same
workflow), 0007–0008 (Erdős 38 — same workflow), `CLAUDE.md`
"External resources".
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/457.lean`,
declaration `Erdos457.erdos_457` (still `:= by sorry`; carries
`@[formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem457.lean"]`).

## One-line summary

Pick `Erdos457.erdos_457` as the next reproduce-and-bridge target: a
proof that there is `ε > 0` such that infinitely many `n` have all primes
`p ≤ (2 + ε) log n` dividing `∏_{1 ≤ i ≤ log n} (n + i)`. Barreto/Aristotle
already shipped the gist proof (342 lines, no axioms, no sorries) — and
they wrote the upstream-signature bridge inline as `theorem erdos_457` at
the bottom of the same file. Our work is a verbatim port to v4.28.0 plus
a thin `answer(True) ↔ _` outer shell.

## Taxonomy — which 2×2 cell

**Goal 2 — Solving + Known proof**, lower-right of the 2×2. Mathematics
(GPT-5.2 Pro / Pilatte's argument with Shiu-style consecutive-primes
plus binomial bounds) and Lean formalisation (Aristotle, with Barreto
prompting) both belong to others. **No new mathematics; no new
formalisation.** Our deliverable is a local v4.28.0 reproduction plus
the `answer(True)`-wrapping bridge.

## Why this candidate (over the alternatives I scanned)

I sized the (LEAN)+formalised candidate pool from memo 0006 / 0009 by
fetching each linked source and doing a `wc -l` plus axiom check. The
results, with disqualifications:

| # | Source size | Axiom-clean? | Notes |
| --- | --- | --- | --- |
| 26 | plby v4.24.0, 1350 lines | yes? | Heavy mathlib drift, big context. |
| 56 | plby v4.24.0, 1350 lines | yes? | Same. |
| 194 | ster-oc gist, 617 lines | – | Disprove only; mid-size. |
| 204 | Woett, 947 lines | – | Mid-size. |
| 268 | madeve-unipi gist, 1297 lines | – | Mid. |
| 258 | live.lean v4.28.0, 353 lines | **no** — uses `axiom tao_teravainen` | Disqualified. |
| 259 | ster-oc gist, 1012 lines | – | Mid. |
| 268 / 275 / 347 / 355 / 370 | varied | – | Mid-large. |
| 392 | AlexKontorovich PrimeNumberTheoremAnd | – | Multi-file project. |
| 397 | llllvvuu gist, 101 lines | yes | **Already shipped (memos 0009–0010).** |
| 418 / 541 / 645 / 728 | plby | – | v4.24.0 drift, big. |
| 427 | JohnEdwardJennings gist, 91 lines | **no** — uses `axiom shiu_consecutive_primes` | Disqualified. |
| **457** | **Woett-hosted Barreto/Aristotle, 342 lines** | **yes (no `axiom` or `sorry` per grep)** | **Pick.** |
| 997 | live.lean v4.28.0, 220 lines | **no** — uses `axiom maynardTaoBFT` | Disqualified. |
| 1051 | forum, 1702 lines | – | Big. |
| 1141 | Oriike, 1629 lines | – | Big. |
| 1196 | math-inc multi-file project | – | Multi-file. |

#457 is the smallest axiom-clean candidate in the list after #397, **and**
the gist already does most of the bridge work itself: the file ends with
the upstream-shaped `erdos_457` theorem (under the gist's namespace),
proved by composing the gist's `thm_main` with a small
`F = ∏_{i ∈ Icc 1 ⌊log n⌋} (n + i)` definitional unfold.

## Side-by-side: gist statement vs upstream signature

**Upstream (`formal-conjectures/FormalConjectures/ErdosProblems/457.lean`):**

```lean
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem457.lean"]
theorem erdos_457 : answer(True) ↔ ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  sorry
```

**Gist (`Woett/Lean-files/.../ErdosProblem457.lean:327–342`):**

```lean
theorem erdos_457 : ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  use 0.1; ... apply thm_main.mono ...
```

So the gist's body matches the upstream **exactly** modulo the
`answer(True) ↔ _` outer wrapper. Bridge work needed:

1. **`answer(...)` macro shim.** Identity macro
   `macro_rules | answer($t) => $t`, same shim as Erdős 38 and Erdős 397
   bridges.
2. **`Iff` wrapping.** `answer(True) ↔ X` reduces to `True ↔ X`.
   Direction `True → X`: discharge via `Gist.erdos_457`. Direction
   `X → True`: trivial.

That's it. Bridge body should be ≤ 30 lines.

## Mathlib drift considerations

Same as #397: v4.24.0 → v4.28.0. Expected friction:
- `Nat.succ_mul_choose_eq` deprecation — the gist uses
  `Nat.choose_pos`, `Nat.sum_range_choose`, etc.; deprecation warnings
  are tolerable.
- `Nat.recOn` style usage — should still compile.
- `Real.log`, `Real.continuous_mul_log`, `tendsto_inverse_atTop_nhds_zero_nat`
  — names should be stable.
- The gist uses `set_option maxHeartbeats 0` (unbounded) plus
  `maxRecDepth 4000` — these will pass through.

The gist also contains:
- `lemma_asymptotic_inequality`
- `lemma_prime_count`
- `lemma_simultaneous_approximation`
- `lemma_binom_bounds`
- `lemma_divisibility`
- `F`, `A_func` definitions

— I'll port verbatim under `namespace Erdos457.Gist`.

## Risks / fallbacks

| Risk | Probability | Fallback |
| ---- | ----------- | -------- |
| Mathlib drift on `Nat.choose`/`Real.log` lemma names | medium | LSP `lean_local_search` to find the v4.28.0 name; substitute. |
| `set_option relaxedAutoImplicit false` triggers errors | low | drop the option. |
| `simp +decide` syntax differs in v4.28.0 | low | replace with `simp` + explicit decide tactic call. |
| Inline `aesop` calls timeout | low | bump heartbeats; the gist already has `maxHeartbeats 0`. |
| `lemma_*` symbols collide with the bridge namespace | none — gist is namespaced as `Gist`. |

If the port runs into more than ~5 drift fixes that aren't trivial
renames, **stop, write a `fail-...` memo, and report**.

## Verdict

**Go.** Same workflow as 0009→0010; the only new wrinkle is that the
gist itself already ports its conclusion to the upstream signature
(modulo `answer(True) ↔ _`), so the bridge file is much smaller than
for #38 or #397. Expected total work: well under an hour.

## Next

`memory/0012-bridge-erdos-457.md` — proof memo recording the final
bridge file, the `#print axioms` output, and an honest taxonomy note.
