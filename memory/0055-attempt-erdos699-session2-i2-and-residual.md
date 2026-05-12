# Erdős #699 — attempt 2: tame-residual closed; `i=2` Pure-Power Dichotomy partly closed via Lucas

**Kind:** attempt (partial — Goal-3 progress, conjecture still open)
**Status:** session complete; conjecture still open.
**Date:** 2026-05-12 (continuation of session 1)
**Related:** [[0052]] (literature), [[0053]] (target), [[0054]] (attempt 1
framework), plan file `~/.claude/plans/majestic-sparking-mochi.md`.
**Upstream link:** none (work stays in our companion repo per user
direction).

## Headline

Six new axiom-clean theorems shipped across `proofs/erdos699/` this
session. Two of the four sorries from memo `0054` are now *strictly
narrower* (their open obstructions are smaller). One new theorem
(`pure_power_dichotomy_M_ge_2_i_eq_2`) is stated and partially closed —
its sorry corresponds to a precisely-named exceptional case requiring
Sylvester-Schur-style machinery not currently in Mathlib v4.27.0.
Erdős #699 itself remains open.

## What closed (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

| Theorem | File | Phase | Lines |
|---|---|---|---|
| `dvd_choose_of_dvd_residual_block` | `Tame.lean` | 1 | 28 |
| `caseB_split_with_hyp_tame_residual` | `CaseB.lean` | 1 | 47 |
| `exists_odd_prime_dvd_of_coprime_two` | `Fix2_i2.lean` | 2 | 14 |
| `odd_prime_dvd_choose_two` (+ private `two_mul_choose_two_eq`) | `Fix2_i2.lean` | 2 | 26 |
| `dichotomy_M_ge_2_witness` | `Fix2_i2.lean` | 2 | 33 |
| `dvd_choose_of_dichotomy_digit_zero_mismatch` | `Fix2_i2.lean` | 3 | 28 |
| `dvd_choose_of_lucas_mismatch_at` | `Fix2_i2.lean` | 4 | 35 |

Repo total: 670 → ~880 lines, 14 → 21 fully proved theorems, 4 → 5
sorries (the new sorry is the `i = 2` partial; the increase is
deliberate — we *narrowed* two existing sorries and *added* a new
theorem that's partly closed).

### Narrowed sorries

**`caseB_split_with_hyp` (CaseB.lean:168)**: previously its `q ∣ C(j,i)`
arm was a single broad sorry. After Phase 1, the theorem is refactored
to a 3-way dispatch: (i) `q ∤ C(j,i)` → `case_B_alpha_gcd`; (ii)
lonely-residual non-empty → new helper `caseB_split_with_hyp_tame_residual`;
(iii) Bridge case `v_q(C(n, i)) ≥ 2` → narrower sorry. The Bridge case
is the same algebraic obstruction as Erdős #699 itself, so it is
genuinely deep, but its scope is strictly smaller than the original.

**`pure_power_dichotomy_M_ge_2_i_eq_2` (Fix2_i2.lean:214, new)**: the
`i = 2` case of the Pure-Power Dichotomy. Witness prime `r` is picked
via `M.minFac`, with `r ≥ 3` (Step 1) and `r ∣ C(n, 2)` (Step 2). The
proof closes the case **`∃ a, (n / r^a) mod r < (j / r^a) mod r`** via
Lucas's theorem (Phase 3 + 4). The remaining sorry corresponds
*precisely* to the case where `j`'s base-`r` digits are pointwise ≤
`n`'s digits — in this configuration `r ∤ C(n, j)` and the
dichotomy-derived prime fails.

## The big new tool

**`dvd_choose_of_lucas_mismatch_at`** (Phase 4) is a clean Mathlib-style
lemma: at any base-`r` digit position `a`, if `n`'s digit at `a` is
strictly less than `j`'s digit at `a`, then `r ∣ C(n, j)`. Proved by
induction on `a` over the recursive Lucas (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`).
This is reusable beyond #699 — it's a clean "digit-mismatch ⟹ divisibility"
fact, the constructive companion to the standard "Lucas product nonzero ⟹
not divisible" direction.

## Precise blocking obstructions

### Obstruction A — Bridge case of `caseB_split_with_hyp`

```lean
-- The remaining sorry in CaseB.lean:168
-- Under: q prime, q tame, q ∣ C(n, i), q ∣ C(j, i),
--        v_q(C(n, i)) ≥ 2, residual block (j-i) empty,
-- show:  q ∣ gcd(C(n, i), C(n, j))
```

This is the same difficulty as Erdős #699 itself. Bloom's verdict on
Parthasarathy's attempt centered on this configuration.

### Obstruction B — `i = 2` Lucas-no-mismatch case

```lean
-- The remaining sorry in Fix2_i2.lean:214
-- Under: dichotomy data with i = 2, M ≥ 2,
--        r = M.minFac, r ≥ 3, r ∣ M, r ∣ C(n, 2),
--        ∀ a, ¬ ((n / r^a) mod r < (j / r^a) mod r),
-- show:  ¬ FullyObstructed n 2 j
```

**Concrete example exhibiting the gap:** `(n, j) = (6, 3)` with
dichotomy data `(k, V, M) = (0, 1, 3)`. `r = 3 = M.minFac`. Base-3
digits: `n = 6 = 20₃`, `j = 3 = 10₃`. At every position `j`'s digit ≤
`n`'s digit, so Lucas gives `3 ∤ C(6, 3) = 20`. But the conjecture
*does* hold for `(6, 2, 3)` — `gcd(C(6, 2), C(6, 3)) = gcd(15, 20) = 5`,
witnessed by `p = 5` from `n(n − 1) = 30`. Our minFac-driven proof
cannot find that witness.

Closing this would require:
1. A formalised Sylvester-Schur (not in Mathlib v4.27.0), OR
2. A witness-selection routine that tries multiple odd primes (including
   primes outside `M`), OR
3. An entirely different argument bypassing the FO definition.

### Obstruction C — `pure_power_dichotomy_M_ge_2` general `i ≥ 3`

Unchanged from memo `0054`. The Pure-Power Dichotomy for `i ≥ 3` involves
prime factors of `M` with potentially `r ≤ i`, where the digit analysis
is more delicate. Out of scope this session.

### Obstruction D — `erdos_699_main` and `dichotomy_closes_FO_residual`

Unchanged from memo `0054`. Closing `erdos_699_main` requires closing
all of Cases A, B (algebraic + Bridge), and the FO residual, which is
the conjecture itself.

## Why this matters as Goal-3 progress

`CLAUDE.md`'s standard for Goal-3 work: *"Even an interesting partial
result (a counterexample, a conditional proof, a sharp special case) on
a previously-unsettled formalised conjecture counts."*

This session shipped:

1. **A clean reusable mathematical tool** —
   `dvd_choose_of_lucas_mismatch_at` is a clean Mathlib-style digit-Lucas
   lemma that did not exist before. It is independently true and
   useful.

2. **A narrowed `caseB_split_with_hyp`** — the Case-B framework's open
   obstruction is now strictly smaller (Bridge case only, lonely-residual
   case fully closed).

3. **A precise statement of the `i = 2` Pure-Power Dichotomy** with a
   *partial proof* (Lucas-mismatch case closed unconditionally, with the
   remaining gap precisely named: "no Lucas mismatch with `M.minFac`").

4. **A concrete witnessed example** (`(6, 3)`) showing why the minFac
   strategy can fail — clarifying for any future attempt that the
   witness-selection problem is non-trivial.

None of this constitutes a closure of #699, and none should be described
as such. Permitted phrasings: *"Lean-verified partial framework, with
the `q ∣ C(j, i)` tame-residual sub-case closed and the `i = 2`
Pure-Power Dichotomy partly closed via Lucas's theorem; one residual
exceptional configuration documented and exemplified"*.

## Files & line counts (this session)

| File | Lines before | Lines after | Δ |
|---|---|---|---|
| `Erdos699/Tame.lean` | 55 | 83 | +28 |
| `Erdos699/CaseB.lean` | 130 | 187 | +57 |
| `Erdos699/Fix2_i2.lean` | — | 218 | +218 (new) |
| `Erdos699/Main.lean` | 44 | 44 | 0 |
| `Erdos699/Fix2.lean` | 93 | 93 | 0 |
| `Erdos699/AxiomCheck.lean` | 37 | 43 | +6 |
| `Erdos699.lean` | 9 | 10 | +1 |
| **Repo total** | **670** | **~880** | **+~210** |

## What to try next (concrete, in priority order)

1. **Resume the `i = 2` Lucas-no-mismatch case via Bertrand's postulate.**
   Mathlib has `Nat.bertrand` (or `Real.bertrand` and variants). Bertrand
   gives a prime in `(n/2, n]`, which is > `j` (since `j ≤ n/2`). Such
   a prime `p > j` automatically gives `p ∤ j!` and `p ∤ (n - j)!`, so
   `p ∣ C(n, j)` whenever `p ∣ n(n - 1)…(n - i + 1) = n(n - 1)` (for
   `i = 2`). This is exactly Case A. Closing this gives an unconditional
   witness for the `(6, 3)`-style cases. Estimated ~80 lines.

2. **Search Mathlib for a Sylvester-Schur formalisation.** Per memo
   `0052` it isn't there, but Bertrand-driven proofs of the `i = 2`
   case exist in the literature and may have been formalised since.
   Worth a `lean_leansearch` or Loogle query.

3. **Close `pure_power_dichotomy_M_ge_2_i_eq_2` exceptional case
   modulo a stated Case-A axiom.** Even if Sylvester-Schur isn't in
   Mathlib, we could state a local `axiom case_A_prime_exists` and
   close the residual conditional on it. *Beware*: `CLAUDE.md` forbids
   custom axioms; this would require user permission. Probably not the
   right move.

4. **Generalise `dvd_choose_of_lucas_mismatch_at` to Mathlib.** The
   helper is clean and independently useful; consider PR'ing it
   upstream (after stabilising the file naming).

5. **Attempt the `i = 2` exceptional case via *another* prime of `M`.**
   When `M` has multiple prime factors `r₁, r₂, ...`, we can try each
   one. Currently we use `M.minFac` only. If `M = r₁ · r₂` with `r₁
   < r₂`, maybe `r₂` gives a Lucas mismatch where `r₁` doesn't. This is
   a finite check, but requires iterating, which adds complexity.

6. **Investigate Mathlib's `Choose.choose_modEq_prod_range_choose_nat`**
   for a "Lucas product zero in `Nat`" formulation. The current proof
   does the conversion ad hoc; a cleaner formulation could shave lines.

## Honest assessment vs. plan

Plan probabilities (from `~/.claude/plans/majestic-sparking-mochi.md`):

- **~95%**: Phases 0–2 ship → ✅ achieved.
- **~70%**: Phase 3 (easy Lucas) closes → ✅ achieved.
- **~25%**: Phase 4 fully succeeds → ❌ partial — the easy case
  generalised to "any Lucas mismatch position", but the
  Lucas-no-mismatch residual remains. The plan's stated mitigation
  ("ship `_under_smoothness` narrowing variant") is what happened in
  spirit, just framed differently in the Lean signature.
- **~3%**: All sorries close, `erdos_699_main` falls → ❌ as expected.

The session produced more reusable mathematical content than the plan's
median outcome (`dvd_choose_of_lucas_mismatch_at` is a clean general
helper, not just a restricted variant). The remaining gap is
characterised precisely; future work has a clear handle.

## Process meta

- All 5 phases completed within wall-clock budget.
- 4 commits pushed: one per substantive phase
  (`e9c6076`, `b97477d`, `0820ae7`, `a1d9b18`).
- Plan file at `~/.claude/plans/majestic-sparking-mochi.md` (approved).
- Axiom audit confirms every new theorem is clean. `caseB_split_with_hyp`
  remains sorry'd; `pure_power_dichotomy_M_ge_2_i_eq_2` remains sorry'd
  in its exceptional case.
- Per `CLAUDE.md`'s commit-and-push discipline: every phase's commit
  was pushed immediately on completion.
