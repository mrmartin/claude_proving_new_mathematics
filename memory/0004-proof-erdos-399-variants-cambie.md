# 0004 — Proof: `Erdos399.erdos_399.variants.cambie`

**Kind:** proof
**Status:** shipped (compiles with standard axioms only; `lake --wfail build` passes)
**Date:** 2026-05-10
**Related:** 0003 (target), 0002 (survey)
**Upstream file:** `formal-conjectures/FormalConjectures/ErdosProblems/399.lean`

## Taxonomy (per `CLAUDE.md`)

- **Defining vs. solving:** *solving.* The statement was already in
  the repo (added by upstream PR #1623, which closed issue #710 — that
  PR was the *defining* work). We replaced one of the file's `:= by sorry`
  placeholders with a working Lean proof. No statement, attribute, or
  docstring touched.
- **Known proof vs. new proof:** *known proof.* Cambie's mod-8
  observation is documented in the
  [erdosproblems.com forum thread](https://www.erdosproblems.com/forum/thread/686#post-4599),
  and the docstring states the argument verbatim ("considerations modulo
  8 rule out…"). Our work is the formal translation; no new mathematics
  is being claimed.

## Goal

Replace the `:= by sorry` on `erdos_399.variants.cambie` with an inline
Lean 4 proof that compiles cleanly under `lake --wfail build`, depends
only on the standard three axioms, and fits in the 25–50-line upstream
budget.

## Result

Compiled. 52 proof-body lines (lines 76–127 of
`FormalConjectures/ErdosProblems/399.lean`), of which the helper
`have` blocks account for 19 lines and the case split for the rest.
The other three sorries in the file (`erdos_399`, `erdos_oblath`,
`pollack_shapiro`, `sum_two_squares`) remain untouched and warn
expectedly.

`lake --wfail build` over the entire project succeeds (8687 jobs).

`#print axioms Erdos399.erdos_399.variants.cambie` reports:

```
'Erdos399.erdos_399.variants.cambie' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

— the standard three. Critically **no** `Lean.ofReduceBool`, which
would mean `native_decide` slipped in.

## Final proof

```lean
@[category research solved, AMS 11]
theorem erdos_399.variants.cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4 := by
  intro hcop hxy heq
  -- Helper: factor a Nat into 2*(a/2) + a%2.
  have hmod_dichot : ∀ a : ℕ, a ^ 4 % 8 = 0 ∨ a ^ 4 % 8 = 1 := by
    intro a
    rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      have : (k + k) ^ 4 = 8 * (2 * k ^ 4) := by ring
      rw [this]; exact Nat.mul_mod_right 8 _
    · right
      have key : (2 * k + 1) ^ 4 = 8 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k) + 1 := by ring
      rw [key]; omega
  have hmod_even : ∀ a : ℕ, a ^ 4 % 8 = 0 → 2 ∣ a := by
    intro a ha
    by_contra h2na
    obtain ⟨k, rfl⟩ : Odd a :=
      (Nat.even_or_odd a).resolve_left (fun he => h2na he.two_dvd)
    have key : (2 * k + 1) ^ 4 = 8 * (2 * k ^ 4 + 4 * k ^ 3 + 3 * k ^ 2 + k) + 1 := by ring
    rw [key] at ha
    omega
  by_cases hn : 4 ≤ n
  · have h8dvd : (8 : ℕ) ∣ n ! :=
      (by decide : (8 : ℕ) ∣ Nat.factorial 4).trans (Nat.factorial_dvd_factorial hn)
    obtain ⟨k, hk⟩ := h8dvd
    have hn0 : n ! % 8 = 0 := by rw [hk]; exact Nat.mul_mod_right 8 k
    have hsum : (x ^ 4 + y ^ 4) % 8 ≠ 0 := by
      rw [Nat.add_mod]
      rcases hmod_dichot x with hx | hx <;> rcases hmod_dichot y with hy | hy
      · exfalso
        have h2g : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd (hmod_even x hx) (hmod_even y hy)
        rw [hcop] at h2g
        exact absurd h2g (by decide)
      · simp [hx, hy]
      · simp [hx, hy]
      · simp [hx, hy]
    exact hsum (heq ▸ hn0)
  · push_neg at hn
    have hnle : n ! ≤ 6 := by interval_cases n <;> decide
    have hxle : x ≤ 1 := by
      by_contra h
      push_neg at h
      have h16 : 16 ≤ x ^ 4 := by
        have := Nat.pow_le_pow_left h 4
        simpa using this
      omega
    have hyle : y ≤ 1 := by
      by_contra h
      push_neg at h
      have h16 : 16 ≤ y ^ 4 := by
        have := Nat.pow_le_pow_left h 4
        simpa using this
      omega
    interval_cases n <;> interval_cases x <;> interval_cases y <;> simp_all
```

## Mathlib lemmas it actually leans on

Compared with the target memo (`0003`), here is what was needed:

| Used in proof | Notes |
| ------------- | ----- |
| `Nat.even_or_odd` | Drives both helpers. Unpacks to `⟨k, rfl⟩` for `a = k + k` (even) or `a = 2*k + 1` (odd). |
| `Even.two_dvd` | Bridges `Even a → 2 ∣ a` in the `hmod_even` contradiction step. |
| `Nat.mul_mod_right` | Closes `(8 * c) % 8 = 0` cleanly. |
| `Nat.factorial_dvd_factorial` | `4! ∣ n!` once we have `4 ≤ n`. |
| `Nat.add_mod` | Splits `(x⁴ + y⁴) % 8` into `(x⁴ % 8 + y⁴ % 8) % 8`. |
| `Nat.dvd_gcd` | Conjunction of `2 ∣ x` and `2 ∣ y` ⇒ `2 ∣ gcd x y`. |
| `Nat.Coprime` | Definitionally equal to `gcd x y = 1`; `rw [hcop]` works. |
| `Nat.pow_le_pow_left` | `1 < x ⇒ 16 ≤ x ^ 4` for the small-`n` bound. |
| `Odd` (mathlib alias for `∃ k, _ = 2*k+1`) | Unpacked via `(Nat.even_or_odd a).resolve_left`. |
| Tactics: `ring`, `omega`, `decide`, `interval_cases`, `simp`, `simp_all` | The real workhorses. |

What I expected but didn't need:
- `Nat.pow_mod` — replaced by direct `ring` factorisation followed by `omega`. The `ring`+`omega` route reads better than the `pow_mod`/`interval_cases` route I drafted in `0003`.
- `Nat.add_mul_mod_self_left` — pattern-match failed on `(8 * X + 1) % 8`. `omega` handles the divisibility cleanly without needing the named lemma.

What I had to redo:
- `Nat.eq_zero_of_dvd_of_lt` is the wrong lemma for "`d ∣ n` ⇒ `n % d = 0`". The correct form here is to destructure `8 ∣ n!` as `⟨k, hk⟩`, rewrite, and use `Nat.mul_mod_right 8 k`.
- The two earlier helper proofs that used `interval_cases (a % 8) <;> omega` failed because omega lifts the surrounding outer-scope hypotheses (`hcop`, `hxy`, `heq`) and gets distracted; rewriting the helpers via `Nat.even_or_odd` plus explicit `ring` factorisation made omega's job purely linear and it closed cleanly.

## Risks that fired vs. didn't (vs. risk register in `0003`)

| Risk in 0003 | Outcome |
| ------------ | ------- |
| Wrong name for `Nat.mod_eq_zero_of_dvd` | Fired. Worked around with `obtain ⟨k, hk⟩ := h8dvd; rw [hk]; exact Nat.mul_mod_right 8 k`. |
| `interval_cases (a % 8) <;> decide` slow | Did not fire — the `Nat.even_or_odd`-based helpers do not use this approach. |
| `Nat.pow_le_pow_left` signature mismatch | Did not fire — `simpa using this` worked. |
| `simp [hx, hy]` doesn't close non-zero residue cases | Did not fire — `simp` reduced `(0 + 1) % 8`, `(1 + 0) % 8`, `(1 + 1) % 8` to `1`, `1`, `2`, all `≠ 0`. |
| `Nat.factorial_dvd_factorial` argument order | Did not fire — first argument is the inequality `4 ≤ n`, second is implicit. |
| `Coprime` rewrite | Did not fire — `rw [hcop]` worked as predicted. |

A new risk that surfaced and was resolved:
- `interval_cases n <;> interval_cases x <;> interval_cases y <;> simp_all <;> omega` produced an "omega tactic does nothing" warning (closed by `simp_all` already, omega had no work). Trailing `omega` removed; `--wfail build` then passes.

## Verification ledger

| Check | Outcome |
| ----- | ------- |
| `lake env lean FormalConjectures/ErdosProblems/399.lean` | Three expected `sorry` warnings on the other three theorems in the file; **no warnings, no errors on `cambie`**. |
| `lake build FormalConjectures.ErdosProblems.«399»` | Module builds, 8687 jobs total. |
| `lake --wfail build` (full project) | Passes, all 8687 jobs. |
| `#print axioms Erdos399.erdos_399.variants.cambie` | `[propext, Classical.choice, Quot.sound]` — standard three only. |
| Diff against upstream `main` | Confined to lines 76–127 of `FormalConjectures/ErdosProblems/399.lean`. No other declarations, files, attributes, or docstrings touched. |

## Phrasebook entries to keep around

(Patterns I want future-me to reach for on similar problems.)

- **`a ^ k % m`-style claims**: don't fight `interval_cases (a % m)` if
  the surrounding context confuses omega; instead unpack via
  `Nat.even_or_odd a` (or a similar dichotomy), substitute via
  `⟨k, rfl⟩`, factor with `ring` into `m * P + r`, then close with
  `omega` or `Nat.mul_mod_right m _`.
- **`8 ∣ n!`** for `n ≥ 4`:
  `(by decide : (8 : ℕ) ∣ Nat.factorial 4).trans (Nat.factorial_dvd_factorial hn)`.
  The same shape generalises to other small-modulus divisibilities of
  factorials.
- **Coprime ⇒ not both even**: `Nat.dvd_gcd (h_even_x) (h_even_y)`
  composed with `rw [hcop]` and `absurd · (by decide)`, where `hcop`
  is `Nat.Coprime x y` and works as `gcd x y = 1`.
- **Small-`n` finite checks**: when an upper bound on a Nat parameter
  combines with a polynomial bound on a witness (here, `x⁴ ≤ 6` ⇒
  `x ≤ 1`), do the parameter `interval_cases` first to reduce
  factorials/symbolic terms, then the witness `interval_cases`,
  then `simp_all` to close.

## Next

- This proof compiles and is sound, but **it has not been PR'd
  upstream**. The `formal-conjectures` PR step is still gated on
  user go-ahead (CLA, fork setup, `gh pr create`).
- Keep the change in our repo (`mrmartin/claude_proving_new_mathematics`)
  as a record of the work, plus the upstream-clone diff under
  `formal-conjectures/`. The clone is git-ignored at the project
  root, so the upstream change does not show up in our own commit;
  we capture it via this memo and (when the upstream PR is opened)
  via the PR URL.
- The natural follow-up Phase 1 target is one of the backups from
  memo `0003` — `Erdos865.variants.k2` (sum-free additive
  combinatorics pigeonhole) is the next pick if the user wants more
  Phase 1 work.
