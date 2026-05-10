# 0003 — Target: `Erdos399.erdos_399.variants.cambie`

**Kind:** target
**Status:** go (proof attempt approved by user)
**Date:** 2026-05-10
**Related:** 0002
**Upstream file:** `formal-conjectures/FormalConjectures/ErdosProblems/399.lean` (lines 73–76)

## Taxonomy

This work is in the **solving + known proof** cell of the
`CLAUDE.md` 2×2:

- **Defining vs. solving:** *solving.* The file already exists
  (added by upstream PR #1623, which closed issue #710 — that PR was
  *defining* work and shipped statements with `:= by sorry`). We
  replace the existing `sorry` on the variant `cambie` with a real
  proof. We do **not** touch any other declaration in the file.
- **Known proof vs. new proof:** *known proof.* Cambie's mod-8
  observation is documented in the
  [erdosproblems.com forum thread](https://www.erdosproblems.com/forum/thread/686#post-4599)
  cited in the docstring, and the docstring itself states the
  argument ("considerations modulo 8 rule out…"). Our work is the
  formal translation of that informal argument. No new mathematical
  content is being claimed.

## Goal

Pick the first concrete `:= by sorry` in `formal-conjectures` to replace
with a real inline Lean proof. Write the informal proof and the risk
register down before touching any code, so future-me can reconstruct the
plan even if the implementation pass goes sideways.

## Context

`memory/0002` settled on **Phase 1 — formalise known proofs**, biased
toward `*.variants.*` solved entries with classical short proofs.
This session ran a three-way candidate scan:

- *number-theory equivalences* (Giuga / Carmichael cluster),
- *concrete-number claims* (`Erdos17.isClusterPrime_97_isLeast_non_cluster`,
  various OEIS sequence values, etc.),
- *`*.variants.*` lemmas* across Erdős, Mahler, InverseGalois, etc.

The leader by every dimension that matters — clean classical mathematics,
mathlib readiness, ≤ 50 line budget, no `native_decide`,
self-contained — is `Erdos399.erdos_399.variants.cambie`.

The user-approved plan is at
`/home/martin/.claude/plans/swirling-snacking-raccoon.md`.

## Theorem

```lean
/--
Cambie has also observed that considerations modulo 8 rule out any
solutions to n! = x^4 + y^4 with (x, y) = 1 and xy > 1.
-/
@[category research solved, AMS 11]
theorem erdos_399.variants.cambie {n x y : ℕ} :
    x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4 := by
  sorry
```

No `formal_proof using ...` annotation today, so the inline `sorry` is
unclaimed in any fork we can see.

## Informal proof

Mod 8, `a⁴ ∈ {0, 1}`, with `a⁴ % 8 = 0 ⇔ 2 ∣ a`:

| `a % 8` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
| ------- | - | - | - | - | - | - | - | - |
| `a⁴ % 8`| 0 | 1 | 0 | 1 | 0 | 1 | 0 | 1 |

If `Nat.Coprime x y` then `gcd x y = 1`, so x and y are not both even.
Therefore `(x⁴ + y⁴) % 8 ∈ {0+1, 1+0, 1+1} = {1, 2}` — never `0`.

Now split on `n`:

- **`n ≥ 4`**: `8 ∣ 4!` (`4! = 24`) and `4! ∣ n!` (Mathlib's
  `Nat.factorial_dvd_factorial`), so `n! % 8 = 0`. The equation
  `n! = x⁴ + y⁴` then forces `(x⁴ + y⁴) % 8 = 0`, contradicting
  the previous.

- **`n ≤ 3`**: `n! ∈ {1, 1, 2, 6}`. Since `x⁴ ≤ x⁴ + y⁴ = n! ≤ 6`
  and `2⁴ = 16 > 6`, we have `x ≤ 1` and similarly `y ≤ 1`.
  `interval_cases x <;> interval_cases y` plus the hypothesis
  `1 < x*y` produces a finite set of cases, all closed by `omega`
  using `heq`.

## Mathlib lemmas expected

- `Nat.pow_mod : a ^ b % n = (a % n) ^ b % n`
- `Nat.add_mod : (a + b) % n = (a % n + b % n) % n`
- `Nat.mod_lt : 0 < n → m % n < n`
- `Nat.factorial_dvd_factorial : m ≤ n → m! ∣ n!`
- `Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n`
- `Nat.Coprime` — a `def`-equal alias for `Nat.gcd x y = 1`, so
  `rw [hcop]` should work.
- `Nat.pow_le_pow_left`
- Tactics: `decide`, `omega`, `interval_cases`, `simp`, `nlinarith`
  (fallback).

No additions to `FormalConjecturesForMathlib/`.

## Risk register

| Risk | Probability | Fallback |
| ---- | ----------- | -------- |
| `Nat.mod_eq_zero_of_dvd` not the exact name in 4.27.0 | medium | `obtain ⟨k, hk⟩ := h8; omega` |
| `interval_cases (a % 8) <;> decide` slow | low | unfold each branch with explicit residues |
| `Nat.pow_le_pow_left` signature mismatch | low | replace with `nlinarith` |
| `simp [hx, hy]` doesn't close non-zero residue cases | medium | `omega` after `Nat.add_mod` |
| `Nat.factorial_dvd_factorial` argument order | low | `(by omega : 4 ≤ n)` |
| `Coprime` rewrite | low | `unfold Nat.Coprime at hcop` |

If a helper grows past ~10 lines, lift it to a `private lemma` above
the theorem (still in the same file — no ForMathlib churn).

## Go verdict

**Go.** The proof has a clean classical informal version, mathlib has
all the pieces, and the line budget is realistic at ~32–40 lines.
Backup targets identified in case this falls over are
`Erdos865.variants.k2`, then
`AgohGiuga.agoh_giuga.variants.isStrongGiuga_implies_isCarmichael`,
then `Erdos686.variants.four_three`.

## Next

Implementation pass next: edit
`formal-conjectures/FormalConjectures/ErdosProblems/399.lean`,
iterate against LSP diagnostics, gate with `lake --wfail build`,
axiom-check, then write `memory/0004-proof-erdos-399-variants-cambie.md`.
