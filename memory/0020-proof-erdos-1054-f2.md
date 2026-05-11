# Erdős 1054 — `f 2 = 0` (first from-scratch Goal-2 proof)

**Status:** shipped (local).
**Date:** 2026-05-11.
**Related:** 0013 (pipeline tracking).
**Kind:** proof (Goal-2 from-scratch, not a bridge).

## What's different about this one

Memos 0007–0019 cover *bridge* work: take an existing Lean proof from
some external source (gist, forum thread, plby repo) and translate the
signature to the upstream `formal-conjectures` form. The Lean proof
itself is preserved as a port.

This memo covers *from-scratch* work: take an upstream `:= by sorry`
where **no Lean proof exists anywhere**, write the proof using the
informal mathematical argument from `erdosproblems.com/1054`.

## Statement

```lean
theorem f_undefined_at_2 : f 2 = 0
```

where `f n := if (∃ m k ≥ 1, n = ∑ i < k, Nat.nth (· ∈ m.divisors) i)
then Nat.find h else 0` (upstream `Erdos1054.f`).

The claim: there is no `m, k ≥ 1` such that `2` is the sum of the `k`
smallest divisors of `m`, so `f` returns the junk value `0`.

## Informal proof

For any `m : ℕ` and `k ≥ 1`, the sum `∑_{i<k} nth (· ∈ divisors m) i ≠ 2`.

- `m = 0`: `divisors 0 = ∅`, every `nth` is `0`, sum is `0`.
- `m = 1`: `divisors 1 = {1}`, so `nth 0 = 1` and `nth (i+1) = 0`;
  sum is `1` (regardless of `k ≥ 1`).
- `m ≥ 2`, `k = 1`: sum is `nth 0 = 1`.
- `m ≥ 2`, `k ≥ 2`: sum ≥ `nth 0 + nth 1`. Now `nth 0 = 1` and `nth 1`
  is the second-smallest divisor of `m`, which is `≥ 2` (since
  `1, m ∈ divisors m` are distinct for `m ≥ 2`, so the card is ≥ 2,
  and by strict-mono of `Nat.nth` we get `nth 1 > nth 0 = 1`).
  Hence sum ≥ `1 + 2 = 3`.

So sum ∈ `{0, 1, 3, 4, ...}` — never `2`.

## Lean formalisation

`proofs/erdos1054/Erdos1054/Proof.lean` (~130 lines). Reproduces the
upstream `f` definition character-for-character, then proves the
theorem via the case analysis above. Helper lemmas:

- `nth_divisors_of_card_le`: `nth = 0` beyond the card.
- `nth_divisors_zero`: `m = 0 ⇒ nth ... = 0`.
- `nth_divisors_pos_zero`: `m ≥ 1 ⇒ nth 0 = 1`.
- `card_divisors_ge_two`: `m ≥ 2 ⇒ #(divisors m) ≥ 2` (via `{1, m}` injection).
- `nth_divisors_ge_two_one`: `m ≥ 2 ⇒ nth 1 ≥ 2` (via strict-mono).

Main proof uses:

- `simp only [Nat.Iio_eq_range] at hsum` to convert the parsed
  `∑ i < k, ...` (which uses `Finset.Iio`) to `∑ i ∈ Finset.range k, ...`.
- `Finset.sum_le_sum_of_subset_of_nonneg` to bound the sum below by
  the partial sum over `Finset.range 2`.

## Verification

```
'Erdos1054.f_undefined_at_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard mathlib axioms. No `native_decide`, no custom
axioms.

## Why this counts

This is the first contribution from this project that *writes* a Lean
proof rather than *translating* one. The mathematical argument is
elementary case analysis, but the Lean machinery for `Nat.nth` +
`Nat.divisors` + the `Finset.Iio`/`Finset.range` distinction requires
several lemmas that weren't in mathlib in directly-applicable form.

The proof matches the upstream signature character-for-character
(modulo our v4.28.0 mathlib pin vs upstream v4.27.0). When
`formal-conjectures` upgrades to v4.28.0, this proof drops in directly.

## Next

* `Erdos1054.f_undefined_at_3` (the misnamed `f 5 = 0`): same helper
  lemmas apply, just need the case analysis for `5` instead of `2`.
  Slightly more work since for k=3 and m=2 the sum hits 3, for k=2 and
  m=4 the sum is 3, etc — need to rule out more cases.
* Other textbook-tier Goal-2 targets from memo 0013's reassessment
  table (e.g. `#945 .equivalence`, `#770 .h_eq_add_one`).
