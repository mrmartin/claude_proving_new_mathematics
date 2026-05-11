# Erdős 1051 — bridge

**Status:** shipped (local).
**Date:** 2026-05-11.
**Related:** 0013 (tracking), 0019 (this).

## Source

Decoded from the forum thread
[`erdosproblems.com/forum/thread/1051`](https://www.erdosproblems.com/forum/thread/1051)
via the live.lean-lang.org `codez=` URL parameter (lz-string compressed
base64). 803-line gist by van Doorn–Tao via Aristotle: irrationality of
`∑ 1/(a_n · a_{n+1})` under the growth condition `liminf (a_n)^(1/2^n) > 1`.

## Drift fixes

Single drift: removed a `; ring` after `norm_num` (the `ring` was a
no-op leftover that v4.28.0 rejects as "no goals").

## Bridge

The gist proves `erdos_1051_irrational` for `a : ℕ → ℕ` with
`0 < a n` and `1 < liminf (a n)^(1/2^n)`. Upstream
`Erdos1051.erdos_1051` is for `a : ℕ → ℤ` with `StrictMono a` and
`GrowthCondition a := 1 < liminf (a n)^(1/2^n)`. The bridge closes
this gap in ~110 lines:

1. **Tail truncation.** From `StrictMono a` derive `∃ N₀, ∀ n ≥ N₀, 2 ≤ a n`
   (since `a n ≥ a 0 + n`, eventually `≥ 2`).
2. **Container conversion.** Define `b m := (a (m + N₀)).toNat`. Prove
   `(b m : ℤ) = a (m + N₀)`, `StrictMono b`, `0 < b m`.
3. **Shifted-power liminf.** Define `u_safe n := max 0 ((a n : ℝ)^(1/2^n : ℝ))`
   to satisfy the gist's `h_pos` requirement (`u_safe ≥ 0` unconditionally,
   and eventually `u_safe n = (a n : ℝ)^(1/2^n : ℝ)`).
   Apply gist's own `erdos_1051_liminf_shift_pow u_safe ... N₀`:
   `1 < liminf (m ↦ (u_safe (m + N₀))^(2^N₀ : ℝ))`. Then rewrite using
   `Real.rpow_mul` and `pow_add` to get
   `1 < liminf (m ↦ (b m : ℝ)^(1/2^m : ℝ))`.
4. **Apply gist's main theorem** to get
   `Irrational (∑' m, 1/((b m : ℝ) * (b (m+1) : ℝ)))`.
5. **Series decomposition.** Show summability via `Gist.summable_of_ge_two`,
   then `Summable.sum_add_tsum_nat_add N₀`:
   `ErdosSeries a = (∑ n < N₀, 1/((a n)·(a (n+1))) : ℝ) + tail`.
6. **Rational + irrational = irrational.** The prefix
   `∑ n < N₀, 1/((a n : ℤ)·(a (n+1) : ℤ))` casts from
   `∑ n < N₀, 1/((a n : ℚ)·(a (n+1) : ℚ)) : ℚ`, which is rational.
   Apply `Irrational.ratCast_add q` to conclude.

## Key bridge insight

The gist itself ships the auxiliary lemma `erdos_1051_liminf_shift_pow`
(via the gist's own `liminf_rpow_gt_one`), which is precisely the shift+
power tool needed. Instead of re-proving the shifted-liminf > 1 from
scratch (which would require careful `IsBoundedUnder`/`IsCoboundedUnder`
manipulation), the bridge re-uses that helper. The `max 0 (·)` redefinition
makes the gist lemma applicable even when `a n < 0` for small `n`.

## Axioms

```
'Erdos1051.erdos_1051' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Status update

This bridge closes the only "decoded but substantive-bridge-blocked"
candidate from the 2026-05-10 reassessment of forum-thread sources.
Shipped count: **9** (was 8).
