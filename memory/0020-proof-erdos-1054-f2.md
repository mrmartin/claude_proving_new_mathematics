# Erdős 1054 — `f 2 = 0` (definitional triviality, NOT a solution)

**Status:** shipped (local) — **but does not solve Erdős Problem 1054**.
**Date:** 2026-05-11.
**Related:** 0013 (pipeline tracking).
**Kind:** proof (Lean encoding sanity check).

## What this proof is, and what it is NOT

### What Erdős Problem 1054 actually asks

From [erdosproblems.com/1054](https://www.erdosproblems.com/1054), the
problem (status: **OPEN**) is:

> Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the
> $k$ smallest divisors of $m$ for some $k \ge 1$. Is it true that
> $f(n) = o(n)$? Or is this true only for almost all $n$, and
> $\limsup f(n)/n = \infty$?

This is a real open question about the asymptotic behaviour of $f$.
Terence Tao has disproved the strong claim $f(n) = o(n)$ in comments to
[Erdős Problem 468](https://www.erdosproblems.com/468), showing that
the upper density of $\{n : f(n) \le \delta n\}$ is $\ll \delta^2$.

### What we proved (and why it is NOT a solution)

We proved `Erdos1054.f_undefined_at_2 : f 2 = 0`. In context:

- The Lean definition of `f` uses `if (∃ m k ≥ 1, ...) then Nat.find h
  else 0`. The `else 0` branch is the "junk value" produced when no
  valid `m, k` exists.
- The erdosproblems.com page explicitly notes: *"The function $f(n)$
  is undefined for $n=2$ and $n=5$, but is likely well-defined for all
  $n \ge 6$ (which would follow from a strong form of Goldbach's
  conjecture)."*
- Our proof shows that the `∃` in the Lean encoding is false for `n = 2`
  (so `f 2` hits the `else` branch and returns `0`). This is a
  **definitional sanity check on the Lean encoding**, not progress on
  the asymptotic question.

The forum thread confirms this:
[the forum discussion](https://www.erdosproblems.com/forum/thread/1054)
explicitly notes that "the function f itself has not been shown to be
well-defined, which makes this problem open anyway." The `f_undefined_at_2`
proof is on the *easy* side of that — it just verifies the obvious
non-existence at `n = 2`.

### Why we got this wrong on first pass

When scanning for "Goal-2" candidates (formalise a known proof of a
solved Erdős problem) in memo 0013, we keyed on the `category textbook`
tag and the very short statement length (`f 2 = 0`). The `category
textbook` tag at upstream means "elementary API exercise", *not*
"solves an Erdős problem". We mistook the elementary exercise for a
research contribution. The user correctly flagged this:

> *"I want to see formalized proofs that solve concrete Erdős Problems,
> and that is not the case here."*

This memo records the result as-shipped, but downgrades the framing:
this is a **Lean-encoding sanity check**, valuable only insofar as it
exercises the `Nat.nth` + `Nat.divisors` API. It does **not** count as
a solution to Erdős Problem 1054 — the headline asymptotic question
remains open, and Tao's partial result is the substantive content.

## Statement (as proved)

```lean
theorem f_undefined_at_2 : f 2 = 0
```

## Lean technique

Reproduces the upstream `f` definition; case-splits on `m` (= 0, = 1,
≥ 2) and on `k` (= 1, ≥ 2). Five helper lemmas about
`Nat.nth (· ∈ Nat.divisors m)`:

- `nth_divisors_of_card_le` — `nth = 0` past the card.
- `nth_divisors_zero` — `m = 0` ⟹ all `nth = 0`.
- `nth_divisors_pos_zero` — `m ≥ 1` ⟹ `nth 0 = 1`.
- `card_divisors_ge_two` — `m ≥ 2` ⟹ `#(divisors m) ≥ 2`.
- `nth_divisors_ge_two_one` — `m ≥ 2` ⟹ `nth 1 ≥ 2` (strict mono).

Main proof normalises `∑ i < k, ...` (parses as `Finset.Iio k`) via
`Nat.Iio_eq_range` and bounds the sum below by
`nth 0 + nth 1 ∈ {0, 1, ≥ 3}`, never `2`.

## Verification

```
'Erdos1054.f_undefined_at_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What WOULD count as solving an Erdős problem

In contrast to this triviality, a genuine "Goal-2" contribution would
formalise the *actual* mathematical content of an Erdős problem. For
example:

- Tao's "upper density of `{n : f(n) ≤ δn}` is `≪ δ²`" (from the
  Erdős 468 comments) — proper analytic-NT result.
- The cambie variant of Erdős 399 (`n! ≠ x⁴+y⁴` under coprime/`xy>1`
  constraints), shipped earlier in this project (memo 0004) via a
  ~50-line mod-8 argument — a 1-paragraph elementary proof of a
  research-solved Erdős variant.

Memo 0021 onward will refocus on candidates of the latter shape.

## Next

Re-survey the catalogue for **research-solved** Erdős variants with
short elementary proofs (mod-arithmetic, counting, descent), of the
cambie shape. Skip `textbook`-tagged items that turn out to be Lean
encoding artefacts.
