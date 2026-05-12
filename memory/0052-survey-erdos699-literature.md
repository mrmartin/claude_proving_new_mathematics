# Erdős #699 — literature & state of the art (May 2026)

**Kind:** survey
**Status:** review complete; conjecture **still open** as of 2026-05-12.
**Date:** 2026-05-12
**Related:** 0051 (pincer scan).
**Upstream:** [`erdosproblems.com/699`](https://www.erdosproblems.com/699),
[`erdosproblems.com/forum/thread/699`](https://www.erdosproblems.com/forum/thread/699).

## Statement

Erdős–Szekeres 1978. For every triple `1 ≤ i < j ≤ n/2` (with `n ≥ 2j`),
does there exist a prime `p ≥ i` such that
`p | gcd(C(n,i), C(n,j))`?

Tagged FALSIFIABLE on the database: a single counterexample triple would
settle it negatively. No counterexample is known.

## Classical foundation

- **Sylvester (1892) — Schur (1929) [Sy1892] [Sc1929].** The single-binomial
  case: for `n ≥ 2k`, the product `n(n-1)···(n-k+1)` has a prime factor
  strictly greater than `k`. Equivalent to: there exists prime `p > k`
  with `p | C(n,k)`.
- **Erdős–Szekeres 1978 [ErSz78].** "Some number theoretic problems on
  binomial coefficients", Austral. Math. Soc. Gaz. 5, 97–99. States
  the conjecture above as a gcd-strengthening of Sylvester–Schur, notes
  that the strong form (`p > i`) fails:
  - When `i = 2` for certain powers of 2;
  - For "some counterexamples" at `i = 3`;
  - Exactly **one** known counterexample for `i ≥ 4`, namely
    `gcd(C(28,5), C(28,14)) = 2³·3³·5`.
- **Guy 2004 [Gu04], Problem B31** in "Unsolved Problems in Number
  Theory" (3rd ed.). Restates the conjecture.

The technique is Kummer's theorem (1852): `v_p(C(n,k))` equals the
number of carries when adding `k` and `n − k` in base `p`. mathlib
has this as `Nat.Prime.multiplicity_choose` and friends.

## Computational state (Conglu 2026)

[github.com/conglu1997/erdos_699_rust](https://github.com/conglu1997/erdos_699_rust)
(MIT-licensed, Rust, multi-threaded, resumable JSONL output).

- **Brute sweep `n ≤ 10⁷`** (Jan 2026): no counterexamples to the
  official `p ≥ i` claim. 9 999 997 rows scanned.
- **Targeted family sweeps to `n ≈ 1.3 × 10⁸`**: `n = 2^k` for
  `k ≤ 27` and `n = 3^m + 1` for `m ≤ 17`. No counterexamples.
- **9 known "near misses"** — counterexamples to the *strong* form
  `p > i`. All are witnessed by `p = i` (and `i` is always prime):

  | n | (i, j) | gcd(C(n,i), C(n,j)) |
  |---|---|---|
  | 10 | (3, 5) | 2²·3 |
  | 16 | (2, 6) | 2³ |
  | 28 | (3, 14) | 2²·3² |
  | 28 | (5, 14) | 2³·3³·5 |
  | 244 | (3, 122) | 2²·3⁴ |
  | 512 | (2, 147) | 2⁸ |
  | 2 048 | (2, 713) | 2¹⁰ |
  | 2 188 | (3, 1094) | 2²·3⁶ |
  | 1 594 324 | (3, 797 162) | 2²·3¹² |

- **Structural pattern** observed in the data:
  - `i = 2`: only at `n = 2^k`, gcd is a pure power of 2.
  - `i = 3`: only at `n = 3^m + 1` for `m ∈ {2, 3, 5, 7, 13}`.
  - `i ≥ 4`: only `(28, 5, 14)`.

  These are the "Fully Obstructed" (FO) triples — every prime `> i`
  in `C(n,i)` also divides `C(j,i)`.

## The Parthasarathy attempted proof (March 2026)

[github.com/srinikethpsarathy-oss/Erdos-verification-suite](https://github.com/srinikethpsarathy-oss/Erdos-verification-suite),
16-page paper "An Effective Proof of the Erdős Prime Divisibility
Conjecture for Binomial Coefficients", submitted to *J. Experimental
Math.* Includes a 200-line Lean 4 + Mathlib formalisation.

**Strategy (sketch).** Let `P = n(n−1)···(n−i+1)`. Two cases:

- **Case A.** `P` has a prime `p > j`. Then `p ∤ i!` and `p ∤ j!`, so
  `p` directly witnesses gcd divisibility.
- **Case B.** `P` is `j`-smooth. Sylvester–Schur supplies a prime
  `q ∈ (i, j]` with `q | P`. Use the **master identity**
  `C(n,j)·C(j,i) = C(n,i)·C(n−i, j−i)` to redistribute divisibility:
  - **B-α** (`q ∤ C(j,i)`): master identity gives `v_q(C(n,j)) ≥ 1`
    directly. Algebraic.
  - **B-β** (`q | C(j,i)`, `q` tame in `(j−i, j]`):
    - **B-β-i** (`q` not lonely in `j−i`-block): master identity gives
      `v_q(C(n,j)) ≥ 1`. Algebraic.
    - **B-β-ii**, `v_q(n−k_q) ≥ 2`: **Prime Power Bridge Lemma** —
      `p ≥ i`, `p^V > j`, `v ≥ 2` forces a carry in the base-`p`
      addition `j + (n−j) = n`. Algebraic.
    - **B-β-ii**, `v_q(n−k_q) = 1`: **Cofactor Escape Lemma** —
      three algebraic sub-routes (un-tame escape, bridge on another
      prime, not-lonely on another prime).
  - **B-γ** (`q | C(j,i)`, `q ≤ j−i`): `q` is not tame, doesn't
    witness directly. Defers to "Fully Obstructed" analysis.
- **Fully Obstructed**: when every prime `> i` in `P` also divides
  `C(j,i)`. Then the `i`-product's terms live in a finite `S`-unit
  system (`S = {primes ≤ i} ∪ {primes > i dividing C(j,i)}`).
  Evertse's theorem + Baker–Wüstholz bound the `n` in an FO triple
  to `[2j, N_0(i,j)]` for an effectively computable `N_0`.
- **`i = 1`** case: handled purely algebraically via Kummer + base-`p`
  digit analysis. The argument is sound.
- **Computation**: 110 109 924 triples (`n ≤ 4400`, `i ≤ 23`)
  exhaustively checked.

**Supplement: Carry Lemma + Pure-Power Dichotomy.** Defines
`n − k_i = i^V · M`. Claims:
- `M = 1`: Carry Lemma resolves algebraically (and **all 8 known FO
  triples have `M = 1`**).
- `M ≥ 2`: covered by combination of base-`i` subordinate analysis
  and supplementary computation (10 814 triples verified).

**Lean 4 formalisation** (200 lines in
`Erdos (1).lean`; axiom-audit: only `propext`, `Classical.choice`,
`Quot.sound`). Genuinely proven:
- `master_identity` (the algebraic core)
- `carry_lemma` and `carry_lemma_at_p`
- `tame_prime`, `prime_not_dvd_factorial`
- `case_B_alpha` and `case_B_alpha_gcd`
- `FullyObstructed` definition + `fo_char` characterisation
- `absorption` (`j·C(n,j) = n·C(n−1, j−1)`)
- `dvd_choose_of_dvd_n_not_dvd_j` (`i = 1` case)
- The 8 specific FO triples via `native_decide`
- The 8 `M = 1` arithmetic structures via `omega`

What the Lean file **does NOT contain**: the main theorem statement
itself, the Cofactor Escape Lemma in full generality, Case B-γ
resolution, the Baker–Wüstholz effective bound, the supplement's
M ≥ 2 case analysis, or any closure of the algebraic-cases-plus-
computation pipeline into one universal `∀ i j n …` statement.

## The bug (StijnC, 2026-05-01)

> "In Case B: when `i < q < j`, it may be that `C(n,j)` and
> `C(n−i, j−i)` are not multiples of `q`, while `C(j,i)` and `C(n,i)`
> are. E.g., assume `q = j − k_j` and `q | n − k_n` where
> `k_j < k_n < i` and `v_q(n − k_n) = 1`."

What this is saying: the proof's case analysis assumes that a tame
prime `q ∈ (i, j]` dividing `P` interacts with the `j`-block and the
`(j−i)`-block in a constrained way that lets one of B-α, B-β-i,
Bridge, or Cofactor Escape always fire. Stijn's example violates the
implicit assumption: `q` can divide an element of the *j*-block
(making `q | C(j,i)`) **and** an element of the *n*-block (making
`q | C(n,i)`) **simultaneously**, with `v_q = 1` on the `n`-block
element, in a configuration where neither the master-identity case
distribution nor the Cofactor Escape's prime-r choice yields a witness.

This is a real, structural gap — it is not a typo. The Cofactor
Escape Lemma's three routes do not exhaust the cases.

## Status declaration (Thomas Bloom, 2026-05-11)

> "After reviewing this proof, it is invalid (and the Lean code is
> not formalising anything like the statement here."

Bloom owns the database and is an active analytic number theorist;
his verdict is authoritative for the site's status field. The
Parthasarathy paper is now formally classified as a failed attempt.
The conjecture is **still open** as of 2026-05-12 (yesterday).

## What's salvageable from Parthasarathy

The 200-line Lean file is real Mathlib-backed infrastructure, axiom
clean, and proves the building blocks any future attempt will reuse:

1. **Master identity** — clean, will appear in any approach.
2. **Carry Lemma** in the `r + p^V` form — useful by itself for the
   `M = 1` FO triples (all known FO triples sit on a pure-`i`-power
   structure).
3. **Tame prime lemma** — primes in `(j−i, j]` always divide
   `C(j,i)`. Direct corollary of Kummer.
4. **Case B-α** — when `q | C(n,i)` and `q ∤ C(j,i)`, master identity
   plus prime-divides-product forces `q | C(n,j)`.
5. **FO characterisation** — every prime `> i` in an FO triple's
   `P` must divide `C(j,i)`.

These are independently true theorems whether or not the overall
proof closes. They are direct consequences of Kummer + Sylvester–
Schur and would be in any future attempt's preamble.

## Bug analysis — what would close the gap

Stijn's example identifies that Case B can have a tame prime
`q ∈ (i, j]` with simultaneous `v_q(C(n,i)) = 1` and
`v_q(C(j,i)) = 1`, where neither block has a "second" `q`-multiple
to make the master identity yield ≥ 1 on `C(n,j)`. To fix:

- **Option A.** Extend the Cofactor Escape with a fourth route that
  handles "simultaneous q-divisibility in both i-block and j-block,
  both with v = 1, and j−i-block missing q". The discharging would
  need to find a *different* prime `r ≠ q` that witnesses.
- **Option B.** Strengthen the FO size constraint to rule out
  Stijn's configuration directly: in an FO triple, both `q | C(n,i)`
  and `q | C(j,i)` with `v = 1` give specific Kummer constraints on
  the base-`q` digits of `n` and `j`, which may admit a structural
  contradiction with the rest of the FO conditions.
- **Option C.** Replace the case analysis with a more uniform
  argument (e.g., direct Kummer-carry analysis on a chosen `p = i`,
  generalising the M = 1 supplement).

The supplement's "Pure-Power Dichotomy" (`M = 1` vs `M ≥ 2`) is
actually the most promising direction — every known FO triple has
`M = 1`, and the Carry Lemma resolves all `M = 1` cases
algebraically. The remaining gap is **proving `M ≥ 2` never
produces an FO triple**, which is exactly what Parthasarathy's
supplement attempts via base-`i` subordination. The proof there
isn't airtight either (Stijn's example may belong to the `M ≥ 2`
case where the subordinate analysis is supposed to fire, but
doesn't).

## Where this leaves us

**The conjecture is open and structurally well-understood.**
We have:

1. **Computational baseline to `n = 10⁷`** plus targeted family
   sweeps to `n ≈ 1.3 × 10⁸`. Open-source code.
2. **A partial algebraic framework** (Master identity, Cases A,
   B-α, B-β-i, Bridge) that handles most cases unconditionally.
3. **A pure-power dichotomy**: all known FO triples have
   `n − k_i = i^V` (M = 1), and the Carry Lemma settles them.
4. **A 200-line axiom-clean Lean foundation** with the master
   identity, carry lemma, tame prime, case B-α, FO characterisation,
   absorption identity, and the 8 specific FO triples.
5. **One identified structural gap** (Stijn's example): a class of
   configurations where the existing case analysis fails to
   produce a witness.

The closure path **is not "compute more `n`"** — Conglu already did
that, and the computation can be extended cheaply but produces
artifact-shop value. The closure path **is** the algebraic gap.
Two concrete attacks:

- **Fix the Cofactor Escape** so it handles Stijn's configuration.
  This is a small focused mathematical question.
- **Prove M ≥ 2 ⇒ not FO** unconditionally, removing dependence on
  the supplement's incomplete case analysis. Combined with the
  Carry Lemma for M = 1, this would close the proof.

Either is **genuine new mathematics**, in a problem that is hot,
has an active community, and where the relevant Lean infrastructure
already exists.

## Existing players and coordination

- **conglu** is listed as "Currently working on this problem" on
  the Erdős database. Their contribution so far is the
  computational baseline (n ≤ 10⁷, family sweeps to 10⁸).
- **Sriniketh Parthasarathy** posted the (now-invalidated) attempt
  in March/April 2026.
- **StijnC** identified the bug.
- **Thomas Bloom** is the database owner and ruled on the validity.

Before serious work, post on the leanprover Zulip
`#Formal-conjectures` thread and/or comment on the database
forum to declare intent and avoid duplication with conglu's
ongoing work. **Do not assume the field is empty.**

## Recommendation

Worth a target memo. The next memo (`0053-target-erdos-699`) should
lay out:

- Which attack route (fix Cofactor Escape vs. prove M ≥ 2 ⇒ not FO).
- The mathlib lemmas we'd reuse from Parthasarathy's 200-line
  Lean file.
- A line budget (probably proofs/erdos699/ in this repo, with
  `@[formal_proof using lean4 at "<url>"]` annotation upstream
  if we close it).
- Coordination plan (Zulip post, forum comment) before any push.
- Honest stop conditions: if neither attack route shows progress
  in two sessions, write the fail memo and pivot.
