# Open-Erdős pincer scan — find problems closable by "tighten both ends"

**Kind:** survey
**Status:** scan complete; recommendation pending pick.
**Date:** 2026-05-12
**Related:** 0050 (Erdős 64 wrap), 0006 (catalogue scope).
**Artefacts:** `catalogue/pincer_scan.py`, `catalogue/pincer_ranking.json`.

## Goal

After Erdős 64 was wound down (memo 0050), the next target should be an
*open* Erdős problem with a **pincer shape**:

- An independent lower-end result (closed cases for small parameters).
- An independent upper-end result (asymptotic / "for large enough X" /
  effective bound) using different mathematical machinery.
- A finite gap between them.
- Both ends **unconditional** — closing the gap should yield an
  *unconditional* proof, not one contingent on a famous open conjecture.

The thesis (from the user): pincer problems are where modern tooling has
the biggest comparative advantage over Erdős. Each end can be improved
incrementally with different techniques (computer algebra on one side,
modular forms / Galois reps / sieves on the other), and when they meet
the problem is settled outright.

## Method

1. Crawled `erdosproblems.com/prizes/{0,10,…,10000}` and parsed all
   1217 problem boxes. 665 are currently OPEN / VERIFIABLE / FALSIFIABLE.
2. Batch-fetched `erdosproblems.com/N` for all 665 open problems
   (`/tmp/erdos_pages/p${N}.html`, 22 MB total).
3. Extracted the "remarks" block on each page and ran LaTeX-aware regex
   matchers for **lower-side** evidence (`$a\leq k\leq b$`,
   "verified for $n\leq …$", "no solutions below", "impossible for k≤…"),
   **upper-side** evidence ("for $k$ sufficiently large", "only finitely
   many", "$k\ll …$", "depending only on", "for all k≥…"), and
   **wall-conjecture** mentions (Riemann, ABC, Legendre, Schinzel,
   Hardy-Littlewood, BSD, Goldbach, transcendence, Continuum, …) plus
   "hopeless"/"beyond our ability" language.
4. Scored: +3 for lower, +3 for upper, +8 if both, +1 per distinct
   pattern, −6 per hard blocker (RH/GRH), −1 per soft blocker (ABC,
   Schinzel, etc.), −5 per hopeless phrase.
5. Filtered to problems with both bounds, no hard blockers, no
   "hopeless" language. Sorted by score.

## Top 10 ranked candidates

| Rk | # | Pincer (lower ↔ upper) | Closure path | Verdict |
|----|---|------------------------|--------------|---------|
| 1 | **672** | `4 ≤ k ≤ 34` impossible (Euler→Obláth→GHS→BBGH→GHP) ↔ `k` sufficiently large with `ℓ > exp(10^k)` impossible (Bennett-Siksek 2020) | Push GHP's explicit Diophantine case-by-case past k=34; sharpen BS's exp(10^k) constant downward. Both ends unconditional. | **Textbook pincer.** Deep but accessible Diophantine machinery (Thue equations, Chabauty, modular Galois reps). Magma + mathlib. |
| 2 | **1108** | Mahler-Erdős: for `k ≤ 4` infinitely many squares in `A_k=Σk^n` (Mahler) ↔ Brindza-Erdős effective bound for powerful factorial sums | Per-fixed-k attack via linear forms in p-adic logarithms; explicit characterisation of squares in `A_k` for k=5,6,7,…. | Tractable per-k. Effective Baker-style bounds + computer search. |
| 3 | **188** | Erdős-Graham red-blue colouring: `k ≥ 6` proven (Tsaturian 2017) ↔ Erdős-Graham "claim `k ≤ 10^7`, no proof" | Provide the missing upper-bound proof (Ramsey-theory contribution) and extend lower bound by SAT/structural arguments. | Real pincer but upper bound is currently **only heuristic** — no published proof. Closing it is a new theorem on each side. |
| 4 | **374** | `D_k = {m : F(m)=k}` (factorial-product squares): `D_2 = {n^2}` settled, `D_k = ∅` for `k > 6` settled ↔ growth rates of `|D_k ∩ {1..n}|` for `k ∈ {3,4,5,6}` open | Per-k asymptotic analysis; least element of D_6 is 527, so very explicit. | Asymptotic per-k, 4 specific values. Less "finite gap"; more "fill in growth-rate per k". |
| 5 | **261** | Erdős `n/2^n` representation: verified `n ≤ 10 000` (Tengely-Ulas-Zygadlo 2020) ↔ Borwein-Loring constructive infinite family `n = 2^{m+1} − m − 2` | Characterise all `n`, not just exhibit infinitely many. | Less clean — both sides confirm existence; the question is the precise set. |
| 6 | **436** | Λ(k,l) consecutive l-th-power residues: many specific Λ(k,l) computed ↔ Hildebrand 1991 (unconditional): Λ(k,2) finite for all k | Remaining open: Λ(k,3) for odd k ≥ 5, plus growth rates. Extend Hildebrand's method. | Unconditional, but pincer is in (k,l) plane not a clean 1-axis range. |
| 7 | **180** | Erdős-Simonovits Turán density: Erdős-Stone gives bipartite case ↔ Hunter's folklore counterexample for some F | Closure: characterise which F obey the conjecture. | Structural, not "tighten ends". |
| 8 | **1158** | Hypergraph Turán density: `n^{t−O(r^{1−t})}` ↔ `≪ n^{t−r^{1−t}}` (both Erdős 1964) | Improve exponent in lower-order terms. | Asymptotic pincer in exponent — not "finite gap" shape. |
| 9 | **389** | Erdős-Straus AP divisibility: `1 ≤ n ≤ 18` computed (Bhavik Mehta, OEIS A375071) ↔ existence for `n ≥ 1` | Push compute + extend asymptotic. | Has compute lower end; upper-end status needs re-reading. |
| 10 | **683** | Sylvester-Schur for binomials: `P(C(n,k)) ≫ k log k` proved ↔ heuristic `> e^{c√k}` | Sharpen lower bound on largest prime divisor. | Asymptotic-only; not finite gap. |

**Near-misses (wall-blocked):**

- **#375 (Grimm)** — pincer `Laishram-Shorey n ≤ 1.9×10^10` ↔
  `Ramachandra-Shorey-Tijdeman k ≪ (log n / log log n)^3`, but closing
  the gap *implies Legendre's conjecture*. Wall.
- **#252 (Erdős factorial irrationality)** — `1 ≤ k ≤ 4` proven
  unconditionally (Pratt 2022 closed k=4), but the only known upper
  bound for all k is conditional on Schinzel/Dickson. Wall unless
  alternative analytic route exists.
- **#398 (Brocard)** — `n ≤ 10^9` searched, Naciri 2025 closed
  "x±1 7-free" unconditionally. The remaining open case (x±1 has prime
  power factor ≥ 7) is not blocked by ABC — Naciri's path is
  unconditional. **Should be considered alongside top tier.**

## Recommendation

**Primary pick: Erdős #672 (perfect-power arithmetic progression).** It
matches the user's stated shape almost exactly:

- Lower end: explicit-k impossibility, currently k=34 (5 papers
  built up from k=4 between 1951 and 2009 — incremental, exactly the
  "tighten" mode).
- Upper end: Bennett-Siksek's exp(10^k) threshold on ℓ for k
  sufficiently large — a published, unconditional bound with an
  *enormous* constant that nobody has tried to sharpen.
- Gap: `35 ≤ k ≤ K₀` with `ℓ ≤ exp(10^k)`. Finite-shaped, attackable
  on both ends with **different machinery**: per-k Thue/Chabauty on
  the bottom, modular Galois rep constant-sharpening on the top.
- Unconditional both sides.

Honest caveats:

- The Diophantine machinery on the lower end is hard. GHP 2009 took
  a year of explicit elliptic Chabauty work for k ≤ 34. We are not
  going to push to k = 35 in a session.
- mathlib's elliptic-curve / Diophantine geometry coverage is real
  but well below Magma's. We would need Magma (or PARI) doing the
  arithmetic geometry and Lean recording the proven cases.

**Secondary picks** (if we want something more session-tractable):

- **#1108 (Mahler-Erdős squares in `A_k=Σk^n`)** — per-fixed-k attack
  via Baker-style linear forms in p-adic logs. Effective Brindza-Erdős
  bound on the analytic side. Smaller-scale Diophantine.
- **#398 (Brocard)** — Naciri's unconditional "k-free" framework can
  potentially be extended. Computational lower end (10^9) is also
  pushable with modern factorisation. The pincer is tighter than #672
  in terms of accessible state-of-the-art.

**Disqualifications:**

- Pincer + wall conjecture (#375 Grimm, #252 factorial irrationality)
  — blocked unless we find an alternate analytic route.
- Asymptotic-only pincers (#1158 hypergraph density, #683
  Sylvester-Schur extensions) — not the "finite gap" the user wanted.

## Decision needed

One of:
- **#672** — biggest-deal pincer, deepest tools required.
- **#1108** — smaller-scale per-k attack, more tractable.
- **#398** — closest to "tight finite gap with active progress".

After the pick, the next memo is `0052-target-erdos-<n>.md` with the
informal proof strategy, mathlib lemma map, line budget, and
go/no-go verdict per CLAUDE.md target-memo template.

## Scan artefacts (kept)

- `catalogue/pincer_scan.py` — the matcher script.
- `catalogue/pincer_ranking.json` — full 665-problem ranked list, with
  per-problem lower/upper hits and blocker flags.
