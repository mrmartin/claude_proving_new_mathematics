# Target: Erdős #699 — port Parthasarathy + encode Stijn's bug + attempt fix

**Status:** in-progress
**Date:** 2026-05-12 (start)
**Related:** [[0050]] (Erdős 64 stop-and-wrap), [[0051]] (pincer scan),
[[0052]] (Erdős 699 literature & state-of-the-art).
**Upstream link:**
`formal-conjectures/FormalConjectures/ErdosProblems/699.lean`
(three sorries — `sylvester_schur`, `erdos_699`, `erdos_szekeres_strengthening`).
**Plan file:** `~/.claude/plans/abstract-tickling-mountain.md`.

## 2×2 cell

**Goal 3** (lower-left of the project's `Defining × Solving` /
`Known proof × No known proof` matrix). The conjecture is open as of
2026-05-12; no informal proof exists; an attempted proof from March 2026
was just invalidated yesterday. We are attempting to make progress on a
genuinely open problem, with realistic probability of full closure well
under 5 % per session.

## Status check against upstream + community

- **erdosproblems.com/699** says OPEN as of 2026-05-12.
- **Bloom (database owner)** declared Parthasarathy 2026 invalid on
  2026-05-11. The Lean code in that attempt does not formalise the main
  statement — it proves modular lemmas only.
- **Conglu** is listed as "Currently working on this problem". Their
  contribution is computational (Rust scanner to `n ≤ 10⁷` plus targeted
  family sweeps to `n ≈ 1.3 × 10⁸`, open-sourced at
  `github.com/conglu1997/erdos_699_rust`).

Per user direction this session: **no Zulip post, no forum comment, no
PR**. The work is internal to our private repo.

## Goal of this attack

Three concrete deliverables, in order of guaranteed-ness:

1. **Port Parthasarathy's 23 mathematically-correct Lean lemmas** into a
   structured companion repo at `proofs/erdos699/`, building against
   Mathlib v4.27.0 (matches upstream `formal-conjectures` pin). Replace
   4 of his 27 theorems with their Mathlib equivalents (master identity
   becomes `Nat.choose_mul`; absorption becomes `Nat.succ_mul_choose_eq`).
   Verify axiom-cleanliness with `#print axioms`.

2. **State the main theorem** (`erdos_699_main`) — Parthasarathy's file
   never did. Signature matches upstream's `erdos_699`. Body is `sorry`.
   This is **not** an upstream contribution (defining-only PRs are
   forbidden by CLAUDE.md) — it is a local target. The point: fix
   Bloom's "the Lean code is not formalising the statement here" by
   stating the statement in our own repo.

3. **Encode Stijn's bug + attempt one or two fixes.** In `CaseB.lean`,
   state both `caseB_split_naive` (the buggy claim) and
   `caseB_split_with_hyp` (the strengthened, *correct* form with explicit
   non-simultaneity hypothesis). The strengthened form makes the gap
   machine-checkable: any future close must remove the non-simultaneity
   hypothesis or supply a separate witness in the simultaneity case.

Attack routes for closing the gap:

- **Fix 1** — extend Cofactor Escape with a fourth route that handles
  Stijn's "simultaneous tame-prime hits in i-block and j-block with
  v_q = 1 on both, empty (j−i)-block" configuration. Low probability of
  closure; the value is forcing the precise sub-lemma into a Lean
  signature.

- **Fix 2** — prove the Pure-Power Dichotomy unconditionally:
  `M ≥ 2 ⇒ not FullyObstructed`. Combined with the M = 1 case (already
  proved by Parthasarathy's `carry_lemma_fo_resolution`), this would
  close the FO residual *unconditionally*. Combined with Case A and the
  algebraic Case B sub-cases B-α / B-β-i / Bridge, this closes
  `erdos_699_main`. **This is genuine open mathematics** — the place to
  spend the session's mathematical effort.

  Tactic angles for Fix 2: (a) direct base-`i` Kummer carry analysis via
  `Nat.factorization`; (b) sub-case on prime factorisation of M (if M
  has a prime factor `> i`, master identity gives a witness; else M is
  `(i−1)`-smooth, which is the residual sub-case where the analysis
  becomes genuinely hard).

## Mathlib lemmas we will lean on

(From the Phase-1 Mathlib survey in the plan file.)

- `Nat.choose_mul` — master identity.
- `Nat.succ_mul_choose_eq` — absorption.
- `Nat.Prime.multiplicity_choose` — Kummer's theorem (carry-count form).
- `Nat.Prime.emultiplicity_factorial` — Legendre's formula.
- `Nat.add_choose_eq` — Vandermonde antidiagonal.
- `Nat.Prime.dvd_choose_add`, `Nat.Prime.dvd_choose`,
  `Nat.Prime.dvd_choose_self`, `Nat.Prime.coprime_choose_of_lt` —
  prime-divides-binomial helpers.
- `Choose.choose_modEq_choose_mod_mul_choose_div` — Lucas's theorem.
- `Nat.factorization` and base-`p` digit machinery (`Nat.digits`,
  `Nat.factorization_choose_le_log`, `Nat.factorization_choose_le_one`).

What Mathlib **lacks** and we will not formalise this session:
**Sylvester-Schur** (we will state it locally with `sorry` for use in
Case A; we will not attempt the classical proof from
Bertrand + prime-counting). **Baker-Wüstholz / S-unit equation effective
finiteness** (this is the wall blocking Parthasarathy's FO bound
formalisation; out of scope).

## Out of scope (explicit)

- Sylvester-Schur as an upstream Goal-2 contribution (user direction:
  pure #699 attempt only).
- Any Mathlib API extension beyond ~50 lines of local helpers.
- The third upstream sorry (`erdos_szekeres_strengthening`) — variant
  conjecture, not the main target.
- The 16-page Parthasarathy PDF's full case-by-case re-formalisation
  (only the structural framework, not the explicit case enumeration
  for `n ≤ 4400, i ≤ 23`).
- External announcements (Zulip, forum, PR) per user direction.

## Line budget

| Component | Estimated lines |
|---|---|
| `proofs/erdos699/lakefile.toml` + skeleton | ~30 |
| Master identity + algebraic prelims (`Master.lean`) | ~80 |
| Tame prime + helpers (`Tame.lean`) | ~40 |
| Sylvester-Schur local statement (`SylvesterSchur.lean`) | ~40 (sorry-bodied) |
| Case A (`CaseA.lean`) | ~60 |
| Case B framework (`CaseB.lean`) — includes bug encoding | ~200 |
| Cofactor Escape — 3 routes + Fix 1 (`CofactorEscape.lean`, `Fix1.lean`) | ~300 (mostly sorry) |
| Fully-Obstructed structure (`FullyObstructed.lean`) | ~120 |
| Carry lemma + M=1 FO resolution (`Carry.lean`) | ~80 |
| Absorption + `i=1` case (`Absorption.lean`) | ~50 |
| Stijn's example (`Stijn.lean`) | ~100 |
| Main theorem statement (`Main.lean`) | ~80 |
| Fix 2 (`Fix2.lean`) | ~200 (mostly sorry, possibly closing) |
| **Total** | **~1380** |

## Hard stop conditions

- **6 wall-clock hours** total in proof project (excluding this memo
  and the exit memo), OR
- **3 Lean-tactic-iteration cycles per sorry** without progress, OR
- User calls time.

On stop, write `memory/0054-{fail|attempt}-erdos699.md` recording
every closed lemma's axiom check, every remaining `sorry` with its
exact Lean signature, the Stijn witness's certificate, line counts,
and concrete "what to try next" for any future continuation.

## Go / no-go

**Go.** The framework + Stijn encoding + Main statement are
high-probability deliverables (close to 100%). Fix 2 is genuinely
research-grade mathematics — its closure is unlikely in-session but
plausible enough that an attempt is worthwhile. Even a fail-memo
exit produces real value: a Lean-checkable formal framework + the
bug stated as a sorry'd theorem, which is concrete progress over the
state of the art as of 2026-05-12.

**Coordination plan: none, per user direction.** Risk note: Conglu
publishing a fix mid-session is acceptable risk under "work only, no
announcement".

## Honest language reminder (per CLAUDE.md)

No commit, memo, or PR may use "solved", "proved", or "disproved"
about Erdős #699 unless a complete proof or verified counterexample
is in hand and quadruple-checked. Permitted phrasing: *"Lean-verified
partial framework for Erdős #699"*, *"port of Parthasarathy's 2026
algebraic lemmas, with Stijn's gap encoded as a `sorry`-bodied
theorem"*, *"attempted Fix 2 (`M ≥ 2 ⇒ not Fully Obstructed`),
status: <closed | partial | sorry>"*.

## Next

Stage 1: create `proofs/erdos699/` skeleton (lakefile, lean-toolchain,
empty modules). `lake build` must exit 0 on the empty skeleton before
any non-trivial proof goes in.
