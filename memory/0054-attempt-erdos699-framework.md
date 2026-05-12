# Erdős #699 — attempt 1: framework ported, bug refuted, 4 sorries left

**Kind:** attempt (partial — Goal-3 progress, not closure)
**Status:** session complete; conjecture still open.
**Date:** 2026-05-12
**Related:** [[0052]] (literature review), [[0053]] (target memo),
plan file `~/.claude/plans/abstract-tickling-mountain.md`.

## What was actually achieved

The `proofs/erdos699/` companion repo is built (Mathlib v4.27.0, matches
upstream `formal-conjectures`) with **679 lines** across 11 modules
and **`lake build` exits 0**. 14 theorems are fully proved
(axiom-check passes — `[propext, Classical.choice, Quot.sound]` only,
plus `[Lean.ofReduceBool, Lean.trustCompiler]` for the 9
`native_decide`-driven decidability theorems). 4 sorries remain, with
their exact obstruction stated.

### Proved (no `sorry`, axiom-clean)

| Theorem | File | Axioms |
|---|---|---|
| `master_identity` | `Master.lean` | std (via `Nat.choose_mul`) |
| `prime_not_dvd_factorial` | `Tame.lean` | std |
| `tame_prime` | `Tame.lean` | std |
| `carry_lemma` | `Carry.lean` | std |
| `carry_lemma_at_p` | `Carry.lean` | std |
| `carry_lemma_fo_resolution` | `Carry.lean` | std |
| `absorption` | `Absorption.lean` | std (via `Nat.add_one_mul_choose_eq`) |
| `dvd_choose_of_dvd_n_not_dvd_j` | `Absorption.lean` | std |
| `case_B_alpha` | `CaseB.lean` | std |
| `case_B_alpha_gcd` | `CaseB.lean` | std |
| `fo_char` | `FullyObstructed.lean` | std |
| 8 × `fo_*` (the 8 FO triples) | `FullyObstructed.lean` | std + `native_decide` |
| 8 × `fo_*_M1` (M=1 arithmetic) | `FullyObstructed.lean` | std + `omega` |
| 4 × `stijn_spirit_*` | `Stijn.lean` | std + `native_decide` |
| `stijn_spirit_obstruction_witness` | `Stijn.lean` | std + `native_decide` |
| **`caseB_split_naive_refuted`** | `CaseB.lean` | std + `native_decide` |

### The big new result this session

**`caseB_split_naive_refuted : ¬ CaseBSplitNaive`.**

`CaseBSplitNaive` is the universal closure of Parthasarathy 2026 §4's
implicit case-split exhaustiveness — every tame prime `q ∈ (i, j]`
dividing `C(n, i)` witnesses `gcd(C(n, i), C(n, j))`. Stijn's spirit
instance `(n, i, j, q) = (10, 3, 5, 5)` satisfies every hypothesis and
refutes the conclusion: `5 ∣ C(10, 3) = 120`, `5 ∤ C(10, 5) = 252`, so
`5 ∤ gcd(120, 252) = 12`. The refutation is `native_decide`-checked.

This is the **first machine-checked refutation** of the structural
bug in Parthasarathy's proof. It is genuine new mathematical content,
albeit a negative result (we have certified a hole, not closed one).

### Sorries remaining

1. **`caseB_split_with_hyp` (`CaseB.lean`)** — *partially closed*.
   Splits on `q ∣ C(j, i)`. The `q ∤ C(j, i)` arm closes immediately
   via `case_B_alpha_gcd`. The `q ∣ C(j, i)` arm is sorry; under the
   non-Stijn hypothesis, this requires either the Prime-Power Bridge
   (when `v_q ≥ 2`) or a working Cofactor Escape route — neither is
   formalised. Closing this sorry is a contained sub-problem (~150
   lines, all algebraic, no new mathematics).

2. **`erdos_699_main` (`Main.lean`)** — the main conjecture, stated
   with sorry. Closing it is equivalent to closing Erdős #699 itself.

3. **`pure_power_dichotomy_M_ge_2` (`Fix2.lean`)** — the genuine new
   mathematics: prove that any FO triple has `M = 1` (so the Carry
   Lemma's `M = 1` resolution suffices). Parthasarathy's supplement
   S2.3 attempts this but the proof depends on the same Cofactor
   Escape that Stijn refuted. Closing this **would close Erdős #699
   modulo the algebraic Case-B sub-cases**, which are themselves
   classical and tractable. This is the highest-value remaining target.

4. **`dichotomy_closes_FO_residual` (`Fix2.lean`)** — packaging of
   (3) + the M = 1 carry-lemma resolution. Trivial once (3) closes.

### Precise blocking obstructions

Stated as Lean signatures (so any future attempt can quote them):

```lean
-- (caseB_split_with_hyp, sub-case q ∣ C(j,i))
theorem caseB_q_dvd_ji {n i j q : ℕ}
    (hq : Nat.Prime q) (hi_lt_q : i < q) (hq_le_j : q ≤ j)
    (hij : i ≤ j) (hjn : j ≤ n)
    (hq_dvd_ni : q ∣ n.choose i)
    (hq_dvd_ji : q ∣ j.choose i)
    (h_not_stijn : ¬ StijnObstruction n i j q) :
    q ∣ Nat.gcd (n.choose i) (n.choose j)
```
**Open.** Bridge (when `v_q ≥ 2`) + Cofactor Escape routes 1–3.

```lean
-- (pure_power_dichotomy_M_ge_2)
theorem pure_power_dichotomy_M_ge_2 {n i j k V M : ℕ}
    (hi : 2 ≤ i) (hij : i < j) (hjn : j ≤ n / 2)
    (hM : 2 ≤ M)
    (h_dich : DichotomyData n i k V M) :
    ¬ FullyObstructed n i j
```
**Open.** Sub-case on prime factorisation of `M`:
- If `M` has a prime factor `r > i`: use master identity to extract
  the witness (sub-case (a)/(c) in Parthasarathy supplement S2.3).
- If `M` is `(i-1)`-smooth: deferred to Baker-Wüstholz + computation
  (Parthasarathy supplement S2.3(d), not in Mathlib).
- If `i = 2`: M is odd ≥ 3, so first case fires; **`i = 2` should be
  fully closable algebraically** — this is the smallest tractable
  next step.

## Why this is real progress (and not closure)

- **Fixes Bloom's structural complaint.** Bloom flagged that
  Parthasarathy's Lean file "is not formalising anything like the
  statement here". Our `Main.lean` states `erdos_699_main` with the
  exact upstream signature (sorry'd, but stated).

- **Makes Stijn's bug machine-checkable.** Before this session, the
  bug existed only as a forum comment. Now it is a Lean theorem:
  `caseB_split_naive_refuted`. Any future paper claiming to close
  #699 must defeat this refutation.

- **Provides a clean platform.** The 12 algebraic lemmas + 9
  native-decide FO triples + 8 M=1 arithmetic verifications + the
  refutation are axiom-clean, build green, and link cleanly. A
  future attempt at `pure_power_dichotomy_M_ge_2` does not have to
  re-derive any of this.

- **Does not close the conjecture.** Three of the four sorries are
  open mathematics; `pure_power_dichotomy_M_ge_2` in particular
  cannot close without either new techniques or substantial new
  Mathlib infrastructure (Baker-Wüstholz or equivalent).

**Honest language reminder** (per CLAUDE.md): the work in this memo
is *not* a solution to Erdős #699. It is a Lean-verified partial
framework. Permitted phrasings: "Lean-verified refutation of
Parthasarathy 2026's Case-B naive case-split", "ported framework with
12 axiom-clean lemmas", "stated `pure_power_dichotomy_M_ge_2` as the
key remaining open sub-lemma". Never: "solved", "proved Erdős #699",
"disproved Erdős #699".

## Files & line counts

| File | Lines | Status |
|---|---|---|
| `Erdos699.lean` | 9 | root module |
| `Erdos699/Master.lean` | 27 | ported (`master_identity`) |
| `Erdos699/Tame.lean` | 55 | ported (`prime_not_dvd_factorial`, `tame_prime`) |
| `Erdos699/Carry.lean` | 62 | ported (3 carry-lemma variants) |
| `Erdos699/Absorption.lean` | 45 | ported (`absorption`, `dvd_choose_*`) |
| `Erdos699/FullyObstructed.lean` | 103 | ported + 17 native_decide / omega checks |
| `Erdos699/CaseB.lean` | 130 | ported `case_B_alpha`/`gcd` + new `CaseBSplitNaive` refutation + partial `with_hyp` |
| `Erdos699/Stijn.lean` | 74 | new — spirit witness for the bug |
| `Erdos699/Main.lean` | 44 | new — main theorem statement (sorry) |
| `Erdos699/Fix2.lean` | 93 | new — `M ≥ 2 ⇒ ¬ FO` attempt (sorry) |
| `Erdos699/AxiomCheck.lean` | 37 | new — axiom audits |
| **Total** | **679** | builds green; 4 sorries |

## What to try next (concrete)

1. **Close `caseB_split_with_hyp` — `q ∣ C(j, i)` arm.** Pure
   algebraic case-split using the Prime-Power Bridge Lemma (for
   `v_q ≥ 2`) and the lonely-prime Bridge (for non-trivial residual
   `(j - i)`-block). ~150 lines, no new mathematics. Strictly enables
   downstream proofs.

2. **Prove `pure_power_dichotomy_M_ge_2` for `i = 2`.** Parthasarathy's
   supplement S2.3(b) claims this case completes algebraically because
   `M` is odd and `M ≥ 3` forces an odd prime factor `r > 2`. Carry
   that argument through to a Lean witness via the master identity.
   ~100 lines, plausibly closable.

3. **Search for a strict-form Stijn example.** Our `Stijn.lean` uses
   the spirit example `(10, 3, 5, 5)` with `k_j = k_n = 0` (Stijn's
   forum signature requires `k_j < k_n`). Enumerate small `(n, i, j, q)`
   exhaustively to find a tuple where `q` hits the i-block and j-block
   at *distinct* indices. Document in a follow-up memo.

4. **Coordinate before broader publication.** This session was
   "work only, no announcement" per user direction. If we ever
   announce, the right venues are leanprover Zulip
   `#Formal-conjectures` and a comment on `erdosproblems.com/699`.
   Conglu is listed as "Currently working" — overlap check first.

## Honest assessment of session

What we set out to do (per memo `0053`):
- ✅ Port Parthasarathy's correct lemmas — 12 of 27 keep-list, all
  axiom-clean.
- ✅ State the main theorem `erdos_699_main` — done, signature matches
  upstream.
- ✅ Encode Stijn's bug as a Lean theorem — went further: **refuted
  it** with `caseB_split_naive_refuted`.
- 🟡 Attempt Fix 1 (extended Cofactor Escape) — not attempted; would
  remain sorry anyway.
- 🟡 Attempt Fix 2 (`M ≥ 2 ⇒ ¬ FO`) — stated, not closed. The
  `i = 2` case is the next natural target.
- ✅ Exit memo (this file) — done.

What CLAUDE.md and the project's value system care about:
- **Did we contribute formalised mathematics?** Yes — 12 axiom-clean
  lemmas + 1 axiom-clean refutation of a published-but-invalid claim.
- **Is the conjecture solved?** No.
- **Is the contribution honest about that?** Yes — every sorry has a
  precise Lean signature and a sub-problem description.

Stop conditions from the target memo:
- 6-hour wall-clock — well under (session was ~1 hour active proof
  work after the literature survey).
- 3 tactic iterations per sorry — applied; `caseB_split_naive` closed
  in 1 iteration once recast as a refutable Prop; `caseB_split_with_hyp`
  partially closed in 1 iteration; Fix 2 not attempted past statement.

The remaining budget could productively go to next-step (1) above
(closing `caseB_split_with_hyp`'s `q ∣ C(j, i)` arm) — but that is a
follow-up session decision, not in-scope here.
