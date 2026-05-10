# `Erdos38.erdos_problem_38` — reproducing the spicylemonade/Aristotle proof locally

**Status:** shipped (local) — proof compiles, axioms clean.
**Date:** 2026-05-10 — 2026-05-10
**Related:** 0002 (survey), 0004 (cambie — first Goal-2 inline proof), 0006 (Lean-side Erdős catalogue).
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/38.lean` — declaration `Erdos38.erdos_38`. Annotation `@[formal_proof using lean4 at "https://www.erdosproblems.com/forum/thread/38#post-6131"]` already points at the (off-repo) Lean proof.

## One-line summary

Reproduced the 1852-line Aristotle/Del-Vecchio Lean formalisation of the
Liam Price + GPT 5.5 Pro positive solution to Erdős Problem 38, as a
self-contained Lake subproject (`proofs/erdos38/`) pinned to mathlib
v4.28.0; full build passes and `#print axioms` shows only the
standard core axioms.

## Taxonomy — which 2×2 cell

**Goal 2 — Solving + Known proof** (lower-right of the 2×2 in
`CLAUDE.md`). The mathematical proof was already produced by GPT 5.5
Pro (prompted by gebyjaff, cleaned up by Liam Price); a Lean
formalisation was already produced by Aristotle (Harmonic) with
cleanup by Matteo Del Vecchio. This memo records the *local
reproduction and verification* of that formalisation, plus the
catalogue/memo paperwork. **No new mathematics, and no new
formalisation, was produced here.**

## Source of the proof

- **Mathematical solution.** GPT 5.5 Pro, prompted by gebyjaff,
  cleaned up by Liam Price. The 28-page write-up is committed to
  `https://github.com/spicylemonade/erdos-38` as a PDF
  (`38.pdf`). The repo's git history is a single commit
  `bcb7d91` "Add files via upload".
- **Lean formalisation.** Aristotle (Harmonic), with cleanup by
  Matteo Del Vecchio, posted at
  [`erdosproblems.com/forum/thread/38#post-6131`](https://www.erdosproblems.com/forum/thread/38#post-6131)
  on 11:29 01 May 2026. The Lean source is a public gist:
  `https://gist.githubusercontent.com/madeve-unipi/690d2bd8f6e8304ba8b456f9db559747/raw/481e3c35de8dce7af70ec440e4e121f084a61860/Erdos38.lean`.
  The live editor link in the forum post pins it to `mathlib-v4.28.0`.
- **How obtained.** `curl` of the gist raw URL. `git clone` of
  `spicylemonade/erdos-38` only fetched the PDF (the repo contains no
  `.lean` file — the Lean version lives in the gist).

## Where the local copy lives

```
proofs/erdos38/
├── lean-toolchain          # leanprover/lean4:v4.28.0
├── lakefile.toml           # depends on mathlib rev v4.28.0
├── Erdos38.lean            # one-line root: import Erdos38.Proof
└── Erdos38/
    └── Proof.lean          # 1852 lines, verbatim copy of the gist
```

- `Erdos38/Proof.lean`: **1852 lines**, **56 top-level declarations**
  (`def` / `lemma` / `theorem` / `structure` / `noncomputable …`).
  The headline theorem is `erdos_problem_38` at lines 1837–1851; its
  proof body is 11 lines (it composes `shift_approx_exists`,
  `constructB_not_basis`, `erdos_f_pos`, `density_increment` — the
  work of the preceding ~1800 lines).
- `Erdos38.lean`: one-line library root that just re-exports
  `Erdos38.Proof`.

The file headers preserve the upstream credits verbatim:
> *Authors: Matteo Del Vecchio, Aristotle (Harmonic). Released under
> Apache 2.0 license. Formalized from a solution by Liam Price and
> GPT 5.5 Pro.*

`formal-conjectures/FormalConjectures/ErdosProblems/38.lean` was **not
modified**.

## Why a subproject (not an inline replacement of `Erdos38.erdos_38`)

Two independent reasons:

1. **Length.** 1852 lines vastly exceeds the upstream README's
   25–50-line inline budget.
2. **Mathlib version.** The proof uses mathlib v4.28.0
   (per the live editor pin); `formal-conjectures` is on v4.27.0.
   Backporting was out of scope for this memo.

Beyond those, there is a third issue worth recording for the
record (and for whoever picks up the next slice of Goal-2 work on
this problem):

3. **Statement mismatch — "weak" vs "asymptotic" additive basis.**
   - `formal-conjectures` formulates the theorem with
     `¬ B.IsWeakAddBasis` (where `IsWeakAddBasis` is from
     `FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean`:
     `∃ n, ∀ a, ∃ m ≤ n, a ∈ A^m` — "every `a` is a sum of *at most*
     `n` elements"). Erdős's docstring also calls out this "at most"
     reading explicitly, citing [Er56] p.135.
   - The Aristotle Lean file defines its own
     `IsAdditiveBasis B := ∃ h, ∀ᶠ n in Filter.atTop, n ∈ hSumset h B`
     — i.e. an **asymptotic** additive basis of order *exactly* `h`.
   - mdelvecchio noted this on the forum thread; natso26 confirmed
     in a reply that "the Lean matches the paper and that both use
     the asymptotic additive basis definition (which … is the
     stronger definition here)" — meaning ¬asymptotic-basis is a
     stronger conclusion than ¬weak-basis (when 0 ∈ B); but in
     general the implication `¬asymptotic ⇒ ¬weak` is *not* a
     trivial bridge for arbitrary `B`, since
     `IsWeakAddBasis → IsAsymptoticAddBasis` fails for sets that
     do not contain 0 (a weak basis of order k just gives a finite
     union of `mSumset m B` for m ≤ k covering ℕ, not a single
     `hSumset h B` covering a cofinite set). For the specific
     `B = {1} ∪ B₀` in the construction, working out a rigorous
     bridge is non-trivial and is not done here.

So this memo does **not** discharge the `sorry` in
`FormalConjectures.ErdosProblems.«38».erdos_38` literally; what it
does is reproduce the proof at the formulation the upstream
`formal_proof using` annotation already points to. Closing the
remaining bridge `(erdos_problem_38) → (Erdos38.erdos_38)` is a
genuine but mechanical follow-up — a candidate for a separate
memo if/when we pursue it.

## Mathlib lemmas it leans on

See the file — the proof uses several hundred mathlib lemmas. The
main families:

- `Finset` cardinality and bijection lemmas
  (`Finset.card_image_of_injective`, `Finset.card_bij`,
  `Finset.card_filter`, `Finset.card_union_of_disjoint`,
  `Finset.card_sdiff`, …).
- `Nat` order and arithmetic
  (`Nat.lt_pow_of_log_lt`, `Nat.pow_log_le_self`,
  `Nat.lt_pow_succ_log_self`, `Nat.pow_le_pow_right`,
  `Nat.cast_*`, `Nat.ceil_*`, …).
- `Real` / `Complex` analytic primitives
  (`Real.log`, `Complex.exp`, `Complex.norm_exp`,
  `Complex.normSq_eq_norm_sq`, `Complex.exp_eq_one_iff`,
  `Complex.abs_re_le_norm`, …) — Parseval/DFT-style use.
- `schnirelmannDensity` and its API
  (`schnirelmannDensity_nonneg`, `schnirelmannDensity_le_one`,
  the standard `countIn ≥ α · N` bound).
- `Filter.cofinite` / `atTop` lemmas (the asymptotic-basis
  definition lives in `Filter.atTop`).

## `#print axioms` output (verbatim)

```
'erdos_problem_38' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard mathlib axioms. **No `Lean.ofReduceBool`**
(so no `native_decide`), **no custom axioms**.

## Build evidence

From `/mnt/nvme2/atp_runs/claude_proving_new_mathematics/proofs/erdos38/`:

- `lake update` — fetched mathlib `rev v4.28.0` (commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`) and the standard
  transitive dependency set; pulled the precompiled mathlib cache
  (8010 files) from Azure.
- `lake build Erdos38.Proof` — completed in 127 s, no errors, no
  warnings: `✔ [8026/8026] Built Erdos38.Proof (127s)`.
- `lake build` — full project build: `✔ [8027/8028] Built Erdos38
  (7.1s)`, no warnings.
- `lake env lean Erdos38/AxiomCheck.lean` (temporary file,
  removed after the check) — printed the axiom line quoted
  above.

## What is new in *this* PR / commit, and what is not

**Not new (provenance carefully preserved):**
- The mathematical proof of Erdős 38 (Liam Price + GPT 5.5 Pro).
- The Lean formalisation (Aristotle / Matteo Del Vecchio).
- The choice of statement (asymptotic-additive-basis variant) and
  the entire chain of 56 definitions / lemmas in `Proof.lean`.

**New here (the actual deliverable of this memo):**
- A local Lake project pinned to mathlib `v4.28.0` that compiles
  the gist on our machine, with the standard cache.
- Verification: full build is warning-free, and
  `#print axioms erdos_problem_38` reports the clean
  `[propext, Classical.choice, Quot.sound]` set (i.e. no
  `native_decide`, no custom axioms).
- This memo, which records provenance, the version mismatch with
  upstream, the "weak vs asymptotic basis" statement-gap, and the
  honest scope claim.

Specifically, this work does **not** flip the catalogue's
`has_sorry_free_proof` for `Erdos38.erdos_38` to `True`: the
upstream declaration is still a `:= by sorry`, and the gist
proves a closely-related but syntactically different theorem. The
catalogue should continue to record `Erdos38.erdos_38` as
`has_sorry_free_proof = False` with `formal_proof_url` pointing
at the forum post.

## Lessons

- The `formal_proof using` annotation should be the first place
  to look for an existing solution — *but* it can point at a
  forum thread that itself points at a gist, not at a repo. The
  GitHub repo named in the docstring (`spicylemonade/erdos-38`)
  can hold the *paper* only, not the Lean.
- When the upstream proof was autoformalised against a different
  mathlib version (v4.28.0 vs the repo's v4.27.0), pinning a
  separate Lake subproject is cheaper than backporting.
- Mismatched `Definition` choices (weak vs asymptotic additive
  basis) between the upstream statement and the actual proved
  variant are easy to miss at a glance. Always re-check the
  precise predicates the proof file actually uses against the
  upstream statement.
- `lake exe cache get` is *not* needed when `lake update`
  already includes a successful Azure cache download.

## Next

- Optional follow-up: write the bridge `IsAsymptoticAddBasis B →
  IsWeakAddBasis B` (or rather its contrapositive specialised to
  the constructed `B = {1} ∪ B₀`) so that
  `FormalConjectures.ErdosProblems.«38».erdos_38` itself can be
  proved by importing `Erdos38.Proof`. This requires either
  backporting the v4.28.0 proof to v4.27.0, or upgrading
  `formal-conjectures` (the latter is upstream's call, not ours).
- Stage A slice 3: re-run the catalogue script to confirm it
  reflects the (unchanged) state of `Erdos38.erdos_38`.
