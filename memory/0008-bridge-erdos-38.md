# Erdős 38 — bridge `erdos_problem_38 → erdos_38` (upstream signature)

**Status:** shipped (local) — bridge compiles, axioms clean.
**Date:** 2026-05-10 — 2026-05-10
**Related:** 0007 (proof — local reproduction of the Aristotle/Del-Vecchio
formalisation), 0006 (Lean-side Erdős catalogue), 0002 (survey).
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/38.lean`,
declaration `Erdos38.erdos_38` (still `:= by sorry` upstream — *not modified*).

## One-line summary

Closed the formulation gap that memo 0007 documented: produced a bridge that
proves the upstream `Erdos38.erdos_38` statement (re-stated under our v4.28.0
mathlib pin) sorry-free, using the existing `Erdos38.Proof.erdos_problem_38`
plus three pieces of formal-engineering plumbing (predicate translation,
cardinality-form coercion, and edge-case extension of `f` for `α ∈ {0, 1}`
and `N = 0`).

## Taxonomy — which 2×2 cell

**Goal 2 — Solving + Known proof** (lower-right of the 2×2 in `CLAUDE.md`).
The mathematical proof of Erdős 38 was already produced by GPT 5.5 Pro (cleanup
by Liam Price), and formalised by Aristotle / Matteo Del Vecchio (memo 0007).
**No new mathematics, and no new mathematical content beyond
`erdos_problem_38`, was produced here.** This work is purely *Lean
formal-engineering plumbing* to translate that proof into the upstream
statement signature.

## What changed since memo 0007

Memo 0007 reproduced `erdos_problem_38` (the asymptotic-additive-basis
formulation used by the Aristotle gist) but explicitly noted the open gap to
the upstream `Erdos38.erdos_38` (the weak-additive-basis formulation):

> So this memo does **not** discharge the `sorry` in
> `FormalConjectures.ErdosProblems.«38».erdos_38` literally; what it does is
> reproduce the proof at the formulation the upstream `formal_proof using`
> annotation already points to. Closing the remaining bridge `(erdos_problem_38)
> → (Erdos38.erdos_38)` is a genuine but mechanical follow-up.

This memo records that follow-up.

## Files added

```
proofs/erdos38/
├── Erdos38.lean                       # now imports Erdos38.Proof, .ProofBridgeLemmas, .Bridge
└── Erdos38/
    ├── Proof.lean                     # 1852 lines, unchanged from memo 0007
    ├── ProofBridgeLemmas.lean         # 176 lines, NEW — sparsity + sumset cardinality bound
    └── Bridge.lean                    # 275 lines, NEW — re-stated upstream theorem + proof
```

`formal-conjectures/FormalConjectures/ErdosProblems/38.lean` was **not modified**.
The catalogue (`catalogue/formal_conjectures_erdos.jsonl`) was **not modified**.

## What `Bridge.lean` does

The upstream `Erdos38.erdos_38` differs from our local `erdos_problem_38` in
three ways:

1. **Predicate.** Upstream: `Set.IsWeakAddBasis B` (`∃ n, ∀ a, ∃ m ≤ n, a ∈ m • B`,
   from `formal-conjectures/FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean`).
   Local: `IsAdditiveBasis B` (asymptotic order *exactly* `h`, from
   `Erdos38.Proof`).
2. **Cardinality term.** Upstream: `(Set.Ioc 0 N ∩ (A ∪ (A + {b}))).ncard`.
   Local: `unionTranslateCount A b N = countIn (A ∪ translateSet A b) N`.
3. **Precondition scope.** Upstream: for *all* `A`, *all* `N` (including
   `α ∈ {0, 1}` and `N = 0`). Local: assumes `0 < α < 1` and `0 < N`.

`Bridge.lean` reproduces verbatim the upstream `Set.IsWeakAddBasisOfOrder`,
`Set.IsWeakAddBasis`, and the `answer(...)` macro (so the restated theorem
matches upstream character-for-character), then proves the upstream signature
in three steps:

1. **Predicate bridge.**
   `not_isWeakAddBasis_of_sparse`: for any `B : Set ℕ` satisfying
   `(countIn B N + 1)^h / N → 0` for every `h`, `B` is not a weak additive
   basis. Proof: weak basis of order `n` means `[1, N] ⊆ ⋃_{m ≤ n} m • B`,
   so `N ≤ ∑_{m=0}^{n} (countIn B N + 1)^m ≤ (n+1)(countIn B N + 1)^n`,
   which contradicts the sparsity (cofinitely `(countIn B N + 1)^n / N <
   1/(n+1)`).
   The required sparsity for `constructB d` is exposed by
   `ProofBridgeLemmas.constructB_sparse` (re-derived from `d.sparse`, the
   `ShiftApproxData` field), so the predicate bridge specialises to give
   `not_isWeakAddBasis_constructB`.

2. **Cardinality bridge.**
   `unionTranslateCount_eq_ncard A b N` turns the local
   `(unionTranslateCount A b N : ℕ)` into the upstream `(Set.Ioc 0 N ∩
   (A ∪ (A + {b}))).ncard` via `translateSet A b = A + {b}` plus
   `Set.ncard_coe_finset`.

3. **Edge-case patching.**
   The bridge defines `f' : ℝ → ℝ` by
   `f' α = if 0 < α ∧ α < 1 then erdos_f α else 0`, so the upstream
   constraint `∀ α, 0 < α → α < 1 → f' α > 0` follows from `erdos_f_pos`,
   and we have `f' 0 = f' 1 = 0`. Then:
   * **`0 < α < 1`, `0 < N`** (the main case): apply `erdos_problem_38`
     directly.
   * **`α = 1`, `0 < N`** (`α ≥ 1` collapses since `α ≤ 1`): pick `b = 1`;
     since `schnirelmannDensity A = 1` forces `n ∈ A` for every `n ≥ 1`
     (via `schnirelmannDensity_eq_one_iff`), `Set.Ioc 0 N ∩ (A ∪ ...) =
     Set.Ioc 0 N`, with cardinality `N = (1 + 0) · N = (α + f' α) · N`.
   * **`α = 0`, `0 < N`** (`α ≤ 0` collapses since `α ≥ 0`): pick `b = 1`;
     `(α + f' α) · N = 0 ≤ ncard`.
   * **`N = 0`**: pick `b = 1`; `Set.Ioc 0 0 = ∅`, both sides zero.

`ProofBridgeLemmas.lean` provides the helper lemmas extracted from facts
that `Erdos38.Proof.constructB_not_basis` already establishes internally:
* `hSumset_eq_nsmul B h : hSumset h B = h • B` — bridges the local
  recursive sumset to mathlib's pointwise `nsmul`.
* `countIn_hSumset_le_pow B h N : countIn (hSumset h B) N ≤ (countIn B N
  + 1)^h` — repackages the inline cardinality bound, using `Set.mem_nsmul_iff_sum`,
  `Finset.card_nsmul_le`, and a Finset-coercion argument.
* `constructB_sparse d h : (countIn (constructB d) N : ℝ)^h / N → 0` —
  re-derived from `d.sparse h` (the structure field) via the identity
  `countIn (constructB d) N ≤ countIn (shiftSet d) N + 1` plus a
  binomial-expansion squeeze.

These helpers add no new mathematics — they only expose what the existing
proof of `constructB_not_basis` already proves.

## Side-by-side statement comparison

**Upstream (`formal-conjectures/FormalConjectures/ErdosProblems/38.lean:50–57`,
unchanged):**

```lean
@[category research solved, AMS 11, formal_proof using lean4 at
"https://www.erdosproblems.com/forum/thread/38#post-6131"]
theorem erdos_38 : answer(True) ↔
    ∃ B : Set ℕ, ¬ B.IsWeakAddBasis ∧ ∃ f : ℝ → ℝ, (∀ α, 0 < α → α < 1 → f α > 0) ∧
      ∀ (A : Set ℕ) (N : ℕ),
        let α := schnirelmannDensity A
        ∃ b ∈ B, (Ioc 0 N ∩ (A ∪ (A + {b}))).ncard ≥ (α + f α) * N := by
  sorry
```

**Bridge (`proofs/erdos38/Erdos38/Bridge.lean`, restated):**

```lean
open Set in
theorem erdos_38 : answer(True) ↔
    ∃ B : Set ℕ, ¬ B.IsWeakAddBasis ∧ ∃ f : ℝ → ℝ, (∀ α, 0 < α → α < 1 → f α > 0) ∧
      ∀ (A : Set ℕ) (N : ℕ),
        let α := schnirelmannDensity A
        ∃ b ∈ B, (Ioc 0 N ∩ (A ∪ (A + {b}))).ncard ≥ (α + f α) * N := by
  ...
```

The two theorem bodies match character-for-character (modulo whitespace and
the `@[category ...]` / `@[AMS ...]` / `formal_proof using` attributes,
which are upstream metadata and not part of the signature).

The `Set.IsWeakAddBasis` and `answer(...)` definitions are reproduced
verbatim from upstream:
* `Set.IsWeakAddBasisOfOrder A n := ∀ a, ∃ m ≤ n, a ∈ m • A`,
  `Set.IsWeakAddBasis A := ∃ n, A.IsWeakAddBasisOfOrder n`
  — copied from
  `formal-conjectures/FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean`,
  written out additively (the upstream version is the additive form generated
  by `to_additive` from `IsWeakMulBasis`).
* `answer(...)` — a standalone macro `macro_rules | answer($t) => $t`. This
  matches the upstream `alwaysTrue`-mode behaviour for `answer(t)` when `t`
  elaborates as a term (which is the case here: `answer(True)` becomes `True`).
* Both projects are Apache 2.0; the bridge file's header preserves that
  attribution.

## `#print axioms` output (verbatim)

```
'Erdos38.erdos_38' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard mathlib axioms. **No `Lean.ofReduceBool`** (so no
`native_decide`), **no custom axioms**.

## Build evidence

From `/mnt/nvme2/atp_runs/claude_proving_new_mathematics/proofs/erdos38/`:

```
$ lake build
✔ [8028/8030] Built Erdos38.Bridge (≈9 s)
✔ [8029/8030] Built Erdos38 (≈6 s)
Build completed successfully (8030 jobs).
```

```
$ cat /tmp/axiom_check.lean
import Erdos38
#print axioms Erdos38.erdos_38
$ lake env lean /tmp/axiom_check.lean
'Erdos38.erdos_38' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What is new in *this* commit, and what is not

**Not new:**
* The mathematical proof of Erdős 38 (Liam Price + GPT 5.5 Pro; via
  `erdos_problem_38` from `Erdos38.Proof`).
* The Lean formalisation of that proof (Aristotle / Matteo Del Vecchio).
* The choice of mathlib version (v4.28.0).
* The internal sparsity bound and the h-fold sumset cardinality bound — both
  are already established by the proof of
  `Erdos38.Proof.not_basis_of_sparse` and
  `Erdos38.Proof.constructB_not_basis`. `ProofBridgeLemmas.lean` only
  *exposes* them as public lemmas.

**New here (the actual deliverable of this memo):**
* `proofs/erdos38/Erdos38/ProofBridgeLemmas.lean` — 176 lines. Public
  re-derivation of the sparsity facts that `constructB_not_basis` already
  establishes inline.
* `proofs/erdos38/Erdos38/Bridge.lean` — 275 lines. Reproduces the upstream
  `Set.IsWeakAddBasis` definition and the `answer(...)` macro, then proves
  the upstream `Erdos38.erdos_38` statement under our v4.28.0 mathlib pin
  by combining `erdos_problem_38` with the predicate bridge, the
  cardinality bridge, and the `α ∈ {0, 1}` / `N = 0` edge-case patches.
* The updated library root `Erdos38.lean` exporting all three modules.

## Important caveat — what this bridge is *not*

`Erdos38.erdos_38` proven in `Bridge.lean` is a **copy of the upstream
statement re-stated under our v4.28.0 mathlib pin**. It is *not* the same
Lean term as the upstream-file declaration: the upstream file
(`formal-conjectures/FormalConjectures/ErdosProblems/38.lean`) is unchanged,
on mathlib v4.27.0, with `:= by sorry`.

In particular, the catalogue (`catalogue/formal_conjectures_erdos.jsonl`)
will *still* show the upstream `Erdos38.erdos_38` as
`has_sorry_free_proof = False`, and that is correct — this bridge does
*not* modify the upstream file.

What the bridge proves is an *equivalent* statement under v4.28.0, where
"equivalent" means: the theorem signature matches the upstream signature
character-for-character (`Set.IsWeakAddBasis`, `Set.Ioc`, `answer(True)`,
all reproduced verbatim), modulo the v4.27.0/v4.28.0 mathlib drift.

A future port — when `formal-conjectures` upgrades to v4.28.0, or when
someone backports the v4.28.0 proof to v4.27.0 — could land the entire
package upstream as the actual `formal_proof using lean4 at "..."` target,
and at that point the upstream sorry would discharge against this bridge.

## Lessons

* When the bridge predicate (here, `IsWeakAddBasis B → IsAdditiveBasis B`)
  fails for general `B` but the conclusion (`¬ Set.IsWeakAddBasis B`) is
  still derivable directly from the *underlying property* used to prove
  `¬ IsAdditiveBasis B` (here, sparsity), the cheaper path is to re-do
  the negation argument under the weak-basis hypothesis. We tried the
  general predicate bridge first; ¬-asymptotic ⇒ ¬-weak fails for sets
  not containing 0 (natso26 noted this on the forum thread). The
  sparsity-direct route bypassed the gap entirely.
* `Finset.card_nsmul_le` (additive form of `Finset.card_pow_le`) is the
  right tool for h-fold sumset cardinality bounds — much cleaner than
  building the bound inductively over `Fin h` and `Fin.snoc`.
* `Set.mem_nsmul_iff_sum` gives the `∃ f : Fin h → ℕ, (∀ i, f i ∈ B) ∧
  ∑ f = a` characterisation directly, which is what the existing
  `not_basis_of_sparse` proof reaches for via a hand-rolled induction.
* `schnirelmannDensity_eq_one_iff` says `{0}ᶜ ⊆ A`, not `∀ n ≥ 1, n ∈ A`
  — same content but different unfolding shape; reach for it via a
  one-line wrapper.
* When two Finsets are extensionally equal but use different
  `DecidablePred` instances (here, the `Classical.dec`-derived filter
  inside `countIn` vs the `Finset.coe`-derived filter inside the bridge),
  `Finset.card_bij (fun a _ => a)` plus `aesop` is a clean discharge.

## Next

* Catalogue stays as-is — the upstream sorry is unchanged. The optional
  follow-up identified in memo 0007 is now done (this memo is exactly
  that follow-up).
* When `formal-conjectures` upgrades to mathlib v4.28.0 (their call,
  not ours), this bridge can be moved up into `Erdos38.erdos_38` itself
  (or pointed at via a single-line `formal_proof using lean4 at "..."`
  annotation pointing at our repo).
