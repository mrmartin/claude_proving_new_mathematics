# Erdős 457 — bridge from gist `erdos_457` to upstream `erdos_457` signature

**Status:** shipped (local) — bridge compiles, axioms clean.
**Date:** 2026-05-10 — 2026-05-10
**Related:** 0011 (target), 0009–0010 (Erdős 397 — same workflow), 0007–0008
(Erdős 38 — same workflow), 0006 (Lean-side Erdős catalogue).
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/457.lean`,
declaration `Erdos457.erdos_457` (still `:= by sorry` upstream — *not modified*).

## One-line summary

Reproduced Barreto/Aristotle's 342-line proof that there is `ε > 0` such that
infinitely many `n` have all primes `p ≤ (2 + ε) log n` dividing
`∏_{1 ≤ i ≤ log n} (n + i)`, in our v4.28.0 subproject (with two small drift
fixes), then wrapped with the trivial `answer(True) ↔ _` shim to match the
upstream signature character-for-character. Bridge file is 45 lines (the
smallest of our three bridges so far — gist already does the heavy lifting).

## Taxonomy — which 2×2 cell

**Goal 2 — Solving + Known proof** (lower-right of the 2×2 in `CLAUDE.md`).
Mathematics (GPT-5.2 Pro / Pilatte's argument with consecutive-primes
estimates plus binomial bounds) and Lean formalisation (Aristotle, Kevin
Barreto prompting) both belong to others. **No new mathematics; no new
formalisation.** Our deliverable is the local v4.28.0 reproduction
(plus drift fixes) plus the `answer(True)`-wrapping bridge.

## Source of the proof

- **Mathematical solution.** Cedric Pilatte's argument on the Erdős
  Problems Forum: apply Shiu's theorem (consecutive primes ≡ 1 mod q)
  with `l = q = d` to obtain consecutive primes near a residue, then
  use binomial bounds on `binom(2m, m)` plus simultaneous Diophantine
  approximation to construct an `n` with all primes ≤ `2.1 log n`
  dividing `∏ (n+i)`.
- **Lean formalisation.** Kevin Barreto prompted Aristotle (Harmonic) to
  fill the upstream `:= by sorry`, given an existing `thm_main`
  formalisation. Result: a single 342-line file at
  [`Woett/Lean-files/.../ErdosProblem457.lean`](https://github.com/Woett/Lean-files/blob/main/ErdosProblem457.lean).
- **How obtained.** `curl` of the GitHub raw URL.

## Where the local copy lives

```
proofs/erdos457/
├── lean-toolchain                # leanprover/lean4:v4.28.0
├── lakefile.toml                 # depends on mathlib rev v4.28.0
├── Erdos457.lean                 # one-line root: import Proof, Bridge
└── Erdos457/
    ├── Proof.lean                # 346 lines — Barreto/Aristotle gist
    │                             #             namespaced under Erdos457.Gist,
    │                             #             with v4.28.0 drift fixes
    └── Bridge.lean               # 45 lines — restated upstream theorem
```

`formal-conjectures/FormalConjectures/ErdosProblems/457.lean` was **not modified**.
The catalogue (`catalogue/formal_conjectures_erdos.jsonl`) was **not modified**.

## v4.24.0 → v4.28.0 drift fixes (two)

The original gist was generated against `Lean v4.24.0` + mathlib commit
`f897ebcf`. Two fixes were needed:

### 1. `Real.log_prod` signature change

Gist line 62:

```lean
rw [Real.log_prod _ _ fun x hx => Nat.cast_ne_zero.mpr <| ...] at h_log_prod_le
```

In v4.28.0 (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:384`),
`Real.log_prod` takes only one explicit argument (the `hf : ∀ x ∈ s,
f x ≠ 0` hypothesis); `s` and `f` are implicit. Fix:

```lean
rw [Real.log_prod (fun x hx => Nat.cast_ne_zero.mpr <| ...)] at h_log_prod_le
```

### 2. `erdos_457` body: norm_num deep-recursion bug

Gist's `erdos_457` (line 327 onward) used:

```lean
use 0.1; norm_num;
apply thm_main.mono; intro n hn; exact (by ...
```

Under v4.28.0 mathlib, `norm_num` after `use 0.1` triggers
`libc++abi: terminating due to uncaught exception of type lean::throwable:
deep recursion was detected at 'interpreter'`, with the stack trace cycling
through `evalLT → evalMul → evalDiv → evalMul → evalInv → evalMul`.
This is a pathological norm_num behaviour on the binding `(2 + 0.1) * Real.log n`
that v4.24.0 didn't trigger. Fix — rewrite the body to avoid the
ambiguous decimal literal and the wide-net `norm_num`:

```lean
refine ⟨(1 : ℝ) / 10, by norm_num, ?_⟩
apply thm_main.mono
intro n hn p hpb hp
have hF_def : F n = ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) := by
  simp [F, A_func]
rw [← hF_def]
exact hn p hp (by linarith)
```

The new body uses `(1 : ℝ) / 10` (no decimal literal in the goal after
`use`), splits the conjunction with `refine`, and replaces the awkward
inner `exact (by have hF_def := ...; ...)` with a direct
`intro / rw / exact / linarith` chain. Mathematical content is identical.

## What `Bridge.lean` does

The upstream `Erdos457.erdos_457` differs from the gist's `Gist.erdos_457`
in *one* way only:

- **`answer(True) ↔ _` outer wrapping.** Upstream:
  `answer(True) ↔ ∃ ε > 0, { ... }.Infinite`. Gist:
  `∃ ε > 0, { ... }.Infinite`. With our `answer(t) = t` macro shim,
  `answer(True) ↔ _` desugars to `True ↔ _`, which is logically
  equivalent to RHS for any RHS.

The bridge body is therefore a one-liner:

```lean
theorem erdos_457 : answer(True) ↔ ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  exact ⟨fun _ => Gist.erdos_457, fun _ => trivial⟩
```

The `answer` macro is the same shim used in the bridges for Erdős 38 and 397
(`macro_rules | answer($t) => $t`).

## Side-by-side statement comparison

**Upstream (`formal-conjectures/.../457.lean:36–40`, unchanged):**

```lean
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem457.lean"]
theorem erdos_457 : answer(True) ↔ ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  sorry
```

**Bridge (`proofs/erdos457/Erdos457/Bridge.lean:40–44`, restated):**

```lean
theorem erdos_457 : answer(True) ↔ ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite := by
  exact ⟨fun _ => Gist.erdos_457, fun _ => trivial⟩
```

The two theorem signatures match character-for-character (modulo the
upstream `@[category ...]` / `@[AMS ...]` / `formal_proof using` attributes,
which are upstream metadata and not part of the type).

## `#print axioms` output (verbatim)

```
'Erdos457.erdos_457' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard mathlib axioms. **No `Lean.ofReduceBool`** (so no
`native_decide`), **no custom axioms**.

The same applies transitively to the gist theorems re-exposed under
`Erdos457.Gist`:

```
'Erdos457.Gist.thm_main'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos457.Gist.erdos_457'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build evidence

From `/mnt/nvme2/atp_runs/claude_proving_new_mathematics/proofs/erdos457/`:

```
$ lake build
✔ [8027/8029] Built Erdos457.Bridge (6.6s)
✔ [8028/8029] Built Erdos457 (6.2s)
Build completed successfully (8029 jobs).
```

(Three `tendsto_inverse_atTop_nhds_zero_nat` deprecation warnings come from
the Barreto/Aristotle gist — flagged as soft drift, not errors. Renaming
to `tendsto_inv_atTop_nhds_zero_nat` would remove them; out of scope for
the bridge work.)

## What is new in *this* commit, and what is not

**Not new:**
* The mathematical proof (Pilatte's argument; the binomial-bound +
  simultaneous-approximation construction).
* The Lean formalisation (Aristotle, prompted by Kevin Barreto).
* The mathlib lemmas (`Nat.choose`, `Real.log`, etc.).
* The choice of mathlib version (v4.28.0).

**New here (the actual deliverable of this memo):**
* `proofs/erdos457/Erdos457/Proof.lean` — 346 lines. The Barreto/Aristotle
  gist namespaced as `Erdos457.Gist`, with two v4.24.0 → v4.28.0 drift
  fixes: `Real.log_prod` signature, and `erdos_457` body rewritten to
  avoid v4.28.0 norm_num deep-recursion. Mathematical content unchanged.
* `proofs/erdos457/Erdos457/Bridge.lean` — 45 lines. Reproduces the
  `answer(...)` macro shim (same as Erdős 38 and 397 bridges), restates
  the upstream signature character-for-character, and proves it via
  one-line `Iff.intro` composition with `Gist.erdos_457`.
* The library root `Erdos457.lean` exporting both modules.

## Important caveat — what this bridge is *not*

`Erdos457.erdos_457` proven in `Bridge.lean` is a **copy of the upstream
statement re-stated under our v4.28.0 mathlib pin**. It is *not* the same
Lean term as the upstream-file declaration: the upstream file
(`formal-conjectures/FormalConjectures/ErdosProblems/457.lean`) is unchanged,
on mathlib v4.27.0, with `:= by sorry`.

The catalogue (`catalogue/formal_conjectures_erdos.jsonl`) will *still*
show the upstream `Erdos457.erdos_457` as `has_sorry_free_proof = False`,
and that is correct — this bridge does *not* modify the upstream file.

## Lessons

* **`norm_num` with decimal literals is fragile across mathlib versions.**
  The `use 0.1; norm_num` pattern that worked under v4.24.0 deep-recurses
  under v4.28.0 because the decimal `0.1` becomes a `(@OfNat.ofNat ℝ 1 _) /
  (@OfNat.ofNat ℝ 10 _)` term that norm_num's Real-literal evaluator
  cycles on through `evalLT → evalMul → evalDiv → evalMul → evalInv`.
  Substituting `(1 : ℝ) / 10` and splitting the conjunction with `refine`
  bypasses the bad path. **Worth remembering as a phrase-book entry.**
* **`refine ⟨_, by norm_num, ?_⟩` is safer than `use _; norm_num`** when
  the existential conclusion is a conjunction whose second conjunct is
  a non-arithmetic statement. The `refine` shape forces norm_num to
  see only the first conjunct, eliminating cross-talk.
* **Bisecting deep-recursion crashes is awkward** (no line-level error
  before the abort). Replacing theorem bodies with `sorry` and re-running
  is the practical bisect tool. We isolated the recursion to a single
  `theorem` (the gist's own `erdos_457`) by sorrying the prior `thm_main`,
  saving an hour vs. tactic-level bisection.
* **A 1-line bridge (`exact ⟨fun _ => Gist.erdos_457, fun _ => trivial⟩`)
  is the "cheapest" bridge** when the gist itself already produces the
  upstream conclusion. The `answer(True) ↔ _` outer wrapping is the
  whole gap. Watch for this shape on future targets — it's strictly
  easier than the Finset-bashing of #397 or the predicate-translation
  of #38.

## Next

* **Catalogue stays as-is.** The upstream sorry is unchanged.
* **Pick the next target.** Of the remaining 41 (LEAN)+formalised
  candidates from memo 0006/0009/0011, the prime "low-cost"
  candidates that might be one-line bridges (gist already shipped to
  upstream signature):
  * Other gist-based PROVED entries: #259 (1012 lines), #268
    (1297 lines), #347 (2180 lines).
  * If they ship to the upstream signature directly (no `answer(True) ↔`
    wrapping needed), they're 1-line bridges. If they ship to a
    "raw" form, more bridge work is needed.
  * The plby v4.24.0 `DISPROVED` family (#26, #56, #189, #198, #707,
    #845, #1043, #1067, #1080) are all single-file ≥ 1300 lines —
    bigger but uniform; would amortise the v4.24.0 → v4.28.0 drift
    diagnostic across many files.
* **Long-running:** if the v4.24.0 → v4.28.0 drift fix list keeps
  growing, write an "infra" memo cataloguing the fixes (norm_num /
  Real.log_prod / `tendsto_inv*` rename / `Nat.add_one_mul_choose_eq`
  rename) so subsequent ports can apply them upfront.
