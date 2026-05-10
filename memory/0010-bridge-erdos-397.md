# Erdős 397 — bridge from gist `infinite_solutions` to upstream `erdos_397` signature

**Status:** shipped (local) — bridge compiles, axioms clean.
**Date:** 2026-05-10 — 2026-05-10
**Related:** 0009 (target), 0007–0008 (Erdős 38 — same workflow blueprint),
0006 (Lean-side Erdős catalogue).
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/397.lean`,
declaration `Erdos397.erdos_397` (still `:= by sorry` upstream — *not modified*).

## One-line summary

Reproduced Wu/Aristotle's 105-line list-form gist (Somani's disproof of "finitely
many index-disjoint multi-products of central binomials are equal") in our v4.28.0
subproject, then bridged to the upstream `Finset ℕ × Finset ℕ`-form signature
character-for-character. The bridge (161 lines) is purely Lean
formal-engineering — it neither re-proves nor extends the mathematical content,
which lives entirely in Wu/Aristotle's `central_binom_identity`.

## Taxonomy — which 2×2 cell

**Goal 2 — Solving + Known proof** (lower-right of the 2×2 in `CLAUDE.md`).
The mathematical solution is Somani's elementary identity (verified via
`norm_num` + `field_simp` + `ring` chains over ℚ). The Lean formalisation is
Wu's, generated via Aristotle. **No new mathematics, and no new
formalisation, was produced here.** Our deliverable is the local
reproduction + the bridge to the upstream Finset-form signature.

## Source of the proof

- **Mathematical solution.** Manjul Somani (using ChatGPT), referenced from
  [`erdosproblems.com/397`](https://www.erdosproblems.com/397). The
  identity is: for any `a ≥ 2`, with `c = 8a² + 8a + 1`,
  `binom(2a, a) · binom(4a+4, 2a+2) · binom(2c, c) = binom(2a+2, a+1) · binom(4a, 2a) · binom(2c+2, c+1)`.
  Indices on each side are pairwise disjoint (and pairwise disjoint across
  sides) for `a ≥ 2`, giving an infinite family of solutions.
- **Lean formalisation.** Wu via Aristotle, gist
  `https://gist.github.com/llllvvuu/40d68cfa9de9f43eece07ff4fdc3b0ef`,
  generated against `lean4 v4.24.0` + mathlib commit
  `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. 105 lines, no axioms, no
  sorries. The upstream `formal_proof using lean4 at "..."` annotation
  already points at this gist.
- **How obtained.** `curl` of the gist raw URL.

## Where the local copy lives

```
proofs/erdos397/
├── lean-toolchain                # leanprover/lean4:v4.28.0
├── lakefile.toml                 # depends on mathlib rev v4.28.0
├── Erdos397.lean                 # one-line root: import Proof, Bridge
└── Erdos397/
    ├── Proof.lean                # 105 lines — Wu/Aristotle gist, namespaced under Erdos397.Gist
    └── Bridge.lean               # 161 lines — restated upstream theorem + proof
```

`formal-conjectures/FormalConjectures/ErdosProblems/397.lean` was **not modified**.
The catalogue (`catalogue/formal_conjectures_erdos.jsonl`) was **not modified**.

## What `Bridge.lean` does

The upstream `Erdos397.erdos_397` differs from the gist's `infinite_solutions`
in three ways:

1. **Container type.** Upstream uses `Finset ℕ × Finset ℕ`; gist uses
   `List ℕ × List ℕ`.
2. **Disjointness phrasing.** Upstream: `Disjoint M N` (Finset-`Disjoint`).
   Gist: `(M ++ N).Nodup`.
3. **Polarity.** Upstream is `answer(False) ↔ <set is finite>`; gist is
   `Set.Infinite { ... }`.

Rather than building a literal `List → Finset` image-of-set bridge, the
file takes the simpler direct route: **re-construct Somani's family
explicitly in Finset form** and prove the upstream signature by injection.

```lean
private noncomputable def F (a : ℕ) : Finset ℕ × Finset ℕ :=
  ({a + 2, 2 * (a + 2) + 2, Gist.c (a + 2)},
   {(a + 2) + 1, 2 * (a + 2), Gist.c (a + 2) + 1})

theorem erdos_397 :
    answer(False) ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
       ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  refine ⟨fun h => h.elim, fun hfin => ?_⟩
  apply Set.not_infinite.mpr hfin
  refine Set.infinite_of_injective_forall_mem (f := F) F_injective ?_
  intro a
  exact ⟨F_disjoint a, F_prod_eq a⟩
```

The three load-bearing pieces:

1. **`F_injective`.** Sum of the first finset has the closed form
   `8a² + 43a + 57` (proved via three `Finset.sum_insert`s and a
   `ring`). Strictly monotone in `a`, so equality of finsets implies
   equality of indices. `nlinarith` discharges the strict-monotone gap.

2. **`F_disjoint`.** The six elements
   `{a+2, 2a+6, 8a²+40a+49} ∪ {a+3, 2a+4, 8a²+40a+50}` are pairwise
   distinct for all `a : ℕ`. Discharged by `c_expand` + 9-way
   `rcases ... <;> omega` (omega handles each cross-equation including
   the linear-vs-quadratic ones, since the quadratic side is provably
   ≥ 49 while the linear side is at most `2a+6`).

3. **`F_prod_eq`.** Three-element finset products expand via
   `Finset.prod_insert` / `Finset.prod_singleton` to the same monomial
   shape that `Gist.central_binom_identity (a+2)` proves;
   `linear_combination` closes the residual associativity gap.

## Side-by-side statement comparison

**Upstream (`formal-conjectures/FormalConjectures/ErdosProblems/397.lean:50–55`,
unchanged):**

```lean
@[category research solved, AMS 11,
formal_proof using lean4 at "https://gist.github.com/llllvvuu/40d68cfa9de9f43eece07ff4fdc3b0ef",
formal_proof using formal_conjectures at "https://github.com/XC0R/formal-conjectures/blob/.../397.lean#L147"]
theorem erdos_397 :
    answer(False) ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
      ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  sorry
```

**Bridge (`proofs/erdos397/Erdos397/Bridge.lean:151–155`, restated):**

```lean
theorem erdos_397 :
    answer(False) ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
       ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  …
```

The two theorem bodies match character-for-character (modulo whitespace
inside the set comprehension, and the `@[category ...]` /
`@[AMS ...]` / `formal_proof using` attributes which are upstream
metadata and not part of the signature).

The `answer(...)` macro is reproduced as `macro_rules | answer($t) => $t`
— the same shim used in `Erdos38/Bridge.lean`, sufficient for
`answer(False)` to elaborate as `False`. The `centralBinom`
identifier resolves to `Nat.centralBinom` via `open Nat`, matching
upstream's file-level `open Nat`.

## `#print axioms` output (verbatim)

```
'Erdos397.erdos_397' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard mathlib axioms. **No `Lean.ofReduceBool`** (so no
`native_decide`), **no custom axioms**.

The same axioms apply transitively to the gist theorems re-exposed under
`Erdos397.Gist`:

```
'Erdos397.Gist.central_binom_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos397.Gist.sol_family_is_solution'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos397.Gist.infinite_solutions'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build evidence

From `/mnt/nvme2/atp_runs/claude_proving_new_mathematics/proofs/erdos397/`:

```
$ lake build
✔ [8027/8029] Built Erdos397.Bridge (8.2s)
✔ [8028/8029] Built Erdos397 (6.9s)
Build completed successfully (8029 jobs).
```

(Five `Nat.succ_mul_choose_eq` deprecation warnings come from the Wu/Aristotle
gist — flagged as soft drift, not errors. Renaming to `Nat.add_one_mul_choose_eq`
would remove them; out of scope for the bridge work.)

## What is new in *this* commit, and what is not

**Not new:**
* The mathematical proof (Somani via ChatGPT; the parametric family
  `(a, 2a+2, c)` vs `(a+1, 2a, c+1)` and its `central_binom_identity`).
* The Lean formalisation of that proof (Wu via Aristotle).
* The mathlib lemmas (`Nat.centralBinom`, `Nat.choose_succ_succ`,
  `Nat.add_one_mul_choose_eq`, etc.).
* The choice of mathlib version (v4.28.0).

**New here (the actual deliverable of this memo):**
* `proofs/erdos397/Erdos397/Proof.lean` — 105 lines. Verbatim port of
  the Wu/Aristotle gist under v4.28.0, namespaced as `Erdos397.Gist` so
  it doesn't collide with the bridge's symbols (`c`, `is_solution`,
  `sol_family`, etc.). Mathematical content unchanged.
* `proofs/erdos397/Erdos397/Bridge.lean` — 161 lines. Reproduces the
  `answer(...)` macro (same shim as Erdős 38), restates the upstream
  signature character-for-character, and proves it via Somani's family
  in Finset form. Three load-bearing helpers: `F_injective` (via finset
  sum), `F_disjoint` (via `c_expand` + omega), `F_prod_eq` (via
  `Finset.prod_insert` + `linear_combination`).
* The library root `Erdos397.lean` exporting both modules.

## Important caveat — what this bridge is *not*

`Erdos397.erdos_397` proven in `Bridge.lean` is a **copy of the upstream
statement re-stated under our v4.28.0 mathlib pin**. It is *not* the
same Lean term as the upstream-file declaration: the upstream file
(`formal-conjectures/FormalConjectures/ErdosProblems/397.lean`) is
unchanged, on mathlib v4.27.0, with `:= by sorry`.

The catalogue (`catalogue/formal_conjectures_erdos.jsonl`) will *still*
show the upstream `Erdos397.erdos_397` as `has_sorry_free_proof = False`,
and that is correct — this bridge does *not* modify the upstream file.

What the bridge proves is an *equivalent* statement under v4.28.0,
where "equivalent" means: the theorem signature matches the upstream
character-for-character (`answer(False)`, `Finset ℕ × Finset ℕ`,
`Disjoint M N`, `∏ i ∈ M, centralBinom i`, `Set.Finite`), modulo the
v4.27.0/v4.28.0 mathlib drift.

A future port — when `formal-conjectures` upgrades to v4.28.0, or when
someone backports the v4.28.0 proof to v4.27.0 — could land the entire
package upstream as the actual `formal_proof using lean4 at "..."`
target, and at that point the upstream sorry would discharge against
this bridge.

## Lessons

* **Skip the list↔finset image bridge if the family is constructible
  directly in finset form.** I started planning a `lf : List × List →
  Finset × Finset` injectivity argument; the cleaner path was to
  rebuild Somani's family with finset literals and reuse only the gist's
  `central_binom_identity`. This cut the bridge to 161 lines.
* **`Finset.sum`/`Finset.prod` on an explicit triple `{x, y, z}` cleanly
  unfolds to three `_insert` rewrites + `_singleton`, provided the three
  membership-not-in-tail lemmas are available**. Extracting them as
  separate `private lemma`s (`not_mem_pair_fst`, etc.) keeps both the
  sum proof and the product proof readable.
* **`omega` in v4.28.0 handles linear-vs-quadratic disequalities when the
  quadratic side is bounded below by an obvious constant.** I expected
  to need `nlinarith` for the `F_disjoint` cross-cases; `omega` alone
  closed all nine, by treating `8 * a^2 + 40 * a + 49` as opaquely ≥ 49
  (since each branch's linear side is at most `2a+6`).
* **`linear_combination` is the right tool for an associativity-only
  reshuffle of an existing equation.** `linarith [hid]` failed on the
  `F_prod_eq` final step (it can't re-bracket `a*b*c = a*(b*c)`);
  `linear_combination hid` closed it cleanly.
* **`Set.infinite_of_injective_forall_mem` is the cleanest tool when the
  set is presented as `{ x | P x }` and you have an explicit injection
  `f : ℕ → α` with `∀ n, f n ∈ S`.** Same lemma the gist itself uses;
  reaching for it twice (once in the gist, once in the bridge) keeps
  the layers parallel.

## Next

* **Catalogue stays as-is.** The upstream sorry is unchanged.
* **Pick the next target.** Of the 44 (LEAN)+formalised candidates from
  memo 0006/0009, the next batch worth scoping:
  * Other `plby/lean-proofs` `DISPROVED` entries (small, single-file,
    similar v4.24.0 → v4.28.0 drift): #56, #189, #198, #204, #707,
    #845, #1043, #1067, #1080, #1141 — most should be 1–2 hour
    bridges each, modulo `Mathlib` import compatibility.
  * `PROVED (LEAN)` entries from non-`live.lean-lang.org` sources:
    #229, #275, #370, #418, #427, #541, #645, #728 — these are larger
    proofs, candidates for "long-form companion-repo" bridges in the
    style of #38.
* **Long-running improvement.** When the Wu/Aristotle proof is
  refreshed against v4.28.0 (or when the current `Nat.succ_mul_choose_eq`
  deprecations cause warnings to become errors), the gist port in
  `Proof.lean` will need updating — but the bridge surface is stable.
