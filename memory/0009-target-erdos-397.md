# Erdős 397 — target evaluation (next bridge candidate after Erdős 38)

**Kind:** target
**Status:** go
**Date:** 2026-05-10
**Related:** 0006 (Lean-side Erdős catalogue), 0007–0008 (Erdős 38
reproduction + bridge — same workflow), `CLAUDE.md` "External resources".
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/397.lean`,
declaration `Erdos397.erdos_397` (still `:= by sorry`; carries
`@[formal_proof using lean4 at "https://gist.github.com/llllvvuu/40d68cfa9de9f43eece07ff4fdc3b0ef"]`).

## One-line summary

Pick `Erdos397.erdos_397` as the next reproduce-and-bridge target: a
disproof of "finitely many index-disjoint multi-products of central
binomials are equal" via Somani's parametric family
`(a, 2a+2, c)` vs. `(a+1, 2a, c+1)` with `c = 8a²+8a+1`. Wu/Aristotle
already shipped the gist proof (101 lines, no axioms, no sorries) in
mathlib commit `f897ebcf` (≈ v4.24.0); the bridge to the upstream
`Finset ℕ × Finset ℕ` form is the only formal-engineering left.

## Taxonomy — which 2×2 cell

**Goal 2 — Solving + Known informal proof, formalised by someone
else** (lower-right of the `CLAUDE.md` 2×2). The mathematics is
Somani's elementary identity (verified in classical-paper style); the
formalisation is by Wu via Aristotle. **This memo's verdict — and
any subsequent proof memo — must not describe this work as new
mathematics.** Our deliverable is purely Lean formal-engineering:
local reproduction + bridge to upstream signature.

## Why this candidate

I joined `catalogue/formal_conjectures_erdos.jsonl` against
`catalogue/erdosproblems.jsonl` filtering on:

- `has_sorry_free_proof == False` (upstream still `:= by sorry`),
- `formal_proof_kind == "lean4"` (upstream points at a Lean proof),
- erdosproblems.com `status_label` contains `(LEAN)` (page knows of
  a Lean proof).

44 candidates. The two `live.lean-lang.org/#project=mathlib-v4.28.0`-
pinned ones (#258, #997) both rely on a custom `axiom` for the deep
analytic input (Tao–Teräväinen, Maynard–Tao–BFT respectively) — that
violates `CLAUDE.md`'s "no custom axioms" rule, so they're disqualified.
Of the remainder, `#397` is the most tractable next pick:

- Its gist proof (`llllvvuu/40d68cfa9de9f43eece07ff4fdc3b0ef`) is
  **101 lines** total, **no axioms**, **no sorries**.
- The mathematical content is a single computational identity over ℚ
  plus an injectivity argument — undergraduate combinatorics.
- The disproof is *constructive* (an explicit family of solutions), so
  the bridge is mostly form-bashing rather than re-proving anything.
- The proof was authored against `Lean v4.24.0` + mathlib commit
  `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Lemmas used
  (`Nat.centralBinom`, `Nat.choose_succ_succ`, `Nat.succ_mul_choose_eq`,
  `Nat.cast_choose`, `Nat.factorial`, `Set.Infinite`,
  `Set.infinite_of_injective_forall_mem`) are all stable; expected
  drift to v4.28.0 is small.

DISPROVED candidates from `plby/lean-proofs/src/v4.24.0/` (e.g. #26,
#56, #189, #198) carry the same v4.24.0 → v4.28.0 drift but a different
import set; pick those for the run after this one if #397 lands cleanly.

## Side-by-side: gist statement vs upstream signature

**Upstream (`formal-conjectures/FormalConjectures/ErdosProblems/397.lean`):**

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

**Gist (`llllvvuu/40d68cfa9...`):**

```lean
def is_solution (M N : List ℕ) : Prop :=
  (M ++ N).Nodup ∧
  (M.map Nat.centralBinom).prod = (N.map Nat.centralBinom).prod

def sol_family (a : ℕ) : List ℕ × List ℕ := ([a, 2*a+2, c a], [a+1, 2*a, c a+1])

theorem infinite_solutions :
    Set.Infinite { s : List ℕ × List ℕ | is_solution s.1 s.2 }
```

The two statements differ in three ways. **All three must be bridged.**

1. **Container type.** Upstream uses `Finset ℕ × Finset ℕ`; gist uses
   `List ℕ × List ℕ`. The `sol_family a` lists are `Nodup` (the
   `is_solution` predicate enforces it), so `List.toFinset` preserves
   them and the products carry over via `List.toFinset_prod`-style
   identities.
2. **Disjointness phrasing.** Upstream: `Disjoint M N` (Finset).
   Gist: `(M ++ N).Nodup`. For `Nodup` lists `M`, `N`, the conjunction
   `M.Nodup ∧ N.Nodup ∧ M.toFinset.Disjoint N.toFinset` matches
   `(M ++ N).Nodup` exactly — discharge via `List.Nodup.append`,
   `List.disjoint_iff_ne_disjoint` etc.
3. **Polarity.** Upstream is `answer(False) ↔ <set is finite>`, i.e.
   the Erdős question's answer is False meaning the set is *not*
   finite. The gist's `infinite_solutions` is exactly `¬ Finite`, so
   the bridge is `answer(False) ↔ (¬ Finite)` ↔ `Infinite`. Direct.

## Mathlib lemmas the bridge will lean on

Expected (none of these are exotic, all are in v4.28.0 mathlib):

- `Nat.centralBinom`, `Nat.centralBinom_eq_choose_two_mul` (or whatever
  the v4.28.0 name is — `Nat.centralBinom` is `(2*n).choose n`).
- `Set.Infinite.mono`, `Set.infinite_of_injective_forall_mem`.
- `List.toFinset`, `List.Nodup.toFinset_inj`,
  `List.Nodup.prod_toFinset_eq` (or
  `Finset.prod_list_map_count` /
  `List.prod_toFinset` — exact name to be looked up).
- `List.Nodup.append`, `List.disjoint_iff_ne_disjoint`,
  `Finset.disjoint_iff_inter_eq_empty`.
- `answer(False)` reduces to `False` via the same macro shim as in
  `Bridge.lean` for Erdős 38 (`macro_rules | answer($t) => $t`).

## Bridge plan (sketch)

```lean
namespace Erdos397

theorem erdos_397 : answer(False) ↔
    {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
     ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite := by
  -- answer(False) ≡ False; so suffices to show the Finset-set is *not* finite.
  refine ⟨fun h => absurd h not_false, fun h => ?_⟩
  apply (h.mono ?_).elim_left infinite_solutions_finset
  …
end Erdos397
```

with `infinite_solutions_finset` re-stating the gist's
`infinite_solutions` over `Finset` containers via the
`List → Finset` converter.

Estimated bridge body: 30–80 lines, well under 50× the gist's own
length. Two helper lemmas at most.

## Risks / fallbacks

| Risk | Probability | Fallback |
| ---- | ----------- | -------- |
| `Nat.cast_choose` signature changed in v4.28.0 | medium | use `Nat.choose_succ_succ`/`Nat.succ_mul_choose_eq` directly; or `field_simp` + `ring_nf` |
| `field_simp [c]` rewrites differently in v4.28.0 | low | unfold `c` manually, `ring` on the cleared identity |
| `set_option maxRecDepth 4000` etc. cause performance grief | low | drop the options or split the `central_binom_identity` lemma |
| `List.toFinset` ↔ `Finset` product bridge is fiddly | medium | switch the gist's `is_solution` to take `Finset` from the start (rewrite locally; not part of the gist) |
| Injection `a ↦ (sol_family a).toFinset` collides | medium | use the *first list element* `a` itself as the discriminator; `Set.infinite_of_injective_forall_mem` with `f a := …` whose first-Finset's `min'` recovers `a` |
| `IsSolution` style mismatches the upstream `Disjoint` form | medium | prove directly: `M.toFinset.Disjoint N.toFinset` from `(M++N).Nodup` |

If the predicate bridge turns out to require >100 lines because the
list-form vs Finset-form gap is genuinely fiddly, **stop, write a
`fail-...` memo, and report**.

## Verdict

**Go.** Self-contained gist, no axioms, mathlib drift small,
straightforward bridge. Same workflow as `0007 + 0008`; expected
total work ≪ Erdős 38.

## Next

`memory/0010-bridge-erdos-397.md` — proof memo recording the final
bridge file, the verbatim `#print axioms` output, and an honest note
on what was already in the literature (everything mathematical) vs.
what is new in this PR (the local reproduction + bridge under
v4.28.0 + the catalogue/memo paperwork).
