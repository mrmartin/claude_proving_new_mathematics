# Bridge pipeline — tracking

**Kind:** infra
**Status:** in-progress
**Date:** 2026-05-10 (start)
**Related:** 0006 (Lean-side Erdős catalogue), 0007–0008 (#38), 0009–0010 (#397), 0011–0012 (#457).

## Goal

Process **all** "(LEAN) + formalised + axiom-clean" Erdős candidates from
memo 0006 with the reproduce-and-bridge workflow established in
memos 0007–0008, 0009–0010, 0011–0012. After each: bridge file in our
v4.28.0 subproject, `#print axioms` clean, memos + commits pushed.

## Methodology (cross-reference, not re-derived)

For each target:
1. Create `proofs/erdosN/` Lake subproject, mathlib v4.28.0 pin
   (same shape as `proofs/erdos38/`, `proofs/erdos397/`, `proofs/erdos457/`).
2. Drop the external proof source into `ErdosN/Proof.lean`,
   namespaced under `ErdosN.Gist`. Apply v4.24.0 → v4.28.0 drift fixes
   as needed.
3. Write `ErdosN/Bridge.lean`: reproduce the `answer(...)` macro shim
   (identity), restate the upstream signature character-for-character,
   and prove it by composing the gist's conclusion through any required
   predicate/cardinality/edge-case bridges.
4. Verify `lake build` clean + `#print axioms ErdosN.erdos_N` shows
   only `[propext, Classical.choice, Quot.sound]`.
5. Memos + README index update + commit/push per `CLAUDE.md` rules.

Subsequent memos in this stream are *intentionally terser* than memos
0007–0012 — those establish the methodology and the rationale; the
follow-on memos cite back and only document what is *different* per
target.

## Candidates (41 starting set, 3 already done)

Pulled from memo 0006 cross-filter (`has_sorry_free_proof == False`
∧ `formal_proof_kind == "lean4"` ∧ erdosproblems.com page tagged
`(LEAN)`). Triage (Bash `grep ^axiom` and `wc -l`) gives the table
below. Disqualified rows are kept for the record so future work
knows they were considered.

| # | Lines | Source | Predicate-match? | State |
| ---:|---:| --- | --- | --- |
| 38   | 1852 (Aristotle / Del-Vecchio) | gist `madeve-unipi` | partial — bridge built explicit construction | **shipped 0007–0008** |
| 26   | 499 | plby v4.24.0 | local `IsThick`/`IsBehrend`; upstream uses similar but separate defs | pending |
| 56   | 1350 | plby v4.24.0 | local `WeaklyDivisible`/`MaxWeaklyDivisible`; upstream uses upstream `WeaklyDivisible` | pending |
| 189  | 607 | plby v4.24.0 | Euclidean rectangles in `ℝ²` | pending |
| 194  | 617 | gist `ster-oc` | local defs | pending |
| 198  | 161 | plby v4.24.0 | local `IsSidon`/`IsAPOfLength` ↔ upstream FCM defs (equivalent on ℕ) | **shipped 0014** |
| 204  | 947 | Woett `Lean-files` | covering systems on ℤ | pending |
| 229  | 1603 | plby v4.24.0 | – | pending |
| 258  | 353 (gist `ster-oc` v4.28.0) | – | **disqualified** — uses `axiom tao_teravainen` |
| 259  | 1012 | gist `ster-oc` | – | pending |
| 268  | 1297 | gist `madeve-unipi` | – | pending |
| 275  | 578 | plby v4.24.0 | – | pending |
| 303  | 1702 (forum thread) | forum-only; not a direct file | – | pending (URL needs scrape) |
| 331  | 0 (Woett URL 404) | – | – | pending (URL needs fixup) |
| 347  | 2180 | ebarschkis | – | pending |
| 355  | 3834 | Woett | – | pending |
| 370  | 190 | plby v4.24.0 | – | **shipped 0016** |
| 392  | 3180 | AlexKontorovich `PrimeNumberTheoremAnd` | multi-file project; may need subset extraction | pending |
| 397  | 101 (gist `llllvvuu`) | – | – | **shipped 0009–0010** |
| 418  | 560 | plby v4.24.0 | – | pending |
| 427  | 91 (gist `JohnEdwardJennings`) | – | **disqualified** — uses `axiom shiu_consecutive_primes` |
| 434.i / 434.ii | – (forum thread) | forum-only | – | pending (URL needs scrape) |
| 457  | 342 | Woett (Barreto/Aristotle) | – | **shipped 0011–0012** |
| 541  | 3072 | plby v4.24.0 | – | pending |
| 645  | 172 | plby v4.24.0 | – | **shipped 0015** |
| 707  | 6359 | plby v4.24.0 | – | pending |
| 728  | 6300 | plby v4.24.0 | – | pending |
| 845  | 3024 | plby v4.24.0 | – | pending |
| 897.i / 897.ii | 947 | plby v4.24.0 | multi-part | pending |
| 997  | 220 (gist `pitmonticone` v4.28.0) | – | **disqualified** — uses `axiom maynardTaoBFT` |
| 1043 | 225 | plby v4.24.0 | – | pending |
| 1051 | 1702 (forum thread) | forum-only | – | pending (URL needs scrape) |
| 1067 | 2510 | plby v4.24.0 | – | pending |
| 1071.i | 3079 | plby v4.24.0 | – | pending |
| 1071.ii | 5385 | plby v4.24.0 | – | pending |
| 1080 | 1389 | plby v4.24.0 | – | pending |
| 1102 (×4 parts) | 898 / 2806 | Woett multi-file | – | pending |
| 1141 | 1629 | yuta0x89 | **disqualified** — uses `axiom theorem_1_3, axiom mertens_third_theorem` |
| 1196 | – (math-inc multi-file `PrimitiveSetsAboveX/Main` etc.) | – | – | pending (heavy port) |

**Already shipped:** 3 (#38, #397, #457).
**Disqualified by custom axioms:** 4 (#258, #427, #997, #1141).
**Pending direct port:** ~30+ subprobs (some multi-part).
**Special handling:** #303, #331, #392, #434, #1051, #1102, #1196 (forum scrape / 404 URL / multi-file projects).

## Order of attack

Sorted by ascending estimated effort = `lines + 0.5 × (1 if predicate-mismatch else 0)`:

1. **198** (161 lines, predicate mismatch — small fix needed) — in progress.
2. **645** (172 lines, plby).
3. **370** (190 lines, plby).
4. **1043** (225 lines, plby).
5. **26** (499 lines, plby; local `IsThick`/`IsBehrend`).
6. **418** (560 lines, plby).
7. **275** (578 lines, plby).
8. **189** (607 lines, plby).
9. **194** (617 lines, gist).
10. **204** (947, Woett).
11. **897.i / 897.ii** (947, plby — multi-part).
12. **1102 — 4 parts** (898 + 2806).
13. **259** (1012, gist).
14. **268** (1297, gist).
15. **56** (1350, plby; local defs).
16. **1080** (1389, plby).
17. **229** (1603, plby).
18. **347** (2180, ebarschkis).
19. **1067** (2510, plby).
20. **541** (3072, plby).
21. **1071.i** (3079, plby).
22. **392** (3180, multi-file project).
23. **845** (3024, plby).
24. **355** (3834, Woett).
25. **1071.ii** (5385, plby).
26. **728** (6300, plby).
27. **707** (6359, plby).

(Special handling: 303, 331, 434, 1051, 1196 — last, after the direct ports.)

## Common drift fixes (v4.24.0 → v4.28.0)

From memos 0010 and 0012 — likely to recur:

- `Nat.succ_mul_choose_eq` → `Nat.add_one_mul_choose_eq` (warning,
  not error).
- `tendsto_inverse_atTop_nhds_zero_nat` → `tendsto_inv_atTop_nhds_zero_nat`
  (warning).
- `Real.log_prod _ _ <hyp>` → `Real.log_prod <hyp>` (positional args
  collapsed to one).
- Decimal literal in `use 0.X; norm_num` triggers `NormNum.derive` deep
  recursion under v4.28.0 — replace with `(N : ℝ) / M; refine ⟨..., by
  norm_num, ?_⟩` plus split-conjunction.

These will be applied per file as encountered. If a fix turns out to
be applicable to many files, it gets a dedicated phrasebook bullet
in this memo's `Lessons` section (TBD).

## Progress log

| Date | Memo range | Done so far |
| --- | --- | --- |
| 2026-05-10 | 0007–0012 | #38, #397, #457 (3 / ~30) |
| 2026-05-10 | 0014 | + #198 (4 / ~30) |
| 2026-05-10 | 0015 | + #645 (5 / ~30) |
| 2026-05-10 | 0016 | + #370 (6 / ~30) |

(Updated as bridges ship.)

## Lessons (accumulated)

* **`(answer(True/False) ↔ X)` is the cheapest bridge shape** when the
  gist already produces the upstream conclusion shape. 1-line
  `exact ⟨fun _ => Gist.erdos_N, fun _ => trivial⟩` (for
  `answer(True)`) or `exact ⟨fun h => h.elim, fun h => ...⟩` (for
  `answer(False)`).
* **Predicate-mismatch bridges** (Erdős 38, likely 198, 56, 26)
  cost the most: reproduce upstream FCM definitions verbatim,
  state the equivalence, prove the direction(s) actually needed
  for the final theorem.
* **v4.24.0 → v4.28.0 drift fixes are uniform across files** — apply
  them upfront when porting any plby/Aristotle file from that era.
* **plby's predicates are typically local re-implementations** of FCM
  definitions; expect mismatch on every plby file with non-`Nat`
  arithmetic content.

## Next

Tackle #198 (in progress). Update this memo's progress log + per-row
state after each bridge ships.
