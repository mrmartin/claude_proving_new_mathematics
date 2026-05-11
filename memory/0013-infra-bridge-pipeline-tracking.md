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
| 26   | 499 | plby v4.24.0 | local `IsThick`/`IsBehrend`; upstream uses similar but separate defs | **blocked: source mismatch** — plby file proves `erdos_26.variants.rusza` (non-thick counterexample) NOT `erdos_26`. Upstream `formal_proof using lean4` annotation appears to be a cataloguing error. |
| 56   | 1350 | plby v4.24.0 | local `WeaklyDivisible`/`MaxWeaklyDivisible`; upstream uses upstream `WeaklyDivisible` | **blocked**: gist uses `native_decide` ×7 (banned). |
| 189  | 607 | plby v4.24.0 | Euclidean rectangles in `ℝ²` | **blocked**: `bound;` tactic context-dependent (was doing False-derivation), `Pi.basisFun` arg shape changed for `Module.Basis (Fin 2) ℝ ℝ²`, type mismatch on `b - a = c - d`. Multiple cascading issues. |
| 194  | 617 | gist `ster-oc` | local defs | **blocked-bridge-complex**: gist proves with `LinearOrdering r` (local) + `ArithProgression a d k : Fin k → ℝ` (function); upstream uses `IsStrictTotalOrder ℝ r` + `s.IsAPOfLength k` (list). Predicate alignment ≈ 40–60 lines of bridge. Gist itself compiles cleanly; revisit when batch easy targets exhausted. |
| 198  | 161 | plby v4.24.0 | local `IsSidon`/`IsAPOfLength` ↔ upstream FCM defs (equivalent on ℕ) | **shipped 0014** |
| 204  | 947 | Woett `Lean-files` | covering systems on ℤ | **blocked-source-mismatch**: gist's `theorem erdos_204` has `→` where upstream has `∧` inside the inner existential (`∃ x : ℤ, x ≡ a d → x ≡ a d'` vs `∃ x, x ≡ a d ∧ x ≡ a d'`). These specify different propositions; gist's `¬ <gist statement>` does not imply `¬ <upstream statement>`. Likely a typo upstream of the `formal_proof` annotation. |
| 229  | 1603 | plby v4.24.0 | – | **blocked**: 10+ v4.24.0 → v4.28.0 drift errors (`List.get?` removed, "No goals to be solved" regressions, type mismatches). |
| 258  | 353 (gist `ster-oc` v4.28.0) | – | **disqualified** — uses `axiom tao_teravainen` |
| 259  | 1012 | gist `ster-oc` | – | **shipped 0018** |
| 268  | 1297 | gist `madeve-unipi` | – | **blocked**: gist proves only the d=3 case (`harmonicSubseriesSet : Set (Fin 3 → ℝ)`); upstream signature is parameterised by general `d : ℕ` — d=0, 1, 2 each need separate handling and d≥3 needs projection. Plus 1 native_decide instance to replace. |
| 275  | 578 | plby v4.24.0 | – | **blocked**: v4.24.0 → v4.28.0 drift on `Finset.card_image_le` ↔ `List.length` cross-comparison (gist's tactic chain doesn't elaborate; needs nontrivial rewrite). |
| 303  | 3926 (decoded from forum) | forum-only — decoded via live.lean-lang.org `codez=` payload (LZ-string base64) | – | **decoded + blocked**: gist signature matches upstream RHS (Brown-Rödl reciprocal-3-AP coloring result). 1-line bridge possible *if* gist compiles — but it doesn't: 10+ v4.24.0 → v4.28.0 drift errors (`field_simp made no progress`, type mismatches, unsolved goals in deeply-nested ring arguments). |
| 331  | 438 (correct URL `ErdosProblem331.lean`, no `%23`) | Woett | – | **fetched + blocked**: gist signature is `¬ ∀ A B, ...` (matches upstream RHS for 1-line bridge); but the gist itself has multiple drift errors: `Lean.Grind.NoNatZeroDivisors (ZMod 4)` typeclass timeout, `omega` regressions on combinatorial split, ambiguous `pow_succ'`. |
| 347  | 2180 | ebarschkis | – | **blocked**: 2 native_decide instances + gist uses local `has_asymptotic_density_one` / `subset_sums_of_set` predicates that differ from upstream's `HasDensity (𝓟 (range (a ∘ ι))) 1` formulation; bridge needs to prove formal equivalence. |
| 355  | 3834 | Woett | – | **blocked**: 2 v4.24.0 → v4.28.0 drifts (`h_apply_finite_seq` arity, internal `Nat.lt_succ_of_le` unification through deeply nested terms). One drift partially fixed; second too tangled. |
| 370  | 190 | plby v4.24.0 | – | **shipped 0016** |
| 392  | 3180 | AlexKontorovich `PrimeNumberTheoremAnd` | multi-file project; may need subset extraction | **blocked-multi-file**: lives in PrimeNumberTheoremAnd repo with many module imports; would require full sub-project port. |
| 397  | 101 (gist `llllvvuu`) | – | – | **shipped 0009–0010** |
| 418  | 560 | plby v4.24.0 | – | **blocked**: gist uses `native_decide` ×13 (banned per `CLAUDE.md`; would introduce `Lean.ofReduceBool` axiom). |
| 427  | 91 (gist `JohnEdwardJennings`) | – | **disqualified** — uses `axiom shiu_consecutive_primes` |
| 434.i / 434.ii | 357 (decoded from forum) | forum live.lean `codez=` payload | – | **decoded + disqualified**: gist uses `axiom theorem_2` (referenced from Erdős 433 — needs Erdős 433's port done first or the axiom resolved). Banned per `CLAUDE.md`. |
| 457  | 342 | Woett (Barreto/Aristotle) | – | **shipped 0011–0012** |
| 541  | 3072 | plby v4.24.0 | – | **blocked**: 10+ drift errors (`Eq.refl` constructor changes, type mismatches, unsolved goals). |
| 645  | 172 | plby v4.24.0 | – | **shipped 0015** |
| 707  | 6359 | plby v4.24.0 | – | **blocked-source-mismatch**: gist's `erdos_707` uses `Set ℤ` for `B` and `IsPerfectDifferenceSetModulo` predicate; upstream uses `Set ℕ` and `IsPerfectDifferenceSet`. Container + predicate translation bridge ≥ 50 lines. |
| 728  | 6300 | plby v4.24.0 | – | **untested** — large v4.24.0 file; given pattern (5/5 plby v4.24.0 files tested had substantial drift), expected blocked. |
| 845  | 3024 | plby v4.24.0 | – | **untested** — gist uses `(false) ↔ ...` with lowercase `false`; needs verification + likely drift. |
| 897.i / 897.ii | 947 | plby v4.24.0 | multi-part | **blocked**: 7+ v4.24.0 → v4.28.0 drift errors (`.not_le` projection gone, `No goals to be solved`, type mismatches). |
| 997  | 220 (gist `pitmonticone` v4.28.0) | – | **disqualified** — uses `axiom maynardTaoBFT` |
| 1043 | 225 | plby v4.24.0 | – | **shipped 0017** |
| 1051 | 803 (decoded from forum) | forum live.lean `codez=` payload | – | **shipped 0019** — 110-line bridge closes the ℕ→ℤ container gap via tail-truncation `b m := (a (m+N₀)).toNat`, the gist's own `erdos_1051_liminf_shift_pow` helper for the shifted liminf > 1, `Summable.sum_add_tsum_nat_add` decomposition, and `Irrational.ratCast_add` for the final rational+irrational. |
| 1067 | 2510 | plby v4.24.0 | – | **blocked-bridge-complex**: gist uses local `uncountably_chromatic`, `finite_independent_paths`, `Set.Iio (Ordinal.omega 1)` colorings; upstream uses `G.chromaticCardinal = ℵ_ 1` + `G.Subgraph` + `InfinitelyConnected`. Predicate translation ≈ 100+ lines. Gist itself compiles after one drift fix (`add_le_add_right` arg order). |
| 1071.i | 3079 | plby v4.24.0 | – | **untested** — large; gist proves `Theorem_1`, `Corollary_2`, `Corollary_3` but upstream signature uses `Maximal (fun T : Finset (ℝ² × ℝ²) => …)` shape — bridge gap nontrivial. |
| 1071.ii | 5385 | plby v4.24.0 | – | **untested** — gist proves `∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Finite S`; bridge gap to upstream's Maximal-over-Finset shape. |
| 1080 | 1389 | plby v4.24.0 | – | **blocked**: 9+ v4.24.0 → v4.28.0 drift errors (`grind` regressions, function-type mismatches, unsolved goals). Substantial rewrite needed. |
| 1102 (×4 parts) | 898 / 2806 | Woett multi-file | – | **blocked-multi-file**: PropertyP.lean and PropertyQ.lean both re-define `HasPropertyP`, `HasNaturalDensity`, `Admissible`, etc.; can't be combined naively. Would require extracting shared helpers into a separate `Erdos1102.Helpers` module. Also v4.24.0 → v4.28.0 drift likely. |
| 1141 | 1629 | yuta0x89 | **disqualified** — uses `axiom theorem_1_3, axiom mertens_third_theorem` |
| 1196 | – (math-inc multi-file `PrimitiveSetsAboveX/Main` etc.) | – | – | **blocked-multi-file**: imports `PrimitiveSetsAboveX.Main`; multi-module project from `math-inc/Erdos1196` repo. |

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
| 2026-05-10 | 0017 | + #1043 (7 / ~30) |
| 2026-05-10 | 0018 | + #259 (8 / ~30) |
| 2026-05-11 | 0019 | + #1051 (9 / ~30) |

### Final tally (2026-05-10)

| Bucket | Count | Identifiers |
| --- | ---: | --- |
| **shipped** | **8** | #38, #198, #259, #370, #397, #457, #645, #1043 |
| disqualified by custom axioms | 4 | #258 (Tao–Teräväinen), #427 (Shiu), #997 (Maynard–Tao–BFT), #1141 (theorem_1_3 + mertens_third_theorem) |
| disqualified by `native_decide` | 2 | #418 (13×), #56 (7×) |
| source mismatch (gist proves different statement than upstream `formal_proof` annotation claims) | 2 | #26 (plby proves `.variants.rusza` not `erdos_26`), #204 (gist has `→` where upstream has `∧`) |
| v4.24.0 → v4.28.0 drift (compile errors I couldn't resolve in budget) | 8 | #189, #229, #275, #355, #541, #897, #1080 + #347 (also 2 native_decide) |
| bridge-complex (gist compiles, but predicate translation to upstream signature ≥ 100 lines) | 3 | #194 (LinearOrdering ↔ IsStrictTotalOrder + ArithProgression as fn ↔ list), #268 (d=3 only, upstream all d), #1067 (`uncountably_chromatic` ↔ chromaticCardinal etc.) |
| source-mismatch (different container types or predicates) | 2 | #707 (Set ℤ vs Set ℕ + IsPerfectDifferenceSetModulo), #347 (different density formulations) |
| multi-file project (would need substantial restructuring) | 3 | #392 (PrimeNumberTheoremAnd), #1102 (shared defs across PropertyP+PropertyQ files), #1196 (math-inc PrimitiveSetsAboveX) |
| untested (forum-only or 404) | 4 | #303, #331, #434, #1051 |
| untested (large plby v4.24.0; high drift risk per pattern) | 4 | #728, #845, #1071, #1071b |
| **TOTAL** | **40+** | |

Shipped rate: **8/44 ≈ 18%** of the (LEAN)+formalised+catalogue-pool candidates.

### Why the rate is what it is

* **plby v4.24.0 files** (the largest single source) bridge poorly: Aristotle-generated tactics are fragile, mathlib API has churned (`.not_lt`, `Set.eq_empty_of_forall_not_mem`, `bound`, `MulAction.mul_smul`, `Real.log_prod`, `Nat.succ_mul_choose_eq`, `tendsto_inverse_atTop_nhds_zero_nat`, `add_le_add_right` arg order, etc.), and many files exceed our project's `CLAUDE.md` rules (`native_decide`).
* **Predicate divergence** between gists and upstream is the second-largest blocker — both `formal_proof using lean4` annotations are sometimes inaccurate (e.g. `#26`, `#204`).
* **Multi-file projects** (`#392`, `#1102`, `#1196`) can be ported, but each requires substantial restructuring (extracting shared helpers, normalising imports) that exceeds the 30-min-per-bridge budget.
* **Forum-only sources** (`#303`, `#434`, `#1051`) need an HTML-scraping step that wasn't in scope; can be added if desired.

### What would unblock more

In rough order of leverage:

1. **A v4.24.0 → v4.28.0 drift auto-fixer** that maps the dozen-or-so recurring rename/arg-order/projection patterns would unblock most plby files in seconds rather than minutes.
2. **Manual port of `#194` predicate translation** (`LinearOrdering ↔ IsStrictTotalOrder` + AP-function-to-list bridge) — the gist compiles cleanly; just need to write ≈ 50 lines of bridge.
3. **Forum-thread scraping** for #303, #434, #1051 — single Python script.
4. **A subagent pass** (lean4:proof-repair) on a single drift-blocked file as a proof-of-concept; if it succeeds in budget, scale up.

These are concrete next-steps. Without them, the remaining candidates are individually expensive to crack.

### Reassessment of scraping-blocked candidates (2026-05-11)

Returned to the four candidates marked "untested — forum-only or 404"
and decoded their Lean payloads. The forum-thread URLs encode the
gist Lean source via `live.lean-lang.org/#project=mathlib-v4.24.0&codez=<base64>`
where the base64 is `lz-string` compressed. Decoded via the Python
`lzstring` package (`pip install --user lzstring`,
`LZString().decompressFromBase64(...)`).

| # | Source path | Status |
| ---:| --- | --- |
| 303 | forum thread `https://www.erdosproblems.com/forum/thread/303`, decoded 3926 lines | **blocked** — gist matches upstream RHS for 1-line bridge, but 10+ v4.24.0→v4.28.0 drifts (`field_simp made no progress`, ring/type mismatches in deeply-nested arguments). |
| 331 | `Woett/Lean-files/ErdosProblem331.lean` (raw GitHub, not `%23331.lean`) | **blocked** — gist matches upstream RHS, but multiple drifts: `Lean.Grind.NoNatZeroDivisors (ZMod 4)` typeclass timeout, omega regressions, ambiguous `pow_succ'`. |
| 434 | forum thread `https://www.erdosproblems.com/forum/thread/434`, decoded 357 lines | **disqualified** — uses `axiom theorem_2` from Erdős 433 (no `formal_proof` for #433 to discharge it). |
| 1051 | forum thread `https://www.erdosproblems.com/forum/thread/1051`, decoded 803 lines | **bridge-substantive** — gist compiles cleanly after one trivial fix; bridge needs ≈80 lines for the ℕ→ℤ container conversion + tail-truncation + series decomposition + `Irrational (ℚ + Irrational)`. The most-shippable candidate of the four; deferred only due to per-bridge budget. |

**Net outcome of reassessment:** decoded all four payloads (none was
truly unreachable), but only #1051 is genuinely shippable; #303 and
#331 are blocked by v4.24.0→v4.28.0 drift exactly like the other plby/Aristotle
files (this just shifts the failure mode from "no URL" to "compilation
errors"), and #434 has a fresh axiom dependency.

Sharp updated tally: still **8 shipped**, but the "untested" bucket
collapses from 4 to 0 (all four reachable, reassessed) and the unshipped
remainder gains one more genuinely-actionable candidate (#1051).

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
