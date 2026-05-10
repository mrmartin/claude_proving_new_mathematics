# 0001 — Lean 4 + mathlib bootstrap and 1+1=2

**Kind:** setup
**Status:** shipped
**Date:** 2026-05-10
**Related:** none (founding memo)

## Goal

Stand up a working Lean 4 + mathlib environment in this project, end-to-end:
toolchain, project skeleton, mathlib cache, a trivial proof that compiles,
and an axiom check confirming the proof is sound. The trivial proof is the
first sanity-checkable artifact for the rest of the project's tooling.

## Context

Fresh working directory `/mnt/nvme2/atp_runs/claude_proving_new_mathematics/`.
The user installed the lean4-skills marketplace (`npx claudepluginhub
cameronfreer/lean4-skills`) before this session, so the `lean4` and
`lean4-contribute` plugins were already available. The
`SessionStart:startup` hook reported `Lean4 v4 ready: PLUGIN_ROOT=...`.

## Work

1. Confirmed toolchain:
   - `lean --version` → `Lean 4 (4.29.1)`
   - `lake --version` → `Lake 5.0.0-src+f72c35b`
   - `elan` resolves at `/home/martin/.elan/bin/elan`.
2. Created the project with `lake new MyProject math`, which:
   - Wrote `MyProject/lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
     `MyProject/Basic.lean`.
   - Cloned mathlib and its dependencies (plausible, LeanSearchClient,
     importGraph, ProofWidgets, aesop, Qq, batteries, Cli) at the toolchain
     versions pinned by the `math` template.
   - Ran the post-update hook that downloads the mathlib cache from Azure
     (8232 `.olean` files; ~17 s decompress).
3. Edited `MyProject/MyProject/Basic.lean` to:
   ```lean
   import Mathlib

   theorem one_plus_one_eq_two : 1 + 1 = 2 := by rfl

   #print axioms one_plus_one_eq_two
   ```
4. Compiled with `lake env lean MyProject/Basic.lean` (run from
   `MyProject/`). The build succeeded silently apart from the `#print
   axioms` output, which read:

   > `'one_plus_one_eq_two' does not depend on any axioms`

## Outcome

- `MyProject/` builds without errors and proves `1 + 1 = 2` by `rfl`.
- The proof depends on **no axioms** (not even `propext` /
  `Classical.choice` / `Quot.sound`), since `1 + 1 = 2 : ℕ` is a
  definitional equality in Lean 4.
- The mathlib cache is fetched into `MyProject/.lake/`, so subsequent
  builds within this project reuse it.

Project line count for the proof itself: 1 line (the `theorem` line). The
file as a whole is 5 lines including the import and the axiom probe.

## Lessons

- `lake new <name> math` is the right entry point for a mathlib-backed
  project. The post-update hook runs `lake exe cache get` automatically;
  no extra step needed for the first build.
- `1 + 1 = 2 : ℕ` reduces by `rfl` because `Nat.succ` literals are
  definitionally equal. This is a useful baseline: anything more
  interesting will need at least `decide` or `simp`, and any `rfl` proof
  on a non-trivial equation should be checked twice.
- `#print axioms <name>` is the canonical sanity check. "Does not depend
  on any axioms" is the strongest possible result; the next-best is
  the standard trio `propext, Classical.choice, Quot.sound`. Anything
  else means we picked up a custom axiom we did not intend.
- Bash `cd` *does* persist between Bash tool calls in this session
  (I had assumed it didn't and re-checked from the wrong directory; the
  re-check then ran from the right one because the prior `cd MyProject`
  had stuck). Worth remembering: don't sprinkle redundant `cd`s.

## Next

- Memo `0002` documents the survey of `google-deepmind/formal-conjectures`
  that we ran in the same session, which is what actually drives Phase 1
  target selection.
- Future setup memos (if any) belong in this `setup-` family. The next
  setup work likely to need a memo is: choosing where the
  `formal-conjectures` clone lives and what local conventions we adopt
  for working on its files (LSP cold-start, `--wfail build` cycles, etc.).
