# 0006 — Lean-side Erdős catalogue (Stage A, slice 2)

**Kind:** infra
**Status:** shipped
**Date:** 2026-05-10
**Related:** 0005 (web-side scrape), `CLAUDE.md` "External resources"
**Code:** `scripts/lean_to_jsonl.py`, `scripts/summarise_lean_erdos.py`
**Output:** `catalogue/formal_conjectures_erdos.jsonl` (1322 records)

## Goal

Capture the **declaration-level state** of every theorem / lemma in
`FormalConjectures/ErdosProblems/` — name, category, AMS subjects,
statement, docstring, formal-proof annotation, and (crucially) whether
the body still contains a `sorry`. This is the second slice of the
Goal-1 catalogue; the first (memo `0005`) was the
`erdosproblems.com` scrape at problem-level granularity. Joining the
two slices on `problem_id` gives the immediate Goal-2 candidate
pool at declaration granularity.

## Method — use the upstream extractor, not a hand-rolled parser

`google-deepmind/formal-conjectures` ships
`scripts/extract_names.lean`, a Lean 4 executable that imports every
module in `FormalConjectures/ErdosProblems/`, walks the environment,
and emits per-theorem JSON with:

- `theorem` (fully-qualified name)
- `module` (e.g. `FormalConjectures.ErdosProblems.«399»`)
- `category` (`research open` / `research solved` / `textbook` /
  `test` / `API`)
- `subjects` (list of AMS strings)
- `statement` (the pretty-printed Lean type)
- `docstring`
- `formalProofKind` (`lean4` / `formal_conjectures` / `other_system` / null)
- `formalProofLink` (the URL of an external proof, if any)
- `hasSorryFreeProof` (the **authoritative** sorry flag — from
  `info.value? |>.any (!·.hasSorry)`, i.e. the actual Lean expression
  has no `sorry` term)

This is dramatically better than a regex parser:

- It uses Lean's own AST and environment, so multi-line attributes,
  nested namespaces, comments, and the `:= by sorry` vs `:= sorry`
  distinction are all handled correctly.
- It cross-checks attributes via the typed `Category` /
  `FormalProofKind` definitions in
  `FormalConjectures/Util/Attributes/Basic.lean`, not by string.
- `hasSorryFreeProof` is the kernel truth — not a textual heuristic.

We invoke it as:

```bash
cd formal-conjectures
lake exe extract_names FormalConjectures/ErdosProblems > /tmp/extract_erdos.json
```

then `scripts/lean_to_jsonl.py` converts the single-object JSON to
JSONL (one record per line) and adds two derived fields:

- `problem_id` (int) — extracted from the module name's
  `«N»` suffix, used to join against `catalogue/erdosproblems.jsonl`.
- `erdosproblems_url` — `https://www.erdosproblems.com/<problem_id>`,
  for one-click external lookup.
- `lean_file` — relative path of the source file.

## Schema

`catalogue/formal_conjectures_erdos.jsonl` — one JSON object per line:

| Field | Type | Description |
| ----- | ---- | ----------- |
| `problem_id` | int | The Erdős problem number (extracted from the module name). |
| `theorem` | str | Fully-qualified Lean name, e.g. `Erdos399.erdos_399.variants.cambie`. |
| `module` | str | Lean module name, e.g. `FormalConjectures.ErdosProblems.«399»`. |
| `category` | str | One of `research open` / `research solved` / `textbook` / `test` / `API`. |
| `subjects` | list[str] | AMS subject codes, e.g. `["11"]` or `["5", "11"]`. |
| `statement` | str | Pretty-printed Lean type. |
| `docstring` | str / null | Theorem docstring if present. |
| `formal_proof_kind` | str / null | One of `lean4` / `formal_conjectures` / `other_system`, when an `@[formal_proof using …]` annotation is present. |
| `formal_proof_link` | str / null | URL inside the annotation. |
| `has_sorry_free_proof` | bool | **Authoritative.** True iff the Lean kernel sees a proof term with no `sorry`. |
| `module_docstring` | str / null | The file's `/-! … -/` module docstring. |
| `erdosproblems_url` | str | Cross-link to the page. |
| `lean_file` | str | `FormalConjectures/ErdosProblems/<id>.lean`. |

## Outcome

```
declarations in Lean Erdős corpus: 1322
unique problem ids: 413
```

(Matches the file count under `FormalConjectures/ErdosProblems/`
and the 413 `formalised=True` rows in
`catalogue/erdosproblems.jsonl`.)

### Category breakdown (declaration-level)

| Category | Count |
| -------- | ----- |
| `research solved` | 554 |
| `research open` | 552 |
| `test` | 118 |
| `textbook` | 63 |
| `API` | 35 |

### Sorry status by category

| Category | `has_sorry_free_proof` False (still sorry) | True (proved) |
| -------- | --: | --: |
| `research open` | 552 | 0 |
| `research solved` | 529 | 25 |
| `textbook` | 39 | 24 |
| `test` | 29 | 89 |
| `API` | 1 | 34 |
| **total** | **1150** | **172** |

So **172 of the 1322 Erdős declarations are already proved**
(13 %), and 1150 still have a sorry. Of the proved ones, 25 are
`research solved` declarations — these are completed Goal-2 work,
either from upstream contributors or (one of them, now)
`erdos_399.variants.cambie` from us.

### `formal_proof` annotations

| Kind | Count |
| ---- | ----- |
| `lean4` | 47 |
| `formal_conjectures` | 28 |
| `other_system` | 2 |
| **none** | **1245** |

A `formal_proof` annotation means somebody has shipped a proof
elsewhere (a fork, a personal repo, another formal system).
Declarations carrying one are *not* Goal-2 targets — the proof
corpus is already covered. The 1245 with no annotation are the
unconstrained candidate pool.

### Goal-2 candidate shortlist (declaration-level): **452**

Filter:

- `has_sorry_free_proof == False` (body still `sorry`)
- `formal_proof_kind == None` (nobody has shipped a proof anywhere)
- `category in {"research solved", "textbook"}` (informally known)
- erdosproblems.com page status_label does **not** carry the
  `(LEAN)` suffix (page does not yet know of any Lean proof)

452 declarations match. The first dozen by problem id:

```
#1   OPEN             research solved   Erdos1.erdos_1.variants.lb
#1   OPEN             research solved   Erdos1.erdos_1.variants.lb_strong
#1   OPEN             research solved   Erdos1.erdos_1.variants.least_N_5
#1   OPEN             research solved   Erdos1.erdos_1.variants.least_N_9
#4   PROVED           research solved   Erdos4.erdos_4
#4   PROVED           research solved   Erdos4.erdos_4.variants.rankin
#6   PROVED           research solved   Erdos6.erdos_6
#6   PROVED           research solved   Erdos6.erdos_6.variants.decreasing
#6   PROVED           research solved   Erdos6.erdos_6.variants.increasing
#9   OPEN             research solved   Erdos9.erdos_9.variants.infinite
#10  OPEN             research solved   Erdos10.erdos_10.variants.gallagher
#10  OPEN             research solved   Erdos10.erdos_10.variants.grechuk_example
```

(Several of the `OPEN` page-status entries are interesting: the
*headline* problem on erdosproblems.com is open, but the file's
**variants** include classical/known partial results that are
formalised as `research solved`. Those are valid Goal-2 candidates —
the headline being open does not block the variant.)

The full list (`scripts/summarise_lean_erdos.py | head -500`)
shows clusters worth attacking together. For example, problem `#36`
contributes 11 candidates (`minimum_overlap.variants.{lower,upper}.<author>_<year>`)
— a single-paper formalisation pass could close several at once.

### Cambie sanity

The proof we shipped in memo `0004` is reflected in the catalogue:

```
Erdos399.erdos_399.variants.cambie:
  has_sorry_free_proof = True
  category             = research solved
  formal_proof         = None
```

i.e. the kernel now sees no `sorry` for cambie, the category is
unchanged, and we did not (yet) add a `formal_proof` annotation.
This validates the pipeline end-to-end: the Lean side reflects the
real source state and the slice is reproducible.

### Cross-check: `(LEAN)` pages vs `formal_proof` annotations

| Quantity | Count |
| -------- | ----: |
| pages with status label `*(LEAN)` | 174 |
| problem ids with at least one declaration carrying a `formal_proof` annotation | 61 |
| intersection | 47 |

Read this as: 174 pages know of *some* Lean proof, 61 problem
files declare it formally via a `formal_proof` annotation, and the
47-element intersection is where both layers agree. The
174 − 47 = 127 pages tagged `(LEAN)` but with no upstream
`formal_proof` annotation are pages where the Lean proof lives in
a personal repo / gist linked from the page itself, but
nobody has yet PR'd the upstream annotation. **These are the
"Goal-2 short" cases where the work is "find the linked external
proof, port the salient parts inline (≤ 50 lines), or just PR
the annotation upstream."** A productive, low-mathematical-risk
direction once we want a string of small upstream PRs.

## Lessons

- **Use the upstream extractor.** A regex parser would have
  re-implemented half of Lean's elaborator. `extract_names.lean`
  uses the actual environment and the actual attribute machinery,
  so its output is the same source of truth used by upstream
  CI's lints.
- **Cross-checks are free quality.** The "413 .lean files = 413
  scrape rows = 413 distinct `problem_id`s in the Lean
  catalogue" three-way agreement is the strongest sanity result
  we get. If a future memo reports a different number, that's
  the signal that something has drifted.
- **Granularity matters.** Going from problem-level (the web
  scrape) to declaration-level (this slice) takes the candidate
  pool from "48 problem files" to "452 declarations". Many
  problem files have several `*.variants.*` declarations whose
  status differs from the headline — a factor we couldn't see at
  problem-level.
- **The 174 vs 47 gap is a real opportunity.** 127 problems where
  erdosproblems.com knows of a formal proof but
  formal-conjectures has no `formal_proof` annotation = 127 small
  upstream PRs we could open with extremely low mathematical
  risk. These are not Goal-2 *proof* work; they are
  metadata-completeness PRs. The user has explicitly said
  metadata-only PRs are not strong contributions, so we
  deprioritise these — but they're useful to know about.

## Next

1. **Memo `0007`**: pick the first concrete Goal-2 target from the
   452-declaration shortlist using a richer ranking heuristic
   (number of mathlib lemmas needed; statement length; proximity
   to existing proved siblings in the same file). The cambie
   work was on the file with the deepest variant chain; we want
   the next pick to be either (a) easier and quicker, or (b)
   long-form proof exercising the `proofs/` + `formal_proof using
   lean4 at "<our-url>"` mechanism for the first time.
2. **Memo `0008`**: extend the catalogue to the rest of
   `FormalConjectures/` — Wikipedia, OEIS, GreensOpenProblems,
   Paper, Arxiv, etc. The same `extract_names` invocation gives
   us all of it; the only adapter needed is per-source URL
   joining (e.g. `OeisANNNNN.lean ↔ oeis.org/A<NNNNN>`).
