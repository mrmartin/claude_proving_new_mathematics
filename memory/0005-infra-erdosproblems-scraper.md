# 0005 — Erdős-Problems scraper (Stage A, slice 1)

**Kind:** infra
**Status:** in-progress (full scrape running in background; this memo
describes the script and intent; an `outcome` section will be filled in
once it lands)
**Date:** 2026-05-10
**Related:** 0002 (survey), `CLAUDE.md` "External resources" section
**Code:** `scripts/scrape_erdosproblems.py`
**Output:** `catalogue/erdosproblems.jsonl`

## Goal

Build the **first slice of the Goal-1 catalogue** (per `CLAUDE.md`):
a one-record-per-problem dump of every page on
[`https://www.erdosproblems.com`](https://www.erdosproblems.com)
from `/1` to `/1217`, capturing status, statement, references, tags,
the partial-results / proofs discussion, and whether the page links
to a `formal-conjectures` Lean file.

`erdosproblems.com` is the highest-leverage external resource for
us — Erdős problems are ~50 % of the upstream `formal-conjectures`
corpus, the URL pattern is a direct integer match
(`FormalConjectures/ErdosProblems/<N>.lean` ↔
`erdosproblems.com/<N>`), and each page authoritatively records
status (open / solved / proved / disproved / disproved-with-Lean)
plus the relevant references. Once this dump exists we can join
it against the Lean repo's own state in a later memo to produce
the full Goal-1 catalogue cross-table (which sorries are still
open vs already shipped vs known-but-not-formalised).

## Scope

This memo and the script cover only **erdosproblems.com**. The
matching scrape of the `formal-conjectures` repo itself (extract
every `theorem` / `lemma`, its `category`, its `formal_proof`
annotation, whether the body is naked `sorry`) is a separate slice
and will get its own infra memo.

## Schema

`catalogue/erdosproblems.jsonl` — one JSON object per line. Fields
(every record is guaranteed to have `id`, `url`, `exists`,
`fetched_at`, `http_status`; the rest are present only when the
page existed and parsing succeeded):

| Field | Type | Description |
| ----- | ---- | ----------- |
| `id` | int | Problem number, 1..1217. |
| `url` | str | `https://www.erdosproblems.com/<id>`. |
| `exists` | bool | False if the page is the missing-page placeholder (e.g. id > current corpus size). |
| `fetched_at` | str | ISO 8601 UTC timestamp. |
| `http_status` | int | HTTP status code (typically 200; -1 on fetch error). |
| `title` | str | The page `<title>`, e.g. `"399 \| Erdős Problems"`. |
| `status_id` | str | The `id="…"` on the main `<div class="problem-text">` — `open` / `solved` / etc. |
| `status_label` | str | The visible text inside the prize tooltip span — `OPEN` / `PROVED` / `DISPROVED` / `DISPROVED (LEAN)` / etc. |
| `status_tooltip` | str | The explanatory tooltip text (e.g. "This has been solved in the negative and the proof verified in Lean."). |
| `statement_html` | str | Inner HTML of `<div id="content">` (LaTeX-flavoured math is preserved verbatim). |
| `statement_text` | str | Whitespace-normalised text of the same. |
| `references` | str | Inner text of `<div id="problem_id">` — typically `#<N>: [<bibkey>]`. |
| `tags` | list[str] | The clickable tags — `["number theory", "factorials"]`, etc. |
| `additional_text_html` / `additional_text_text` | str | The "discussion" block (partial results, counterexamples, references, lemma history). The footer ("View the LaTeX source" / "View history") is stripped. |
| `formalised_in_formal_conjectures` | bool / null | True iff the page has a "Formalised statement? Yes" link to a specific `.lean` file under `google-deepmind/formal-conjectures`. False iff the page renders "Formalised statement? No (Create a formalisation here)". Null if neither could be detected. |
| `formalised_url` | str / null | The `.lean` file URL when formalised, else null. |
| `prize` | str / null | Bounty/prize text inside the `#prize` div, when present. |
| `fetch_error` / `parse_error` | str | Only present on failure rows. |

The fields are written in `dataclasses.asdict` order; consumers
should not rely on field ordering, only on field names.

## Design choices

- **Polite scraping.** Single Firefox-like User-Agent, 0.5s sleep
  between requests, single `requests.Session` for connection
  reuse, `5xx` retries with exponential backoff (`1.5^attempt`).
  Total wall time at ~1217 records: ~10 minutes.
- **Resumable.** Output is JSONL appended one record per request
  with `flush()` after each. If interrupted, re-running the
  script reads the file, builds the set of completed `id`s, and
  skips them. A `--force` flag forces full re-fetch.
- **Robust on failures.** A failed fetch or parse writes a record
  with `fetch_error` or `parse_error` and continues; we never
  abort the whole run on one bad page.
- **Missing-page detection.** `erdosproblems.com/<N>` returns
  HTTP 200 even for non-existent IDs (e.g. `/9999`) with a
  small placeholder. We detect missing pages by checking that
  `<title>` starts with `"<N> |"`. Such records get
  `exists: false` and no further fields.
- **Status-link gotcha.** The "Formalised statement? No" branch
  renders an anchor `<a href="https://github.com/google-deepmind/formal-conjectures">Create a formalisation here</a>`
  pointing at the **repo root**, not a specific `.lean` file.
  An earlier draft of the parser wrongly matched this anchor as
  a "Yes" link. Fixed by requiring `/FormalConjectures/` and
  `.lean` in the href, and bailing on `Create a formalisation here`
  anchor text.

## Smoke test

Verified on `/1`..`/6` (a mix of statuses):

| ID | Status label | Formalised | URL |
| -- | ------------ | ---------- | --- |
| 1 | OPEN | True | `…/ErdosProblems/1.lean` |
| 2 | DISPROVED | False | — (page renders "No (Create a formalisation here)") |
| 3 | OPEN | True | `…/ErdosProblems/3.lean` |
| 4 | PROVED | True | `…/ErdosProblems/4.lean` |
| 5 | OPEN | False | — |
| 6 | PROVED | True | `…/ErdosProblems/6.lean` |

Manual check against the live pages confirms each line. The fix
for the "Create a formalisation here" false positive was caught by
this very test.

## Outcome (filled in after the full run lands)

*To be completed.*

Expected fields in the outcome section, once the scrape finishes:

- Total records fetched, count of `exists=true` vs `exists=false`.
- Status-label breakdown (open / proved / disproved / disproved-lean / other).
- `formalised_in_formal_conjectures` breakdown
  (`True` / `False` / `null`), with a sanity check against the
  number of files actually present under
  `formal-conjectures/FormalConjectures/ErdosProblems/`.
- Top tags by frequency (sanity: should mostly be combinatorics
  and number theory).
- A handful of cross-checks: e.g. for ten random sampled
  formalised problems, confirm the linked `.lean` file exists in
  our local clone.
- Cross-reference against `Subsets/FC100SolvedSet1.lean` and
  `Subsets/FC100OpenSet1.lean`: how many of the
  `formalised_in_formal_conjectures=true` Erdős entries appear
  in each benchmark slice.

## Lessons (pre-outcome)

- The `<a href>`-disambiguation gotcha is a recurring class of
  bug in HTML scraping: any pattern like "the next anchor in
  document order" needs an *exclude* list of "navigation /
  call-to-action" anchors that should not count, in addition to
  the *include* pattern. The fix here adds both — require
  `/FormalConjectures/<...>.lean` *and* bail on
  `Create a formalisation here`.
- Polite 0.5s sleep + connection reuse + retries on 5xx is a
  solid default for scraping a small-volume site like this; it
  costs us ~10 minutes for 1217 pages and minimises load on
  someone else's server.
- For a flat key/value extraction job like this, JSONL is the
  right output format: append-only, line-grep-able,
  `pandas.read_json(..., lines=True)` works directly, and partial
  files remain valid.

## Next

1. Wait for the full scrape to land in `catalogue/erdosproblems.jsonl`.
2. Fill in the **Outcome** section above with the actual
   distribution and sanity checks.
3. **Memo 0006**: build the matching slice for the Lean side —
   walk `formal-conjectures/FormalConjectures/`, extract every
   `theorem`/`lemma`, record `category`, `AMS`, body-is-`sorry`,
   any `@[formal_proof using …]` annotations. Write to
   `catalogue/formal_conjectures.jsonl`.
4. **Memo 0007**: join the two slices into the unified Goal-1
   catalogue. The join key for Erdős problems is the integer
   `id` (filename ↔ URL); for non-Erdős problems we will need
   per-source rules. Output: `catalogue/index.json` plus a
   shortlist memo of the most attractive Goal-2 candidates.
