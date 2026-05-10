# 0005 — Erdős-Problems scraper (Stage A, slice 1)

**Kind:** infra
**Status:** shipped (full scrape ran 17:55–18:11 UTC on 2026-05-10;
JSONL written; sanity checks below pass)
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

## Outcome

The full run finished cleanly: **1217 records, all live** (no
missing-page placeholders — turns out 1217 is the highest current
problem on erdosproblems.com). Reproducible with
`python3 scripts/summarise_erdosproblems.py`.

### Status-label distribution

| Label              | Count |
| ------------------ | ----- |
| `OPEN`             | 632   |
| `PROVED`           | 216   |
| `PROVED (LEAN)`    | 104   |
| `DISPROVED`        | 74    |
| `SOLVED`           | 68    |
| `DISPROVED (LEAN)` | 54    |
| `FALSIFIABLE`      | 27    |
| `SOLVED (LEAN)`    | 16    |
| `DECIDABLE`        | 9     |
| `VERIFIABLE`       | 7     |
| `NOT DISPROVABLE`  | 4     |
| `NOT PROVABLE`     | 3     |
| `INDEPENDENT`      | 3     |

Open : non-open ≈ 632 : 585. The `(LEAN)` suffix appears on 174
records — these are problems where erdosproblems.com knows a
formal Lean proof exists *somewhere* (not necessarily upstream
in `formal-conjectures` — sometimes a fork or a personal repo).
A `(LEAN)` label on a candidate is a signal to **look up the
linked proof** rather than re-prove.

### Formalised in `formal-conjectures`

| `formalised_in_formal_conjectures` | Count |
| ---------------------------------- | ----- |
| `True`                             | 413   |
| `False`                            | 804   |

The local clone has exactly **413** files under
`FormalConjectures/ErdosProblems/*.lean`, matching the scrape's
413 `True` entries with **zero discrepancies in either direction**
(no scrape-says-formalised-but-no-local-file, no
local-file-but-scrape-doesn't-flag-it). This is the strongest
sanity check we get for free.

### Top tags (sanity)

```
number theory                       576
graph theory                        277
ramsey theory                       119
geometry                            108
additive combinatorics              102
analysis                            80
primes                              62
chromatic number                    61
distances                           55
unit fractions                      49
combinatorics                       47
set theory                          35
sidon sets                          34
divisors                            33
hypergraphs                         32
additive basis                      31
arithmetic progressions             29
polynomials                         26
cycles                              24
turan number                        23
```

This matches the AMS-attribute distribution we'd expect: number
theory dominates, combinatorics in second, graph theory close
behind.

### Benchmark slice cross-reference

| Slice              | Erdős ids | Open on EP | Solved on EP | All formalised? |
| ------------------ | --------- | ---------- | ------------ | --------------- |
| `FC100SolvedSet1`  | 43        | 28         | 15           | 43 / 43         |
| `FC100OpenSet1`    | 46        | 43         |  3           | 46 / 46         |

Note: the `FC100SolvedSet1` "Erdős ids" column counts erdosproblems.com
**problem numbers** referenced from FC100SolvedSet1, not theorem
declarations. Many of the 43 are research-open headlines whose
`*.variants.*` solved sub-claims are what FC100SolvedSet1 actually
benchmarks. The next slice (memo 0006) will catalogue at the
declaration level so this column becomes "FC100SolvedSet1
sorry-bearing variants by Erdős id" and we can target benchmark
deltas precisely.

### Goal-2 candidate pool, first cut

Erdős problems where:

- the statement is already formalised in `formal-conjectures`
  (i.e. `FormalConjectures/ErdosProblems/<N>.lean` exists), AND
- `erdosproblems.com/<N>` reports an informally-solved status
  (`status_id == "solved"`), AND
- the status label does **not** carry the `(LEAN)` suffix
  (so the page does not yet know a formal Lean proof exists
  anywhere)

| Bucket | Count |
| ------ | ----- |
| SOLVED + formalised + **no Lean proof yet** (Goal-2 targets) | **48** |
| SOLVED + formalised + page already cites a Lean proof (skip) | 53 |

First 10 candidate ids:
`4, 6, 13, 42, 48, 67, 69, 109, 139, 152`.

This is the pool to filter further once we have the Lean-side
catalogue (memo 0006) — a candidate qualifies as a Goal-2 *target*
only if its `.lean` file still has at least one naked sorry on
the headline statement or a `*.variants.*` declaration.

### Caveats

- **Problem-level granularity.** This catalogue is one record per
  Erdős problem *number*, not per theorem declaration. The cambie
  work was on `Erdos399.variants.cambie`, which is one of *four*
  sorries inside `ErdosProblems/399.lean`. Erdős 399's page
  status is `DISPROVED (LEAN)` because the headline is disproved
  by Barfield's `10! = 48⁴ − 36⁴` (which the file proves inline
  with `decide`). The variant-level structure is invisible at
  this layer and only surfaces in the Lean-side catalogue.
- **`(LEAN)` doesn't mean "linked here".** A page can be tagged
  `PROVED (LEAN)` because someone formalised the proof in a
  personal fork or a Mathematica-style gist; the link is on
  the page text, not in our scrape's structured fields.
  Following each link is per-target work in memo 0007.
- **`erdosproblems.com` may be stale.** We treat it as
  authoritative for "is this already solved informally?" but
  not for "is this proof in `formal-conjectures` master right
  now?" — the upstream Lean repo is authoritative for that, and
  memo 0006 will be its scrape.

## Lessons

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
