# Project briefing — `claude_proving_new_mathematics`

This file is auto-loaded into every Claude Code conversation that starts in
this directory. **Read it before doing anything else** — and especially before
suggesting tools, files, or strategies. It encodes the decisions and lessons
already worked out, so we don't relitigate them every session.

The project pairs Claude Code (Opus, with the lean4-skills plugin) with a goal
of contributing meaningful Lean 4 theorem-proving work to
`google-deepmind/formal-conjectures` and, eventually, proving genuinely new
mathematics.

---

## Vocabulary — be precise about which kind of work

`formal-conjectures` mixes several activities that look similar from a
distance but are not. Always classify the work along **two orthogonal
axes** before picking it up.

**Axis 1 — Defining vs. Solving.**

- **Defining the problem in Lean 4.** Writing a Lean statement of a
  problem and shipping it with `:= by sorry` plus sanity-check tests.
  Most `good first issue` tickets and most upstream issues (e.g.
  `#710` for Erdős 399) close when *the file with the statement
  exists* — they do **not** require a proof. The deliverable is a
  faithful Lean translation of the informal statement.
- **Solving the problem.** Replacing a `:= by sorry` with a real
  Lean proof. The deliverable is a working proof in the upstream-cap
  budget (≤ 25–50 lines inline, or longer in a companion repo with a
  `formal_proof using lean4 at "..."` link). This is a separate PR from
  the defining one and never closes the original `defining` issue.

**Axis 2 — Writing up a known proof vs. Coming up with a new proof.**

- **Writing up a known proof.** The mathematical proof already exists
  somewhere — a paper, textbook, classical result, even a forum
  comment. Our work is *translation into Lean*. Mathematical
  originality is zero; formalization-engineering value is real.
- **Coming up with a proof hitherto unknown.** Proving something
  where no informal proof yet exists in the literature. This is
  *new mathematics*. It is much harder, much rarer, and we treat
  it accordingly.

**The 2×2 we sit in:**

|                          | **Defining (statement only)** | **Solving (filling a sorry)** |
| ------------------------ | ----------------------------- | ----------------------------- |
| **Known informal proof** | `formal-conjectures`' job — they own this column. | **Goal 2 of this project.** Pick a sorry whose informal proof is in the literature, write the Lean version. |
| **No known proof**       | `formal-conjectures`' job too. | **Goal 3 of this project.** Pick a sorry whose proof exists *nowhere yet* — informal or formal — and produce one. |

Always classify the target before starting. Memos must say *which
cell* the work falls in. Never describe Goal-2 work as "proving new
mathematics" — that conflates known-proof formalisation with novel
proof creation.

**Off-limits — `formal-conjectures`' spirit, which is theirs.**
The whole left column ("defining the problem in Lean") is *their*
mission, not ours. We never close upstream issues like
[`#991` (formalise Erdős 869)](https://github.com/google-deepmind/formal-conjectures/issues/991)
that ask for a new statement to be added. We never write a new
`theorem foo : P := by sorry` in their repo as a contribution.
Erdős 869 is informally disproved on
[`erdosproblems.com/869`](https://www.erdosproblems.com/869) — but
*the statement is not in the repo yet*, so there is no sorry for us
to fill, so it is not a target for us. The same diagnostic applies
to every candidate: **is the statement already formalised? if not,
ignore.**

## Goals (in order — a pipeline, not parallel)

1. **Goal 1 — Catalogue.** Build and maintain a precise map of
   what's already formally proved in `formal-conjectures`:
   - **inline-proved** (body is not `sorry`),
   - **linked elsewhere** (body is `sorry` plus a `@[formal_proof using …]` annotation),
   - **naked sorry, known informally** (`category research solved`/`textbook`/`test` with no annotation),
   - **naked sorry, unknown** (`category research open` with no annotation).

   The catalogue lives in this repo (`catalogue/` directory) as
   machine-readable JSON plus a Markdown summary memo. Goals 2 and 3
   each pull their candidates from a different column; without the
   catalogue we can't tell "still open" from "already shipped
   elsewhere."

2. **Goal 2 — Formalise known proofs.** Lower-right cell of the
   2×2: take a naked sorry whose informal proof is in the literature
   and write the Lean version.
   - **Short** (≤ 25–50 lines): inline in `formal-conjectures`,
     PR upstream when the user gives the go-ahead.
   - **Long** (more than that): full proof in `proofs/` of *this*
     repo, plus a one-line `@[formal_proof using lean4 at "<our-url>"]`
     annotation upstream. The upstream README explicitly invites
     this and it removes the 25–50-line ceiling without violating
     their rules.

   **HARD GATING RULE — main-problem status, not variant status.**
   For any candidate from `FormalConjectures/ErdosProblems/N.lean`,
   the very first check before opening a target memo is the status
   of the *main problem* on `erdosproblems.com/N`:
   - If `erdosproblems.com/N` reports **OPEN** → the entire file is
     off-limits for Goal 2, *including any `variants.*` declaration
     inside it whose specific sub-statement has a known proof*. We
     do not work on solved subproblems of open Erdős problems —
     that work doesn't advance our Goal 2 KPI and is easy to
     mis-describe as "solving an Erdős problem" when it doesn't.
   - If `erdosproblems.com/N` reports **SOLVED** or **DISPROVED**
     → the file is in-scope for Goal 2. Pick the right variant.
   - If `erdosproblems.com/N` reports **OPEN** but a variant has a
     known proof → it may still be Goal-3-adjacent (a partial result
     on an open problem), but only if the variant is itself novel
     enough to write up; if the variant was solved long ago by a
     classical theorem it is *neither* Goal 2 nor Goal 3 for us.
   For non-Erdős files (`OeisA…`, `Mathoverflow/…`, `Paper/…`,
   `Wikipedia/…`, etc.), apply the analogous status check against
   the natural external source before targeting.

   Past misclassifications under this rule (do not repeat):
   - Erdős 1113 (Sierpiński numbers): `erdosproblems.com/1113` is
     OPEN (smallest-Sierpiński question, "Seventeen or Bust"). The
     `infinitely_many_sierpinski` variant has Sierpiński's 1960
     proof but is off-limits because the parent is open. See memo
     `0022`.
   - Erdős 1054 (Schmerl): `f 2 = 0` is a definitional triviality
     in the upstream Lean encoding, not a solution. See memo `0020`.

3. **Goal 3 — Solve unsolved formalised problems.** Lower-left
   cell: a sorry whose proof exists *nowhere* — neither inline,
   nor linked, nor in any informal source we can find. Produce a
   formal proof. This is the apex goal. Yield will be very low —
   most `category research open` entries are Riemann-/Goldbach-class
   — but the catalogue makes the search systematic. Even an
   *interesting partial result* (a counterexample, a conditional
   proof, a sharp special case) on a previously-unsettled
   formalised conjecture counts.

We do **not** chase low-hanging fruit (pure `decide` testcase PRs,
trivial restatements, metadata-only PRs, *defining* PRs that just
add new sorries). We do **not** chase Fields-medal-level problems
where the informal proof is itself a research paper we cannot reach.

---

## Environment & layout

- Working directory: `/mnt/nvme2/atp_runs/claude_proving_new_mathematics/`
- Toolchain: Lean 4 via `elan`, mathlib pinned at the version each project
  declares in `lean-toolchain` and `lakefile.toml` (formal-conjectures
  currently uses `v4.27.0`; our `MyProject/` smoke test uses `v4.29.1`).
- Plugins installed: `lean4-skills` (the `lean4:*` slash commands), and
  `lean4-contribute` (commands to draft bug reports / feature requests /
  shareable insights when relevant).

Repo layout (committed):

```
.
├── CLAUDE.md                    # this file
├── README.md                    # project overview + memo index table
├── .gitignore                   # ignores .lake/ build artifacts and the upstream clone
├── memory/                      # one Markdown memo per piece of work
│   ├── 0001-...
│   └── ...
└── MyProject/                   # smoke-test Lean project (1+1=2 etc.)
```

**Not committed but expected to be present locally:**

- `formal-conjectures/` — clone of `https://github.com/google-deepmind/formal-conjectures`
  at the repo root. Git-ignored on purpose; it is upstream code, not ours. If
  it is missing, `git clone https://github.com/google-deepmind/formal-conjectures.git`
  from the repo root and then `cd formal-conjectures && lake exe cache get`.
- `MyProject/.lake/` — Lake build artifacts. Git-ignored.

---

## Skills & how to use them

The `lean4-skills` plugin exposes slash commands. The most relevant ones, in
the order you will reach for them:

- `/lean4:learn --mode=repo` — orient yourself in an unfamiliar Lean repo.
- `/lean4:learn --mode=mathlib` — search mathlib for an unfamiliar topic.
- `/lean4:prove` — guided cycle-by-cycle proving of a single sorry, with
  user-facing checkpoints. Default for the first few proofs of a new topic.
- `/lean4:autoprove` — autonomous cycles. Use only after `/lean4:prove`
  has confirmed the goal is in scope and the user has signed off on
  unattended work.
- `/lean4:review` — read-only sanity check.
- `/lean4:refactor`, `/lean4:golf` — apply *after* the proof compiles, to
  shrink it within the repo's line-length and style limits.
- `/lean4:doctor` — diagnose environment problems (LSP cold, missing scripts,
  cache misses).

The base `lean4:lean4` skill is auto-invoked when a `.lean` file is being
edited; do not invoke it manually.

If a question is about Claude Code itself (hooks, settings, MCP, the SDK),
the `claude-code-guide` agent is the right tool, not a web search.

---

## Process — what to do at the start of every session

1. **Read this file and `README.md`.** The README's memo table tells you
   what we have already tried, learned, and shipped.
2. **Read the most recent memo.** It is the entry point to the current
   work. If the user's request is a continuation, scan back through the
   memo chain until you have full context.
3. **State the plan, then act.** One short sentence before the first tool
   call. Don't narrate; the diff and the memo are the audit trail.
4. **Open or update a memo for the current task.** See "Memory discipline"
   below. The memo is for *future you* — make it usable cold.
5. **Commit and push after every addition.** Durable user
   preference (2026-05-10): every time work produces a shippable
   artifact — a new memo, an updated index entry, a working proof,
   a doc edit — `git add` the touched files, commit with a focused
   message, and `git push origin main` immediately. Do not batch:
   small commits, one logical change each, pushed as they happen.
   - Remote: `git@github.com:mrmartin/claude_proving_new_mathematics.git`.
   - Never `git add -A`; stage explicit paths only.
   - Never force-push or rewrite history without explicit ask.
   - Pre-commit hook failures = fix the issue and create a *new*
     commit; never `--amend` the failed one.
   - Skipping this rule (e.g. "I'll commit later") is itself a
     deviation worth flagging to the user.

---

## Memory discipline

The `memory/` directory is the durable record. README.md indexes it. Every
memo is one piece of work — a setup, a survey, a target evaluation, an
attempt (success or failure), an infrastructure note, or an idea worth
remembering.

**File naming.** `NNNN-<kind>-<short-topic>.md`, where:

- `NNNN` is a four-digit zero-padded counter, monotonically increasing.
  The counter is global; never reuse a number, even for retracted memos.
- `<kind>` is one of:
  - `setup` — environment, tooling, project skeleton work.
  - `survey` — reading a repo, paper, or codebase to understand the lay of
    the land. Output is structured findings, not edits.
  - `target` — evaluation of a specific problem we might attack. Includes
    the informal proof sketch and a feasibility verdict.
  - `attempt` — a serious proof attempt that hasn't yet shipped.
  - `proof` — a successful formal proof, with the final tactic listing,
    the mathlib lemmas it leans on, and the line count.
  - `fail` — an attempt we abandoned. **Always write the memo.** Saying
    "we tried X and it didn't work because Y" saves the next session days.
  - `infra` — repo-wide infrastructure (CI, scripts, conventions).
  - `idea` — a contribution direction worth remembering but not yet
    chosen.
- `<short-topic>` is kebab-case, descriptive enough that the filename
  alone tells you what's inside. `0017-target-erdos-350-ryavec.md` is
  good; `0017-target.md` is not.

**Memo body.** Plain Markdown. Start with a one-line summary. Then the
sections that fit; not every memo needs every section:

```markdown
# <human title>

**Status:** <in-progress | shipped | abandoned | superseded by NNNN>
**Date:** YYYY-MM-DD (start) — YYYY-MM-DD (last edit)
**Related:** NNNN, NNNN
**Upstream link:** <issue/PR/file URL if applicable>

## Goal
What we set out to do, in one paragraph.

## Context
What state the project was in, what the user asked for, what assumptions
this memo makes about prior memos.

## Work
The actual chronicle: commands run, files touched, results, key tactic
choices, mathlib lemmas leaned on. Specific enough that someone can
reconstruct the work.

## Outcome
What shipped (or didn't), measured against the goal. Include line counts
and axiom checks for proofs.

## Lessons
Anything worth remembering for the next memo: a tactic that worked, a
mathlib name we kept missing, a repo convention we tripped on.

## Next
Concrete follow-ups. If the next memo is queued, name it.
```

**Update the README index whenever you create or change a memo.** The
table is the navigation surface. If the table is out of sync with the
files, fix the table first.

---

## Rules from `formal-conjectures` we must respect

These come from the upstream `README.md`, `AGENTS.md`, and
`CONTRIBUTING.md`. They are non-negotiable when we PR there.

- `lake --wfail build` must pass with zero warnings.
- Inline proofs ≤ 25–50 lines per the upstream README. Longer proofs go
  in our own repo and are linked via `@[formal_proof using lean4 at "<url>"]`.
- Never edit a theorem statement, type signature, or docstring without
  explicit user permission.
- Do not introduce custom axioms.
- `native_decide` is banned in `FormalConjecturesForMathlib/` and
  case-by-case in problem files. Prefer `decide`, `decide +kernel`, or a
  real proof.
- Files start with the upstream copyright header (year = current year).
- Module docstrings include reference links; `research open`, `research
  solved`, and `textbook` theorems each need a concise docstring describing
  the problem.
- Names follow mathlib conventions (`snake_case` for terms of `Prop`,
  `UpperCamelCase` for types/structures/classes).
- Use Unicode math symbols where mathlib does.
- Every theorem has exactly one `@[category ...]` and at least one
  `@[AMS ...]`.
- A signed Google CLA is required before any PR is merged. The user
  handles signing; we do not assume it.

---

## Approach we have committed to (the staged pipeline)

The three goals run as **stages, not in parallel**. Stage A gates
B; B and C feed off A.

1. **Stage A — build the catalogue (Goal 1).** Script
   `formal-conjectures/FormalConjectures/` for every `theorem` /
   `lemma`, extract: file path, fully-qualified name,
   `@[category …]`, `@[AMS …]`, whether the body reduces to a naked
   `sorry` or `by sorry`, and any `@[formal_proof using <kind> at
   "<url>"]` annotations (kind + URL each). Output to
   `catalogue/index.json` (machine-readable) plus a Markdown
   summary memo in `memory/`. Re-run the script when upstream
   updates. The catalogue, not ad-hoc grep, is the candidate
   pool for stages B and C.
2. **Stage B — Goal 2 work.** Filter the catalogue to "naked
   sorry, known informally" (mostly `category research solved`
   with no `formal_proof` annotation). Pick by tractability and
   mathlib readiness, the same way memo `0002` did. Two formats:
   - **Short** (≤ 25–50 lines): inline in `formal-conjectures`,
     PR upstream when the user gives the go-ahead. (`cambie`
     was item 1 of this stream.)
   - **Long**: full proof in `proofs/` of *this* repo, then PR
     upstream a one-line `@[formal_proof using lean4 at
     "https://github.com/mrmartin/claude_proving_new_mathematics/..."]`
     annotation. The upstream README explicitly invites this.
3. **Stage C — Goal 3 work.** From the "naked sorry, unknown"
   column. Bias toward small variants of bigger problems, sharp
   computational claims about specific objects, and combinatorial
   conjectures where mathlib has the heavy machinery and the
   missing piece is one new lemma. An interesting *partial* result
   (counterexample, conditional proof, sharp special case) on a
   previously-unsettled formalised conjecture counts.

Procedural rules (apply across stages):

- We avoid `native_decide`, deep paper-only proofs, and anything
  that needs new ForMathlib API beyond what we can build in the
  same PR.
- Every target gets a `target-...` memo first. The memo states
  **which cell of the 2×2 the work falls in**, what's been
  checked against erdosproblems.com or the relevant external
  source, the informal proof sketch (or "no informal proof" for
  Goal 3), the mathlib lemmas we expect, a line budget, and a
  go/no-go verdict. We do not start proving until the target
  memo exists.
- After a successful proof, we write a `proof-...` memo with the
  final tactic listing, the axiom-check output, and (importantly)
  an honest note distinguishing *what was already in the literature*
  from *what was new in this PR*. For Goal 2 work that note is
  "the proof was already known; this PR is the formal translation."
  For Goal 3 work it states the actual mathematical contribution.
- After a failed attempt, we write a `fail-...` memo.
- Goal 3 contributions never get described in commit messages,
  PR bodies, or memos using language stronger than the
  mathematical reality. If the contribution is a partial result,
  say partial; if it's conditional, say conditional. **Goal-2
  work is never described as Goal-3 work.**

**Working principles for new mathematics, when we get there:**

- Mathlib search before tactic search. If a result exists, find it; don't
  reprove it.
- LSP-driven inspection (`lean_goal`, `lean_multi_attempt`,
  `lean_diagnostic_messages`) is faster and cheaper than `lake build`
  cycles. Reach for it first.
- Failed attempts are data. Memo them with the actual error messages and
  the tactic ladder we tried.
- Build a private "phrasebook" memo of mathlib names we keep needing.
  Future-you will thank present-you.
- Verify, don't trust. Re-grep, re-build, re-`#print axioms` before
  claiming a proof is done.
- Quote artifacts when scheduling follow-ups (issue numbers, file paths,
  commit hashes). Future memos are searchable; vague references are not.

---

## External resources — where to look up status

When evaluating a candidate, check these external lookups
*before* writing a target memo. Status from these resources tells
us whether a problem has an informal proof (Goal 2 territory), a
formal proof shipped elsewhere (skip), or genuinely no proof at
all (Goal 3 territory).

- **`https://www.erdosproblems.com/<N>`** — definitive lookup for
  any Erdős problem `N`. Erdős problems form ~50% of the
  `formal-conjectures` corpus, so this is the highest-leverage
  resource we have. Each page lists status (open / solved /
  disproved), references to the relevant papers, and (when known)
  links to formal proofs in Lean / Coq / etc. Treat it as
  authoritative for "is this already shipped elsewhere?".
  Example: `erdosproblems.com/399` for `Erdos399.*`,
  `erdosproblems.com/869` for `Erdos869.*`. The numeric suffix in
  upstream filenames (`FormalConjectures/ErdosProblems/N.lean`)
  matches exactly.

  **First action on any new candidate: `WebFetch erdosproblems.com/N`.**
  Read the status line. If it says OPEN, the whole file is
  off-limits for Goal 2 — every variant, every `.variants.*`
  sub-statement, regardless of whether someone published a proof
  of the specific variant. See the "HARD GATING RULE" under
  Goal 2 above. Repeat misses of this check have wasted shipped
  work twice (memos `0020`, `0022`); the check is now mandatory
  before any other lookup.
- **`https://oeis.org/A<NNN>`** — OEIS for any `OeisA<NNN>` file
  in the repo. Useful for sequence-based conjectures, with
  references and known formulae.
- **`https://en.wikipedia.org/wiki/<conjecture>`** — for
  `Wikipedia/*.lean` files; sometimes lists a Lean formalisation.
- **`https://mathoverflow.net/questions/<id>`** — for
  `Mathoverflow/<id>.lean` files. Often the comments include
  partial proofs or counterexample constructions.
- **arXiv links** — most `Paper/` and `Arxiv/` files cite the
  source paper. The paper *is* the informal proof for those
  entries.
- **Mathlib search via the lean4-skills LSP tools** —
  `lean_local_search`, `lean_leanfinder`, `lean_loogle`,
  `lean_leansearch`. Run these before tactic search; if a lemma
  already exists, find it.
- **`formal-conjectures` issue tracker** — search by problem
  number to see whether somebody else is already working on
  the *defining* PR (off-limits for us) or the *solving* PR
  (potentially relevant; coordinate via Zulip if so).
- **Upstream `Subsets/FC100SolvedSet1.lean` and `FC100OpenSet1.lean`** —
  curated benchmark slices. Proofs in `FC100SolvedSet1` count
  as benchmark deltas; proofs in `FC100OpenSet1` are Goal-3
  attempts on genuinely open problems.

When the catalogue (Goal 1) is built, every entry should have a
**`status_url`** field with the relevant external lookup, so
future targeting reduces to a table query rather than a manual
search.

## Reminders

- The `formal-conjectures` repo's contribution channel is the leanprover
  Zulip `#Formal-conjectures` and GitHub issues / PRs. Coordinate with
  the user before opening PRs; do not auto-publish.
- Pushing to `git@github.com:mrmartin/claude_proving_new_mathematics.git`
  is fine when the user asks. Force-pushing or destructive `git` is not
  fine without explicit instruction, even on this repo.
- The user's email is `martin@martintech.co.uk` (commit-author info).
