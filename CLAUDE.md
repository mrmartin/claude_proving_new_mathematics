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
| **Known informal proof** | Many `good first issue` tickets — pick a known conjecture from a list, write its Lean statement, ship `:= by sorry`. | **Phase 1 of this project.** Take a sorry whose informal proof is in the literature and write a Lean version. |
| **No known proof**       | Defining a genuinely open conjecture. The headline `category research open` files in the repo. | **Phase 2 of this project.** Proving an open conjecture. Out of reach until Phase 1 has produced merged PRs. |

Always classify the target before starting. Memos must say *which
cell* the work falls in. Never describe Phase 1 work as "proving new
mathematics" — that conflates known-proof formalisation with novel
proof creation.

## Goals (in order)

1. **Phase 1 — solving with known proofs.** Lower-right cell:
   replace `:= by sorry` placeholders in `formal-conjectures` whose
   informal proofs already exist in the literature with short
   (≤ 25–50 line) Lean proofs. Prefer `category research solved`,
   `category textbook`, `category test`, and `category API`. Avoid
   `category research open` unless the variant is a known classical
   result.
2. **Phase 2 — solving with new proofs.** Lower-left cell:
   genuinely open problems where Claude's strengths (mathlib search,
   definitional bookkeeping, tactic enumeration) give us a real shot.
   We do not pretend Phase 2 work until Phase 1 has produced merged
   PRs.

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

## Approach we have committed to

This is the strategy worked out in the founding session and ratified by
the user (memo `0002-survey-formal-conjectures-repo.md` records the full
analysis):

1. We start in **Phase 1** — *solving with known proofs*. Targets are
   `:= by sorry` placeholders in `category research solved`,
   `category textbook`, `category test`, and `category API` files
   whose informal proof already exists in the literature. We prefer
   the `Subsets/FC100SolvedSet1` list because every proof there
   directly improves the published benchmark.
2. We avoid `native_decide`, deep paper-only proofs, and anything that
   needs new ForMathlib API beyond what we can build in the same PR.
3. Each target gets a `target-...` memo first. The memo states **which
   cell of the defining/solving × known/unknown 2×2 the work falls
   in**, the informal proof sketch, the mathlib lemmas we expect to
   need, an estimated line budget, and a go/no-go verdict. We do not
   start proving until the target memo exists.
4. After a successful proof, we write a `proof-...` memo with the
   final tactic listing, the axiom-check output, and (importantly)
   an honest note distinguishing *what was already in the literature*
   from *what was new in this PR*. For Phase 1 work that note is
   "the proof was already known; this PR is the formal translation."
5. After a failed attempt, we write a `fail-...` memo.
6. Phase 2 (*solving with new proofs* — genuine new mathematics)
   only begins after at least one merged Phase 1 PR has shown the
   workflow scales. PR descriptions, commit messages, and memos
   must never claim Phase 2 originality for Phase 1 work.

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

## Reminders

- The `formal-conjectures` repo's contribution channel is the leanprover
  Zulip `#Formal-conjectures` and GitHub issues / PRs. Coordinate with
  the user before opening PRs; do not auto-publish.
- Pushing to `git@github.com:mrmartin/claude_proving_new_mathematics.git`
  is fine when the user asks. Force-pushing or destructive `git` is not
  fine without explicit instruction, even on this repo.
- The user's email is `martin@martintech.co.uk` (commit-author info).
