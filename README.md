# claude_proving_new_mathematics

A working journal of Claude Code (Opus, with the
[`lean4-skills`](https://github.com/cameronfreer/lean4-skills) plugin)
attempting to contribute Lean 4 theorem-proving work to
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures),
and — eventually — to prove new mathematics.

The substantive content lives in `memory/`. Each file there is one piece of
work: a setup step, a survey of a repo or topic, an evaluation of a target
theorem, a proof attempt (successful or not), an infrastructure note, or an
idea worth keeping. The table below is the navigation surface; **update it
whenever you add or change a memo**.

`CLAUDE.md` (auto-loaded by Claude Code in this directory) is the briefing
for new conversations: goals, process, rules, the strategy we've committed
to. Read it first if you are picking this project up cold.

## Goals

1. **Phase 1 — formalize known proofs.** Convert `:= by sorry` placeholders
   in `formal-conjectures` into short Lean proofs (≤ 25–50 lines) when the
   informal proof already exists in the literature.
2. **Phase 2 — new mathematics.** Once Phase 1 is producing merged PRs,
   attack genuinely open problems where Claude's mathlib search and tactic
   enumeration give us a real shot.

We are not chasing low-hanging fruit (pure `decide` testcases, restatement
PRs) or Fields-medal headlines (Goldbach, Riemann, Beal, Apéry, Mihailescu).

## Memory index

| #    | Kind   | Title                                                                | Status     |
| ---- | ------ | -------------------------------------------------------------------- | ---------- |
| 0001 | setup  | [Lean 4 + mathlib bootstrap and 1+1=2](memory/0001-setup-lean4-mathlib-bootstrap-1plus1.md) | shipped    |
| 0002 | survey | [`formal-conjectures` repo: structure, conventions, attack vectors](memory/0002-survey-formal-conjectures-repo.md) | shipped    |

## Local layout

```
.
├── CLAUDE.md                    # auto-loaded briefing for every session
├── README.md                    # this file (memo index)
├── .gitignore
├── memory/
│   └── NNNN-<kind>-<short-topic>.md
└── MyProject/                   # smoke-test Lean project (1+1=2 etc.)
```

`formal-conjectures/` is expected as a sibling clone but is *not* committed
here (it is upstream code). To set it up locally:

```bash
git clone https://github.com/google-deepmind/formal-conjectures.git
cd formal-conjectures && lake exe cache get
```

## Conventions in brief

- Memo filenames: `NNNN-<kind>-<short-topic>.md`. `NNNN` is monotonic and
  never reused. `<kind>` ∈ {setup, survey, target, attempt, proof, fail,
  infra, idea}. `<short-topic>` is descriptive enough to read alone.
- Memo body: see the template in `CLAUDE.md` (`## Memory discipline`).
- Commits: follow upstream rules where they apply. Never `git add -A`;
  stage files explicitly. Push to
  `git@github.com:mrmartin/claude_proving_new_mathematics.git` only when
  the user asks.

## Toolchain

- Lean 4 + Lake via `elan`.
- `lean4-skills` plugin (slash commands `/lean4:learn`, `/lean4:prove`,
  `/lean4:autoprove`, `/lean4:review`, `/lean4:refactor`, `/lean4:golf`,
  `/lean4:doctor`, etc.).
- `lean4-contribute` plugin for drafting bug reports / feature requests
  / shareable insights about `lean4-skills` itself.
