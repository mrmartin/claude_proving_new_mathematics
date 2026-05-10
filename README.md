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

## Goals (a pipeline, not parallel work)

`formal-conjectures` exists to **formalise problems** — write the
Lean statement of a conjecture, ship it as `:= by sorry`. Their
spirit is the *statement corpus*. We do not contribute to that.
Our work is **orthogonal**, oriented at the *proof corpus*:

1. **Goal 1 — Catalogue.** Build and maintain a precise map of
   what's already formally proved in `formal-conjectures` —
   inline-proved, linked elsewhere via `@[formal_proof using …]`,
   naked sorry with a known informal proof, naked sorry with no
   proof anywhere. The catalogue lives in this repo
   (`catalogue/index.json` + a Markdown summary memo) and is the
   candidate pool for goals 2 and 3.
2. **Goal 2 — Formalise known proofs.** Take a naked sorry whose
   informal proof is already in the literature, and write the
   Lean version. Short proofs (≤ 25–50 lines) go inline upstream;
   long proofs go in `proofs/` here, with a one-line
   `@[formal_proof using lean4 at "<our-url>"]` annotation
   upstream. The cambie work was Goal-2 short.
3. **Goal 3 — Solve unsolved formalised problems.** A naked sorry
   whose proof exists *nowhere* — neither inline, nor linked, nor
   informally. Produce a formal proof. This is the apex goal;
   yield will be very low. An *interesting partial result*
   (counterexample, conditional proof, sharp special case) on a
   previously-unsettled formalised conjecture also counts.

### Off-limits

The whole "defining the problem in Lean" column is `formal-conjectures`'
job, not ours. We never close upstream issues like
[`#991` (formalise Erdős 869)](https://github.com/google-deepmind/formal-conjectures/issues/991)
that ask for a new statement. Erdős 869 is informally disproved
on [`erdosproblems.com/869`](https://www.erdosproblems.com/869) —
but the statement is not in the repo yet, so there is no sorry
for us to fill, so it is **not** a target. The diagnostic for
every candidate: *is the statement already formalised? if not,
ignore.*

### A taxonomy worth being precise about

|                          | **Defining (statement only)** | **Solving (filling a sorry)** |
| ------------------------ | ----------------------------- | ----------------------------- |
| **Known informal proof** | `formal-conjectures`' job — they own this column. | **Goal 2 here.** Translate a literature proof into Lean. |
| **No known proof**       | `formal-conjectures`' job too. | **Goal 3 here.** Proving an open conjecture. New mathematics. |

`CLAUDE.md` enforces these distinctions on every memo and PR.
We never describe Goal-2 work as "proving new mathematics."

### External resources

- **`https://www.erdosproblems.com/<N>`** — definitive lookup for
  any Erdős problem `N`. Erdős problems are ~50 % of the upstream
  corpus, so this is our highest-leverage external resource.
  Each page reports status (open / solved / disproved) and
  references; treat it as authoritative for "is this already
  shipped elsewhere?". File-name match is exact:
  `FormalConjectures/ErdosProblems/<N>.lean` ↔
  `erdosproblems.com/<N>`.
- **`https://oeis.org/A<NNN>`** — for `OeisA<NNN>` files.
- **`https://en.wikipedia.org/wiki/<conjecture>`** — for
  `Wikipedia/*.lean` files.
- **`https://mathoverflow.net/questions/<id>`** — for
  `Mathoverflow/<id>.lean` files.
- arXiv links cited by `Paper/` and `Arxiv/` files.
- mathlib via lean4-skills LSP search tools.
- `formal-conjectures` issue tracker (search by problem number).
- Upstream `Subsets/FC100SolvedSet1.lean` and
  `FC100OpenSet1.lean` benchmark slices.

When the catalogue (Goal 1) is built, every entry will carry a
`status_url` linking to the appropriate resource above so
targeting reduces to a table query.

We are **not** chasing low-hanging fruit (pure `decide` testcases,
restatement PRs, *defining* PRs that add new sorries) or
Fields-medal headlines (Goldbach, Riemann, Beal, Apéry,
Mihailescu).

## Memory index

| #    | Kind   | Title                                                                | Status     |
| ---- | ------ | -------------------------------------------------------------------- | ---------- |
| 0001 | setup  | [Lean 4 + mathlib bootstrap and 1+1=2](memory/0001-setup-lean4-mathlib-bootstrap-1plus1.md) | shipped    |
| 0002 | survey | [`formal-conjectures` repo: structure, conventions, attack vectors](memory/0002-survey-formal-conjectures-repo.md) | shipped    |
| 0003 | target | [`Erdos399.erdos_399.variants.cambie` — Cambie's mod-8 obstruction](memory/0003-target-erdos-399-variants-cambie.md) | go         |
| 0004 | proof  | [`Erdos399.erdos_399.variants.cambie` — solving + known proof](memory/0004-proof-erdos-399-variants-cambie.md) | shipped (local) |
| 0005 | infra  | [Erdős-Problems scraper (Stage A, slice 1)](memory/0005-infra-erdosproblems-scraper.md) | shipped     |
| 0006 | infra  | [Lean-side Erdős catalogue (Stage A, slice 2)](memory/0006-infra-lean-side-erdos-catalogue.md) | shipped     |
| 0007 | proof  | [Erdős 38 — reproducing the spicylemonade/Aristotle proof locally](memory/0007-proof-erdos-38.md) | shipped (local) |

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
