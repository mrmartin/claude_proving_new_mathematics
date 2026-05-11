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
| 0008 | proof  | [Erdős 38 — bridge from `erdos_problem_38` to upstream `erdos_38` signature](memory/0008-bridge-erdos-38.md) | shipped (local) |
| 0009 | target | [Erdős 397 — Wu/Aristotle disproof of "finitely many central-binomial collisions"](memory/0009-target-erdos-397.md) | go |
| 0010 | proof  | [Erdős 397 — bridge from gist `infinite_solutions` to upstream `erdos_397` signature](memory/0010-bridge-erdos-397.md) | shipped (local) |
| 0011 | target | [Erdős 457 — Barreto/Aristotle's prime-divisor density result; minimal bridge needed](memory/0011-target-erdos-457.md) | go |
| 0012 | proof  | [Erdős 457 — bridge from gist `erdos_457` to upstream `erdos_457` signature](memory/0012-bridge-erdos-457.md) | shipped (local) |
| 0013 | infra  | [Bridge pipeline tracking — all (LEAN)+formalised Erdős candidates](memory/0013-infra-bridge-pipeline-tracking.md) | in-progress |
| 0014 | proof  | [Erdős 198 — bridge for plby/Alexeev's AlphaProof Sidon-set construction](memory/0014-bridge-erdos-198.md) | shipped (local) |
| 0015 | proof  | [Erdős 645 — bridge for plby/Alexeev's Brown-Landman 3-AP-with-large-gap](memory/0015-bridge-erdos-645.md) | shipped (local) |
| 0016 | proof  | [Erdős 370 — bridge for plby/Alexeev's `(k!+3)²-1` max-prime-factor construction](memory/0016-bridge-erdos-370.md) | shipped (local) |
| 0017 | proof  | [Erdős 1043 — bridge for Pommerenke's monic-polynomial level-set counterexample](memory/0017-bridge-erdos-1043.md) | shipped (local) |
| 0018 | proof  | [Erdős 259 — bridge for ster-oc's Chen-Ruzsa irrational Möbius series](memory/0018-bridge-erdos-259.md) | shipped (local) |
| 0019 | proof  | [Erdős 1051 — bridge for van Doorn–Tao series irrationality (ℕ→ℤ container)](memory/0019-bridge-erdos-1051.md) | shipped (local) |
| 0020 | proof  | [Erdős 1054 — `f_undefined_at_2`: Lean encoding sanity check, NOT a solution to the problem](memory/0020-proof-erdos-1054-f2.md) | shipped (local, but not substantive) |
| 0021 | proof  | [Erdős 399 `.sum_two_squares`: characterises all `n ≤ 6` solutions; `n ≥ 7` blocked by missing Bertrand-in-AP](memory/0021-proof-erdos-399-sum-two-squares-partial.md) | partial (n ≤ 6 shipped) |
| 0022 | fail   | [Erdős 1113 `.infinitely_many_sierpinski`: misclassified — parent problem is OPEN on erdosproblems.com](memory/0022-fail-erdos-1113-misclassified-open-parent.md) | abandoned (off-target) |
| 0023 | target | [Erdős 1148 `.variants.weaker` — `n = x²+y²-z²` with slack `2√n`](memory/0023-target-erdos-1148-weaker.md) | go |
| 0024 | proof  | [Erdős 1148 `.variants.weaker` — Goal-2 four-case construction](memory/0024-proof-erdos-1148-weaker.md) | shipped (local) |
| 0025 | target | [Erdős 613 (parent, disproved) — Tao's n=5 Pikhurko counterexample](memory/0025-target-erdos-613.md) | go |
| 0026 | proof  | [Erdős 613 — bridge for Tao's `PikhurkoN5.red_triangle_of_no_blue_star`](memory/0026-proof-erdos-613-bridge.md) | shipped (local) |
| 0027 | target | [Erdős 499 (parent, SOLVED) — Marcus-Minc 1962 via plby/Aristotle](memory/0027-target-erdos-499.md) | go |
| 0028 | proof  | [Erdős 499 — bridge for plby/Aristotle's Marcus-Minc proof](memory/0028-proof-erdos-499-bridge.md) | shipped (local) |
| 0029 | target | [Erdős 26 `.variants.rusza` — Ruzsa's counterexample via plby/Aristotle](memory/0029-target-erdos-26-rusza.md) | go |
| 0030 | proof  | [Erdős 26 `.variants.rusza` — bridge for plby/Aristotle's Ruzsa proof](memory/0030-proof-erdos-26-rusza-bridge.md) | shipped (local) |
| 0031 | target | [Erdős 64 (Erdős–Gyárfás, OPEN, $1000) — three-track attack plan](memory/0031-target-erdos-64.md) | in-progress |
| 0032 | infra  | [Erdős 64 project skeleton + `Basic.lean`](memory/0032-infra-erdos64-skeleton.md) | shipped (local) |
| 0033 | proof  | [Erdős 64 `WarmUp.lean`: K₄, K₃,₃, 3-prism each have a 4-cycle](memory/0033-proof-erdos64-warmup.md) | shipped (local) |
| 0034 | proof  | [Erdős 64 `Bipartite.lean`: bipartite graphs have no odd cycle](memory/0034-proof-erdos64-bipartite-no-odd-cycle.md) | shipped (local) |
| 0035 | idea   | [Erdős 64 — `girth ≤ 2·diam+1` deferred (needs closed-walk → cycle helper)](memory/0035-idea-erdos64-girth-diam-deferred.md) | deferred |
| 0036 | proof  | [Erdős 64 `BipartiteCubic.lean`: bipartite girth ∈ {4, 8} cases](memory/0036-proof-erdos64-bipartite-cubic-partial.md) | shipped (local, partial) |
| 0037 | target | [Erdős 64 A3 — diameter-2 (Carr 2026): setup + statement, body deferred](memory/0037-target-erdos64-diam-two.md) | partial (statement + helper) |
| 0038 | proof  | [Erdős 64 A4 — `Markstrom.lean`: Petersen graph verified](memory/0038-proof-erdos64-petersen.md) | shipped (local) |
| 0039 | infra  | [Erdős 64 B1 — `Search/check_cubic.py`: 11 named cubic graphs pass](memory/0039-infra-erdos64-search-b1.md) | shipped (B1.0; full pipeline needs nauty/SAT) |
| 0040 | result | [Erdős 64 B1 — exhaustive `n ≤ 18` (all 45 974 connected cubic graphs pass)](memory/0040-result-erdos64-b1-up-to-n18.md) | shipped (local) |

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
