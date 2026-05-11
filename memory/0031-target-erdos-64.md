# Erdős 64 (Erdős–Gyárfás) — target evaluation

**Kind:** target
**Status:** Goal-3 attack in progress (Track A ships verified partials, Track B
attempts solve, Track C fills mathlib gaps).
**Date:** 2026-05-11
**Related:** plan at `~/.claude/plans/zesty-launching-origami.md`, future memos
0032+.
**Upstream link:** `formal-conjectures/FormalConjectures/ErdosProblems/64.lean`

## Statement

> Does every finite graph with minimum degree ≥ 3 contain a cycle of length
> $2^k$ for some $k ≥ 2$?

Open. **FALSIFIABLE — $1000 prize** per `erdosproblems.com/64`.

## 2×2 cell

- **Defining vs solving:** solving — upstream statement already exists.
- **Known proof vs new:** **no known proof either way.** This is Goal 3
  (genuine open mathematics).
- **Sub-cases** (Track A) are Goal-2-style work technically (the informal
  proof exists), but per the `CLAUDE.md` HARD GATING RULE the parent is
  OPEN, so sub-case work ships as *Goal-3-adjacent partial results* with
  honest language: "Lean-verified partial result on Erdős 64", *not*
  "solving" anything.

## Coordination check (pre-stage)

1. **erdosproblems.com/64 forum thread:** one comment, by Alfaiz (06 Dec
   2025), listing known sub-cases — pure exposition, no Lean artifact.
   User "Chillguy" is marked as `working on this` but has posted no code
   or comment and has no public Lean repo I can find via the usual
   sources. No coordination conflict at present; if Chillguy publishes,
   we will reroute Track A accordingly.
2. **Upstream `git log -- ErdosProblems/64.lean`:** the file has only
   four commits, all bookkeeping (initial creation `cc48266`, namespace
   pass `5d6e8b9`, naming-convention update `cd70885`, `answer(sorry)`
   normalisation `a22f98a`). No proof attempt in upstream history.
3. **No PR open on formal-conjectures** mentioning Erdős 64 or
   "Gyárfás" at scan time.
4. **No Erdős 64 file** in `plby/lean-proofs` or `teorth/analysis`.
5. **Zulip `#Formal-conjectures`** search returned no matches for
   "Erdős 64" or "Gyárfás" at scan time.

## State of the art (informal mathematics)

- **Liu–Montgomery 2020 [LiMo20]:** proved Erdős 64 (and a much stronger
  cycle-spectrum statement) when min degree is sufficiently large; this
  disproved the Erdős–Gyárfás stronger conjecture that arbitrarily-high
  min-degree counterexamples exist. Out of reach for us
  (sublinear-bandwidth + probabilistic embedding machinery).
- **Sub-cases proven:**
  - (i) K_{1,m}-free with min-deg ≥ m+1 — Shauger 1998 [Sh98].
  - (ii) Planar claw-free — Daniel-Shauger 2001 [DaSh01].
  - (iii) 3-connected cubic planar — Heckman-Krakovski 2013 [HeKr13].
  - (iv) Several Cayley families — Ghaffari-Mostaghim, Ghasemi-Varmazyar.
  - (vi) P_8-free — Gao-Shan 2022 (`arXiv:2109.01277`).
  - (vii) P_{10}-free — Hu-Shen 2024 (`arXiv:2308.05675`).
  - (viii) Diameter-2 → C_4 or C_8 — Carr 2026 (`arXiv:2508.19302`,
    12 pages, 10 figures).
- **Counter-search bounds:**
  - Cubic counterexample ≥ 30 vertices — Markstrom 2004
    (`abel.math.umu.se/~klasm/Uppsatser/cycex.pdf`).
  - Bipartite counterexample ≥ 32 vertices — Nowbandegani-Esfandiari
    2011 [NoEs11].
  - Cubic claw-free counterexample ≥ 114 vertices, and *every*
    claw-free min-deg-3 has a $2^k$ or $3·2^k$ cycle — Nowbandegani et
    al. 2014 (`arXiv:1109.5398`).

## Three-track plan (full detail in `~/.claude/plans/zesty-launching-origami.md`)

- **Track A — Verified partial-result ship.** A1 reformulation + warm-ups,
  A2 bipartite cubic girth ≤ 8, A3 diameter-2 (Carr 2026), A4
  Pikhurko-style small named cubic graphs.
- **Track B — Original solve attempts.** B1 SAT-encoded counterexample
  search on cubic graphs n=30..60 (offline nauty + CaDiCaL/Kissat); B2
  bipartite cubic via Moore bound + small-girth catalogue; B3 girth-
  pigeonhole / BFS-layer counting (time-boxed 2-week spike). B4/B5
  deferred.
- **Track C — Mathlib gap-fill.** C1 `girth ≤ 2 · diam + 1` (the TODO at
  mathlib's `Girth.lean:19`); C2 small girth equivalences; C3
  `Decidable (∃ c, c.IsCycle ∧ c.length = k)` for fixed `k ≤ 16`.

## Stop / pivot conditions

- If Chillguy or another formaliser publishes overlapping work, reroute
  Track A to a non-overlapping sub-case.
- If B1 SAT runs find a candidate counterexample, **quadruple-check by
  hand** before any memo language stronger than "candidate, verification
  in progress".
- If B3 has no observable progress after 2 weeks, kill it via
  `fail-NNNN-erdos64-girth-pigeonhole.md`.
- If any Track-A milestone exceeds its line budget by >50 %, narrow the
  hypothesis (e.g. `minDegree ≥ 4` instead of `minDegree ≥ 3`) and memo
  the harder version as a fail.

## Honest-language reminder

- **No commit, memo, or PR** may use the phrase "solved Erdős 64",
  "proved Erdős 64", or "disproved Erdős 64" unless a complete proof or
  verified counterexample is in hand and quadruple-checked.
- Permitted phrasing: *"Lean-verified partial result on Erdős 64"*,
  *"Lean translation of [Author] [year]'s [class] sub-case"*,
  *"extension of Markstrom 2004's bound on cubic counterexamples"*.

## Next

Commit 1 (this memo + `proofs/erdos64/Erdos64/Basic.lean` + infra memo
0032). Commit 2 is `WarmUp.lean`. Commit 3 is `GirthDiam.lean`.
