# Impossibility, Self-Reference and Collective Choice

Work in progress on a common description of the impossibility results of social choice (Arrow, Gibbard–Satterthwaite, Young–Levenglick and others), the paradoxes of self-reference (the Liar, Gödel, the halting problem, Lawvere's fixed-point theorem) and contextuality.

The guiding observation is that all of these have the same form: local pieces that each make sense do not fit into a consistent whole, and every attempt to force a fit either produces a contradiction, imposes an arbitrary choice, or introduces chance.

**Status.** Apart from the CORE paper, everything here is a draft. Notes are revised as the picture becomes clearer; papers that reach a stable form are moved to `papers/` and then left unchanged. Claims are marked throughout as cited theorems, results proved in the text, results checked by computation on small cases, or interpretation; proofs checked in Lean are marked as such.

## Where to start

- [`notes/roadmap.md`](notes/roadmap.md) — overview of all threads, what is in hand and what is missing.
- [`notes/map-of-voting-paradoxes.md`](notes/map-of-voting-paradoxes.md) — the known voting paradoxes, grouped by what is varied, with the theorems that connect them.
- [`notes/where-the-symmetry-goes.md`](notes/where-the-symmetry-goes.md) — aggregation into a ranking must dispose of a symmetry; it ends up in the output (a paradox), in the rule (a dictator or tie-breaker), or in a fixed point (a lottery).
- [`papers/CORE.md`](papers/CORE_13.md) — the application: a consensus procedure with a random fallback.
- [`notes/alignment-roadmap.md`](notes/alignment-roadmap.md) — an outlook on how this work can apply the the problem of AI alignment.

## How to help

Any help is appreciated.

### Lean

The main bottle neck currently is in formalizing the existing work in Lean. This for this you don't need to understand what is going on, just a few tokens to burn. Setting up Lean is easy, and AI can help you with that too. If the Lean proof does not work or gives any other new information, then this is also valuable. Just give notice before you start working on something and stay in the lean directory with the changes to reduce conflicts.

### Organizing

The scope of this project will make it hard to navigate as it grows. So some help with organization (like [here](https://github.com/mccorvie/riemann-masullo) would make it easier.

## Contents

### Paper (`papers/`)

*CORE: Consensus Or Random Exclusion* ([`CORE.md`](papers/CORE.md), typeset as [`CORE.pdf`](papers/CORE.pdf)). A procedure for groups that have to agree on a single course of action: the participants deliberate toward unanimous agreement, and at any time any of them may call for one participant, drawn uniformly and possibly the caller, to be removed. If removals continue, the procedure ends in random dictatorship, so that each participant's fallback is a fair lottery over the participants' ideals. The paper is complete and stays as it is; results that bear on it are collected in [`notes/core-connection.md`](notes/core-connection.md) for a follow-up, outlined in [`notes/core-follow-up-outline.md`](notes/core-follow-up-outline.md).

### Paper drafts (`papers/drafts/`)

| File | Content |
|---|---|
| `cycles-and-twists.md` | *Cycles and Twists.* Value spaces and the winding number; the Liar as the same loop over a different cover; non-orientability at the seam of the Klein bottle; the projective plane as the sphere divided by preference reversal |
| `walls-and-strategy.md` | *Walls and Strategy.* Walls in profile space and burial; Gibbard's theorems combined with a diagonal argument: every non-dictatorial game form with at least three outcomes has a voter for whom no program always computes a best reply; rational opponents; sequential moves; with lotteries, regress or ex ante inefficiency; consequence for a random fallback |
| `levels-of-obstruction.md` | *Four Levels of Obstruction in Social Choice.* Local inconsistency, contextuality, symmetry breaking, consistency; the three value spaces as the template; Young–Levenglick and the no-show theorem at the first level when read for joint draws of winners; Arrow's scenario at the third, moved to the second by dividing by the voters' permutations; exits by changing what counts as a value |

### Working notes (`notes/`)

Notes on the individual threads, revised as the work goes on. The index is [`notes/README.md`](notes/README.md).

### Scripts (`scripts/`)

Short computations that check statements on small cases, grouped by topic: Python, with a few C++ programs for the exhaustive searches. The index, with what each script checks and where it is used, is [`scripts/README.md`](scripts/README.md).

### Formal proofs (`lean/`)

Lean 4 files that check statements from the notes and the drafts, as one Lake project with Mathlib (`lake build` in `lean/`). The index is [`lean/README.md`](lean/README.md); proofs not yet formalised are listed in [`lean/roadmap.md`](lean/roadmap.md).

## Related work

The notes build on, among others: Livson, Prokopenko and Pritam on Arrow and Gödel and on the non-orientable topology of Condorcet's paradox; Abramsky and co-authors on contextuality and on Arrow's theorem in categorical form; Gibbard (1973, 1977, 1978); Young and Levenglick; Moulin; Saari's geometry of voting; Jiang, Lim, Yao and Ye on combinatorial Hodge theory and ranking; McKelvey on intransitivity in spatial voting; Binmore, Anderlini, and Nachbar and Zame on non-computable strategies, and Canning on which domains of games and opponents allow computable rational play; Baryshnikov and Root, and Rajsbaum and Raventós-Pujol, on topological proofs of the Gibbard–Satterthwaite and Arrow theorems. Full references are given in each document. References marked † in the notes were cited from memory and have not yet been checked against the originals.

## Authors

Hiveism and Claude (Anthropic).

The work was developed in conversation: questions, ideas and direction from Hiveism; literature search, proofs, computations and drafting largely by Claude. Both are responsible for errors.

## License

- **Code** — everything in `lean/` and `scripts/` — is licensed under the [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0), as Mathlib is. See [`LICENSE`](LICENSE).
- **Text** — everything else, including the papers and the working notes — is licensed under the [Creative Commons Attribution-ShareAlike 4.0 International License](https://creativecommons.org/licenses/by-sa/4.0/) (CC BY-SA 4.0). See [`LICENSE-CC-BY-SA`](LICENSE-CC-BY-SA).

Copyright 2026 Hiveism and Claude (Anthropic).

Suggested citation: Hiveism and Claude, *Impossibility, Self-Reference and Collective Choice* (work in progress), 2026.
