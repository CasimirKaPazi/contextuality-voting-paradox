# Impossibility, Self-Reference and Collective Choice

Work in progress on a common description of the impossibility results of social choice (Arrow, Gibbard–Satterthwaite, Young–Levenglick and others), the paradoxes of self-reference (the Liar, Gödel, the halting problem, Lawvere's fixed-point theorem) and contextuality.

The guiding observation is that all of these have the same form: local pieces that each make sense do not fit into a consistent whole, and every attempt to force a fit either produces a contradiction, imposes an arbitrary choice, or introduces chance.

**Status.** Everything here is a draft. Notes are revised as the picture becomes clearer; papers that reach a stable form will be moved to `papers/` and then left unchanged. Claims are marked throughout as cited theorems, results proved in the text, results checked by computation on small cases, or interpretation.

## Where to start

- [`notes/roadmap.md`](notes/roadmap.md) — overview of all threads, what is in hand and what is missing.
- [`notes/map-of-voting-paradoxes.md`](notes/map-of-voting-paradoxes.md) — the known voting paradoxes, grouped by what is varied, with the theorems that connect them. Includes the elementary argument that no Condorcet extension is consistent, and that the obstruction is the majority cycle itself acting on the possible ways of breaking it.
- [`notes/where-the-symmetry-goes.md`](notes/where-the-symmetry-goes.md) — aggregation into a ranking must dispose of a symmetry; it ends up in the output (a paradox), in the rule (a dictator or tie-breaker), or in a fixed point (a lottery). Includes a table sorting known results by placement.

## Contents

### Notes (`notes/`)

| File | Content |
|---|---|
| `roadmap.md` | Threads, status, suggested order |
| `map-of-voting-paradoxes.md` | Families of paradoxes, links between them, consistency as convexity and as a gluing condition |
| `consistency-as-extension.md` | Consistency as convexity; the Condorcet winner as a partial assignment that cannot be extended consistently across the cycle region; symmetry, gluing and cycle sensitivity, deterministic versus lotteries (maximal lotteries) |
| `contextuality-and-symmetry.md` | Aggregation as a constraint network in which independence of irrelevant alternatives is non-contextuality; dictators as integral solutions, random dictatorship as the symmetric fractional one; random rules as empirical models, with mixtures of dictatorships as the non-contextual ones and a contextual coin rule; agreement-type versus symmetry-breaking obstructions, as in distributed computing; the linear-programming bridge between keeping symmetry and gluing |
| `where-the-symmetry-goes.md` | Three placements of the symmetry, composed voters, agreeing for different reasons |
| `two-kinds-of-loop.md` | Condorcet cycles (integer winding) versus the Liar (parity), the Klein bottle seam, strategy and computability |
| `ladder-of-lost-properties.md` | Speculative: the normed division algebras and Hopf fibrations as a frame for successive breakdowns of aggregation |

### Paper drafts (`papers/drafts/`)

| File | Content |
|---|---|
| `cycles-twists-walls.md` | *Cycles, Twists and Walls.* Value spaces and the winding number; non-orientability at the seam; walls in profile space; Gibbard's theorems combined with a diagonal argument (every non-dictatorial game form with at least three outcomes leaves some voter without a computable best reply); randomisation and its price |

### Scripts (`scripts/`)

All scripts are short and self-contained. They need Python 3 with `numpy`; some also need `scipy` or `matplotlib`. Run them from their own directory, for example `cd scripts/consistency && python3 convexity_check.py`.

| Script | What it checks | Used in |
|---|---|---|
| `topology/condorcet_gluing.py` | The six ways of gluing the two Condorcet cycles of the three-alternative annulus: three give a torus, three a Klein bottle; global reversal alone gives a torus | *Two Kinds of Loop*, *Cycles, Twists and Walls* §5 |
| `topology/seam_check.py` | In every Klein bottle gluing, orientation flips at every seam edge; in every torus gluing, at none | *Cycles, Twists and Walls*, Proposition 5 |
| `contextuality/condorcet_contextuality.py` | A Condorcet cycle has no valid model on a finite line, is consistent on a circle, and is strongly contextual only on an unbounded line; a choice-based encoding cannot tell cycles from orders | *Cycles, Twists and Walls* §3 |
| `strategy/rational_diagonal.py` | The diagonal argument with opponents rational in the actual play, for plurality, Borda, instant runoff and Black's rule (two and three voters). Takes some minutes | Proposition 9 |
| `strategy/rational_diagonal_controls.py` | Controls (dictatorial and two-outcome rules give no cases) and a worked Borda example | Proposition 9 |
| `strategy/rational_diagonal_gameforms.py` | All 18,138 non-dictatorial two-player game forms with three strategies and three outcomes. Takes some minutes | Proposition 9 |
| `strategy/sequential_veto.py` | Veto-then-pick procedure: the diagonal survives Nash-style rationality but not sequential rationality | *Cycles, Twists and Walls* §7 |
| `consistency/convexity_check.py` | Winner regions in the simplex of vote shares: Borda and plurality are convex (consistent); Condorcet methods fail only at profiles with a cycle; instant runoff fails also without cycles | *Map*, gluing as convexity |
| `consistency/blocking_any_n.py` | The explicit blocking construction for three to six candidates: at every profile without a Condorcet winner, any choice of winner is undone by a mixture | *Map*, Young–Levenglick for any number of candidates |
| `consistency/participation_check.py` | Participation along ballot segments in vote-share space for maximin, Black and Borda with three and four candidates; maximin fails only from four candidates on. Takes about a minute | *Map*, no-show mechanism |
| `consistency/cycle_assignment_check.py` | No profile with a majority cycle can be assigned to any candidate by a consistent Condorcet extension | *Map*, Young–Levenglick for three candidates |
| `symmetry/isotropy_check.py` | Stabilisers of all anonymous profiles for small numbers of alternatives and voters; the condition "every stabiliser fixes an admissible output" reproduces the existence conditions for anonymous, neutral rules with single winners, Pareto-optimal winners and rankings. Takes about twenty seconds | *Where the Symmetry Goes* §7 |
| `symmetry/arrow_as_csp.py` | Arrow's problem for three alternatives as a constraint network: the unanimous solutions independent of irrelevant alternatives are exactly the dictators (two and three voters), none is anonymous, and the share assignment is a consistent fractional solution equal to random dictatorship | *Contextuality and Symmetry* §2 |
| `symmetry/probabilistic_arrow.py` | Random rules with probabilistic independence of irrelevant alternatives: with two voters every rule is a mixture of dictatorships in its marginals; from three voters on, the coin rule (unanimity, otherwise ½ per pair) is anonymous, Paretian and not such a mixture, hence contextual; it exists for three to five alternatives and fails for some profiles with six. Takes about a minute and a half | *Contextuality and Symmetry* §2a |
| `exploratory/condorcet_island.py` | Interactive: where a third candidate produces a cycle in a spatial model, as a function of zoom and voter arrangement | exploratory |
| `exploratory/island_phase_map.py` | Area and direction of the cycle region over the parameters of the spatial model | exploratory |

### Formal proofs (`lean/`)

Small Lean 4 files that check finite and abstract statements from the notes. They use only core Lean, without Mathlib, and are checked with `lean <file>`; most proofs are by computation (`decide`).

| File | What it proves | Used in |
|---|---|---|
| `Diagonal.lean` | Lemma 7 in abstract form: without a dominant ballot, no strategist is universally correct against opponents that can run it. The only computational assumption is that the opponents can apply any map to the strategist's output | *Cycles, Twists and Walls* §7 |
| `Condorcet.lean` | The Condorcet profile has a majority cycle and no Condorcet winner; each of the 216 profiles of three voters on three alternatives has a Condorcet winner or a full cycle; exactly 12 have a cycle | background to *Cycles, Twists and Walls* §3 |
| `Nerve.lean` | The complex of strict orders on three alternatives is an annulus bounded by the two cycles; of the six gluings of its boundary circles, the three along the reference orientations are non-orientable and the other three orientable; filling in both cycles gives a closed orientable surface of Euler characteristic 2, on which reversing every preference is a free, orientation-reversing symmetry; identifying only the two cycle faces gives no surface | *Cycles, Twists and Walls* §5 |

What the files leave to standard topology: that a coherent orientation of the triangles is the same as orientability, and the classification of surfaces, which names the resulting surfaces (torus, Klein bottle, sphere, projective plane).

## Related work

The notes build on, among others: Livson, Prokopenko and Pritam on Arrow and Gödel and on the non-orientable topology of Condorcet's paradox; Abramsky and co-authors on contextuality and on Arrow's theorem in categorical form; Gibbard (1973, 1977, 1978); Young and Levenglick; Moulin; Saari's geometry of voting; Jiang, Lim, Yao and Ye on combinatorial Hodge theory and ranking; McKelvey on intransitivity in spatial voting; Binmore, Anderlini, and Nachbar and Zame on non-computable strategies; Baryshnikov and Root, and Rajsbaum and Raventós-Pujol, on topological proofs of the Gibbard–Satterthwaite and Arrow theorems. Full references are given in each document. References marked † in the notes were cited from memory and have not yet been checked against the originals.

## Authors

Hiveism and Claude (Anthropic).

The work was developed in conversation: questions, ideas and direction from Hiveism; literature search, proofs, computations and drafting largely by Claude. Both are responsible for errors.

## License

All content in this repository — text and code — is licensed under the [Creative Commons Attribution-ShareAlike 4.0 International License](https://creativecommons.org/licenses/by-sa/4.0/) (CC BY-SA 4.0). See [`LICENSE`](LICENSE).

Suggested citation: Hiveism and Claude, *Impossibility, Self-Reference and Collective Choice* (work in progress), 2026.
