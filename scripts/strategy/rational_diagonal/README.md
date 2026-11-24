# Rational diagonal: searches and tests

Scripts behind the open problem on tight game forms in *Walls and Strategy*
(Proposition 5 and open problem 1). Plain Python 3, no dependencies. Run from
this folder, since the scripts import `diag2.py` and `recipes_core.py`.

Convention: a two-player game form is a tuple of outcomes in row-major order,
rows for player 1, columns for player 2. Preferences are strict rankings.

## Core

- `diag2.py` — the fast test. For a player i and a ranking P, call a cell
  *refuted* if another strategy of i does better against that column. An
  opponent ranking Q exists iff an order can be built greedily so that in every
  row the opponent's favourite outcome sits in a refuted cell. Also
  `works_brute` (all P and Q) and `dictator`.
- `recipes_core.py` — `works_PQ(R, P, Q)`: does a fixed pair (P, Q) give a
  rational diagonal for the player whose strategies are the rows of `R`.
- `check33.py` — validates the fast test against brute force on 3 × 3 forms.
- `diagn.py` — brute force for any number of players (the opponents' replies
  must form an equilibrium among themselves). `python3 diagn.py 2x2x3 3`.

## Exhaustive scans

- `scan.py m1 m2 k` — all m1 × m2 forms with exactly k outcomes (first cell
  fixed to `a` to remove relabelling). Results so far: no failure for 3 × 3, 3 × 4,
  3 × 5, 4 × 4 with three outcomes, 3 × 3 and 3 × 4 with four.
- `injtight.py m1 m2 k` — tight forms with no outcome repeated in any row or
  column (none exist up to 3 × 4); such a form would be a counterexample.

## Recipes and tightness

- `revscan.py`, `recipe2.py` — whether Q = reverse(P), or P with its top moved
  to the bottom, suffices.
- `tight.py`, `tight2.py` — restrict to tight forms; tight2 tests the shape
  "i ranks first an outcome x it cannot force, the opponent ranks x last".
- `rule.py`, `rule2.py`, `Kgen.py` — which choices of player and outcome work;
  Kgen shows that "every outcome i cannot force works" is false for general
  tight forms.

## Totally tight forms

- `tt.py` — totally tight forms (every 2 × 2 subform has a constant line) and a
  candidate induction invariant (fails, e.g. on `aaa / aab / ccc`).
- `core.py`, `canon.py` — forms with a non-empty irreducible core
  (Boros–Gurvich–Makino–Papp): the diagonal with i's top x not forcible by i and
  the opponent's bottom x, core outcomes in a cyclic order, holds in all cases
  checked; canon tests fixed canonical choices of the opponent's order.
- `semidict.py`, `semirule.py`, `semirule2.py` — totally reducible forms as
  stopping games: lines with times and outcomes, cell = outcome of the earlier
  line. Random tests (no failure) and attempts at a rule for the player.

## Structured and random families

- `randtight.py m1 m2 k seed seconds` — random tight forms (no failure in
  about 430,000 forms up to 5 × 5).
- `veto.py seed` — two-player veto voting forms, tight when total veto
  resistance minus total veto cards is 1 (no failure).
- `trees.py seed count maxcells` — normal forms of random perfect-information
  game trees (no failure in 8,568 forms).

## A tight form without a rational diagonal

Note *A tight form without a rational diagonal*.

- `tight_counterexample.py` — the 6 × 6 form with three outcomes: tightness,
  non-dictatorship, the table of strict Nash strategies for every pair of strict
  preferences and both players, minimality under deleting lines, and the
  isomorphism with its transpose.
- `border_scan.cpp n m [from to]` — all n × m inner forms inside a c-row and a
  c-column (such forms are always tight), tested for a rational diagonal.
- `three_outcomes_veto.py [seed]` — three outcomes: without a common veto some
  player works (Theorem A); with one, the exact criterion (Theorem B); both
  against the brute-force test.
- `local_search.cpp n m seed restarts flags k` — local search for tight forms
  without a rational diagonal, with k outcomes.

## Survival of a working configuration (`absorption/`)

Towards a hand proof for totally tight forms (note *The rational diagonal on
totally tight game forms*, Sections 7 and 8). Run from `absorption/`; `sg.py` imports
`recipes_core.py` from the parent folder. `python3 collect.py k N` first, then
the analyses with the same `k N`. `tr_absorb.cpp` checks on all reachable
summaries that a line with a present outcome keeps a working configuration
exactly when the new form is valid. `base_rule.py` checks the two base cases
proved in the note. `positions.py` (stopping games) and `tr_positions.cpp` (all
reachable summaries) check the position lemma: some working configuration that
survives can be recognised by where the line's outcome sits in its orders.
The `k3_*.py` scripts belong to the hand proof for three outcomes: the
properties behind the working conditions, the search for the implications
used in the proof, and a check of the chain lemma (`k3_chain.py`). The chain
conjecture for more outcomes is checked by `chain_k.py` (random forms) and
`tr_chain.cpp` (all reachable summaries); `k4_chainsearch.py` found it.
