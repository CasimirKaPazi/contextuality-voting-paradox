# The rational diagonal on totally tight game forms

*Working note on open problem 1 of* Walls and Strategy *(rational diagonal on tight forms). It settles the totally tight forms with at most four outcomes by a complete computer check, and records the method, the evidence beyond four outcomes, and what remains open. Scripts: `scripts/strategy/rational_diagonal/`.*

## 1. The question and the condition

A two-player game form has rows (player 1's strategies), columns (player 2's) and an outcome in each cell. Fix a player i, a strict ranking P of the outcomes for i and a strict ranking Q for the opponent. Read i's strategies as rows. Player i *works* under (P, Q) if every row of i is refuted: among the opponent's best replies to that row (the cells holding the opponent's favourite outcome y in the row) there is one whose column contains an outcome i prefers to y. Then no strategy of i is a strict Nash strategy, which is the rational diagonal. On tight forms every pair of preferences has an equilibrium, so refutation works only through repeated outcomes: the opponent is indifferent among the cells holding y, and one of them must push i away.

**Theorem (computer-checked).** Every non-dictatorial totally tight two-player game form with three or four outcomes admits a rational diagonal with strict preferences. Moreover some player i works under some P with Q equal either to the reverse of P or to P with its top moved to the bottom. In both cases i's favourite outcome is the opponent's least favourite.

Totally tight forms are those whose 2 × 2 subforms are all tight. They include the normal forms of stopping games (games on a path in which the player to move may stop with that node's outcome) but not all games of perfect information.

## 2. Structure of totally tight forms

A *constant line* is a row or column holding a single outcome. Boros, Gurvich, Makino and Papp show that deleting constant lines repeatedly reduces a totally tight form either to a single cell (the form is *totally reducible*; these are exactly the stopping games) or to a non-empty irreducible core. Read backwards, every totally tight form is a core or a single cell with constant lines added one at a time. Each added line gives one player a new strategy that forces one outcome.

Every core has the same effectivity function, the 2-majority on three outcomes a₁, a₂, a₃: each player forces any two of them and no single outcome. Cores may contain further outcomes that neither player can force. The journal version (Discrete Mathematics 310 (2010), Fig. 13, Approximation III) describes cores block by block. Rows and columns fall into eight classes:
- three pair classes, whose lines hold exactly one pair of a₁, a₂, a₃ and are always present;
- four classes whose lines hold all three;
- one class whose lines also hold an outcome nobody can force.

The table gives, for each pair of a row class and a column class, the outcomes the cells may take: most blocks are constant, a few are two-valued "staircases", and the block where the last two classes meet is recursive. The complete case analysis behind this table is referred by the authors to their earlier preprint.

## 3. The method: a finite summary

Fix i, P and Q. For each row of i record the pair (y, M):
- y is the opponent's favourite outcome in the row;
- M is the best outcome, for i, among the columns in which y occurs.

Each column contains y, so M is at least as good as y, and the row is refuted exactly when M is strictly better. Whether i works depends only on the set of these pairs.

**Lemma (update rule).** Adding a constant line changes the set of pairs without reference to the rest of the matrix:
- a new row of i with constant outcome o: every M becomes the better of M and o; the new row contributes (o, best present outcome including o);
- a new column of the opponent with constant outcome o: every row whose y the opponent ranks below o becomes (o, o); the other rows are unchanged.

*Proof.* A new row of i raises every column's best entry to at least o, and the new row is constant. A new column puts o into every row; it becomes the opponent's favourite exactly where it beats y, and in that column the only outcome is o. ∎

With k outcomes the possible summaries, taken jointly over all choices of i, P and Q, form a finite set. A breadth-first search over the summaries reachable from the starting forms by adding lines therefore covers every form of the class at once, of any size. Validity (non-dictatorial, at least three outcomes) is tracked alongside, through the sets of outcomes each player forces.

**Monotonicity.** The update rule acts on each pair separately, so a summary that contains more pairs stays a superset after any sequence of lines, and a superset makes refutation harder. A pessimistic starting summary therefore covers every form whose summary it contains.

## 4. Results

**Stopping games (start: a single cell).** For three outcomes the search ends after 12 lines with 292 summaries up to renaming outcomes; for four, after 20 lines with 475,978. Every valid summary has a working (i, P, Q) of the two kinds in the theorem. The two kinds are both needed: each alone fails on some stopping games with three outcomes.

**Cores (start: the cores).** By the table of Section 2, a core row's pair (y, M) depends only on its class and on which outcomes its cells take in each block, and pair columns hold exactly their pair. For each pattern of present classes, the union of everything a row of those classes can contribute gives a pessimistic starting summary; blocks that might hold the extra outcome are allowed to hold it, which only adds pessimism. Three outcomes: 24 starting summaries up to renaming, none leading to a valid summary without a working pair. Four outcomes (one outcome nobody can force, or a core on three outcomes with the fourth added by lines): 311 starting summaries, 615,119 valid reachable summaries, none without a working pair.

Together these give the theorem.

## 5. Checks

- The update rule was compared with direct matrix computation on about 30,000 random totally reducible forms with three and four outcomes, with no mismatch.
- Every enumerated core is covered, bit for bit after renaming, by a pessimistic starting summary: all 344,508 cores with three outcomes up to 5 × 5 and the 3,072 cores with an extra outcome up to 4 × 5. (Searching directly from these cores, up to 5 × 5 and with lines added, also finds no failure.)
- The search stores 128-bit hashes of visited summaries; a collision could in principle skip a summary.

## 6. Beyond four outcomes, and what remains open

- With five and six outcomes, random stopping games (3,000 and 600) always had a working pair of the two kinds. The summary search does not scale to five outcomes.
- No simple rule for choosing i was found. The owner of the first node, the player who forces more outcomes and the outcome that appears last each work in most stopping games but not in all. A hand proof would need to explain why the two kinds of opponent order together always suffice.
- Tight forms that are not totally tight remain open. They include the normal forms of general games of perfect information and veto procedures. Exhaustive and random searches over tight forms have found no counterexample (see *Walls and Strategy*, Section 3).

*Reading.* On a core, the three key outcomes are forced in pairs by both players and singly by neither: the loop of refutation is present locally, as in a rock–paper–scissors. On a stopping game it is built step by step in time, one constant line per node. The theorem says both ways of building the loop always leave a player without a strict Nash strategy. *(Interpretation.)*

## 7. Scripts

In `scripts/strategy/rational_diagonal/` (they import `diag2.py` and `recipes_core.py` from the same folder):
- `tr_automaton.py`: the summary search in Python, with the update rule documented;
- `tr_auto.cpp`: the same search in C++, reduced by renaming outcomes; `./tr_auto k zsrot [file]` runs it with the two kinds of opponent order, from a single cell or from starting summaries in a file;
- `tr_validate.py`: comparison of the update rule with matrix computation;
- `tr_random.py`: random stopping games with five and six outcomes;
- `core_struct.py`, `core_struct4.py`: pessimistic core summaries from the table, for three and four outcomes;
- `core_enum.py`, `core_summ.py`, `core_profiles.py`, `core_struct_check.py`, `core_struct_check4.py`: enumeration of cores, their summaries, and the coverage checks.

## References

- Boros, E., Gurvich, V., Makino, K. and Papp, D. (2010). Acyclic, or totally tight, two-person game forms: characterization and main properties. *Discrete Mathematics* 310, 1135–1151. (Preprint: DIMACS Technical Report 2008-10.)
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Edmonds, J. and Fulkerson, D. R. (1970). Bottleneck extrema. *Journal of Combinatorial Theory* 8, 299–306.
- Gurvich, V. (1975). Solution of positional games in pure strategies. *USSR Computational Mathematics and Mathematical Physics* 15, 74–87.
- *Walls and Strategy* (draft, this repository).
