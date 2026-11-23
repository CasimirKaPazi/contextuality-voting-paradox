# The rational diagonal on totally tight game forms

*Working note on open problem 1 of* Walls and Strategy *(rational diagonal on tight forms). It settles the totally tight forms with at most four outcomes by a complete computer check, gives a hand proof for three outcomes, and records the method, the evidence beyond four outcomes, and what remains open. Scripts: `scripts/strategy/rational_diagonal/`.*

## 1. The question and the condition

A two-player game form has rows (player 1's strategies), columns (player 2's) and an outcome in each cell. Fix a player i, a strict ranking P of the outcomes for i and a strict ranking Q for the opponent. Read i's strategies as rows. Player i *works* under (P, Q) if every row of i is refuted: among the opponent's best replies to that row (the cells holding the opponent's favourite outcome y in the row) there is one whose column contains an outcome i prefers to y. Then no strategy of i is a strict Nash strategy, which is the rational diagonal. On tight forms every pair of preferences has an equilibrium, so refutation works only through repeated outcomes: the opponent is indifferent among the cells holding y, and one of them must push i away.

**Theorem (computer-checked; by hand for three outcomes, Section 7).** Every non-dictatorial totally tight two-player game form with three or four outcomes admits a rational diagonal with strict preferences. Moreover some player i works under some P with Q equal either to the reverse of P or to P with its top moved to the bottom. In both cases i's favourite outcome is the opponent's least favourite.

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
- No simple rule for choosing i was found. The owner of the first node, the player who forces more outcomes and the outcome that appears last each work in most stopping games but not in all. A hand proof would need to explain why the two kinds of opponent order together always suffice. For three outcomes Section 7 gives such a proof. It suggests a chain of four configurations for any number of outcomes, checked exhaustively for four and reduced to at most nine outcomes (end of Section 7). Section 8 proves the base cases of an induction and reduces the rest to one lemma about positions in the orders.
- Tight forms that are not totally tight remain open. They include the normal forms of general games of perfect information and veto procedures. Exhaustive and random searches over tight forms have found no counterexample (see *Walls and Strategy*, Section 3).

*Reading.* On a core, the three key outcomes are forced in pairs by both players and singly by neither: the loop of refutation is present locally, as in a rock–paper–scissors. On a stopping game it is built step by step in time, one constant line per node. The theorem says both ways of building the loop always leave a player without a strict Nash strategy. *(Interpretation.)*

## 7. Three outcomes by hand

With three outcomes the theorem has a short direct proof, without the summary search and without induction. It uses only that every 2 × 2 subform is tight. A 2 × 2 form is tight exactly when it has a constant row or column.

**Words.** Fix a player i and its opponent o, with i's strategies as rows. Let u ≠ v be outcomes. A row *leaves u* if some cell of the row holding u lies in a column holding another outcome. A row *reaches v from u* if some cell of the row holding u lies in a column holding v. A row is *inside* a set of outcomes if all its cells hold outcomes from the set. The same words are used for columns, with rows and columns exchanged.

**Working conditions.** Let P = (t, m, w), best first.
- With Q the reverse of P, the configuration (i, P, Q) works exactly when: i does not force t; every row holding w leaves w; every row inside {t, m} holding m reaches t from m.
- With Q the rotation (m, w, t), it works exactly when: i does not force t; every row holding m reaches t from m; every row inside {t, w} holding w leaves w.

*Proof.* Take the pair (y, M) of a row (Section 3). With the reverse, y is w if the row holds w; otherwise m if it holds m; otherwise t. The row is refuted exactly when some column in which it holds y contains an outcome i prefers to y. For y = w this is any other outcome, for y = m it is t, and for y = t there is none. The rotation is the same with the opponent's order m, w, t. ∎

**Three facts.** Let u, v, w be the three outcomes, all present. Each fact holds with the roles of rows and columns exchanged as well.
- *(F1)* If o does not force w, every row holding w leaves w. Otherwise all w-cells of some row lie in columns that are constant w.
- *(F2)* Every row inside {v, w} holding w reaches v from w, or every column inside {u, w} holding w leaves w.
  *Proof.* Suppose a row r and a column c both fail. Their common cell lies in {v, w} ∩ {u, w}, so it holds w. It is a w-cell of c, so its row r holds only w. But v occurs in some column, r holds w there, and so r reaches v from w. ∎
- *(F3)* Every row holding w reaches v from w, or every column holding v reaches w from v.
  *Proof.* Suppose a row r and a column c both fail. Their common cell does not hold w: it would be a w-cell of r in a column holding v. It does not hold v either: it would be a v-cell of c in a row holding w. So it holds u. Take a w-cell of r, in a column c′, and a v-cell of c, in a row r′. Column c′ holds no v and row r′ holds no w, so the cell (r′, c′) holds u. On rows r, r′ and columns c, c′ the subform is (u, w | v, u), which has no constant line and so is not tight. ∎

(F1) and (F2) hold for every form with three outcomes. (F3) is where total tightness enters. On random forms that are not totally tight, the lemma below fails in about 3% of the cases.

**Chain lemma.** Let a, c, e be the three outcomes. Let i be a player who does not force a, and suppose its opponent o does not force c. Then one of the following four configurations works:

(i, (a, e, c), reverse), (o, (c, a, e), rotation), (i, (a, c, e), rotation), (o, (c, e, a), reverse).

*Proof.* Each step uses the failure of the previous configuration.
1. (i, (a, e, c), reverse). i does not force a, and rows holding c leave c by (F1). So this configuration works unless some row inside {a, e} holding e does not reach a from e.
2. In that case (F2) gives: every column inside {c, e} holding e leaves e. Then (o, (c, a, e), rotation) works unless some column holding a does not reach c from a.
3. In that case (F3) gives: every row holding c reaches a from c. Then (i, (a, c, e), rotation) works unless some row inside {a, e} holding e does not leave e.
4. In that case (F2), with rows and columns exchanged, gives: every column inside {c, e} holding e reaches c from e. Columns holding a leave a by (F1), since i does not force a. So (o, (c, e, a), reverse) works. ∎

The four configurations alternate between the players and between the two kinds. Each one's failure hands the refutation on to the next. *(Interpretation: the loop of refutation of Section 6, carried by four orders.)*

**Theorem for three outcomes.** Every non-dictatorial totally tight form with three outcomes has a working configuration, with Q the reverse of P or its rotation.

*Proof.* Some player i does not force some outcome a. If its opponent does not force some outcome c ≠ a, apply the chain lemma. Otherwise the opponent forces both outcomes other than a. Then i forces no outcome, since a constant row would meet two constant columns with different outcomes. The opponent is not a dictator, so it does not force a. Apply the chain lemma to the opponent, a, and any c ≠ a. ∎

**The position lemma for three outcomes.** The chain lemma also gives the position lemma of Section 8 for three outcomes. Take a line of j with outcome x, after which the form is still valid. Then j does not force some outcome a ≠ x; let b be the third outcome.
- If the other player does not force some c ≠ a, the chain with i = j gives a configuration of j with top a, or one of the other player whose Q, (a, e, c) in both kinds, has x among its two lowest outcomes, since x ∈ {c, e}.
- Otherwise the other player forces x and b. Then j forces nothing, and the chain applies with i the other player, top a and c = b. It gives a configuration of j with top b, or one of the other player whose Q is (b, x, a), with x among its two lowest outcomes.

**How the facts were found.** For each player, the working conditions depend on 24 yes-or-no properties of the form: forcing, leaving and reaching, for each choice of outcomes. On stopping games with three outcomes these properties take few joint values. A search for short implications that hold on all of them, and that together exclude every assignment in which the lemma fails, returned seven implications up to renaming outcomes. The chain lemma was read off the resulting propositional proof, and its proof uses only (F1), (F2) in both forms and (F3).

The chain lemma was checked directly on 3,000 random totally tight forms of size up to 6 × 6, with 15,376 cases. It was also checked on every stopping game with three outcomes up to seven nodes, with 292,488 cases. No failure was found.

**Beyond three outcomes: the chain conjecture.** For an order P with top a, write P* for P with everything below the top reversed: (a, M, c)* = (a, c, M reversed). The rotation of P* is the reverse of P. So, with P running from a to c, the following four configurations are of the two kinds:

(i, P, rev P), (o, rev P, P), (i, P*, rev P), (o, (rev P)*, P).

With three outcomes and P = (a, e, c) these are the four configurations of the chain lemma.

**Conjecture (computer-checked for four outcomes).** Let i not force a and its opponent o not force c ≠ a. Then for every order P with top a and bottom c, one of these four configurations works.

Checks, with no failure:
- *Four outcomes, exhaustively.* The check covers all reachable summaries of Section 3 with four outcomes present: 15,662,736 cases on totally reducible forms and 20,280,576 from the core summaries.
- *Five and six outcomes, by sampling.* On random stopping games: 800 games with 119,184 cases for five outcomes, and 800 games with 771,120 cases for six.
- *Random totally tight forms with four outcomes.* 1,500 forms, with 38,400 cases.

The four configurations were found as the smallest family of shapes that always contains a working configuration on stopping games with four outcomes. Every order of the middle outcomes works.

The theorem for three outcomes uses only the chain lemma and the forcing sets. So a proof of the conjecture for every number of outcomes would give the theorem for all totally tight forms, without the induction of Section 8.

**Reading.** The four tests take place in three games.
- *The opposed game* (P against rev P). Both players are tested in it.
- *i's twin game* (P* against rev P). i ranks a first, and agrees with o on every other outcome.
- *o's twin game* (P against (rev P)*). o ranks c first, and agrees with i on every other outcome.

A configuration fails exactly when the tested player has a strategy against which every best reply of the opponent is an equilibrium of its game. In the opposed game these are saddle points, all with the same outcome. Neither a nor c can be that outcome, by (F1).

Geometrically, P ↦ rev P is the antipodal map of the permutohedron. P ↦ P* is the antipodal map of the facet on which a is on top, with the other outcomes forming the bottom block. In *The global form*, Section 8, the layer |S| = m − 1 of the stack of degrees lives on such facets. *(Interpretation; the connection is not worked out.)*

**Towards a proof of the conjecture.** Fix P = (a, m₁, …, m_n, c), and write "above" and "below" for P.
- *The saddle value.* By tightness the opposed game has an equilibrium. Its equilibria are saddle points, and they all have one outcome v. Every row's worst outcome is at or below v, and every column's best outcome is at or above v. Equality holds for some row and some column.
- *v is a middle outcome.* If v = a, a saddle point's row holds only a, so i forces a. If v = c, its column holds only c, so o forces c. Write v = m_q.

A test fails when the tested player has a strategy against which every best reply of the opponent is an equilibrium of its game. Call such a line *safe*. All four tests fail exactly when there are four safe lines:
- r₁, a row of i, safe in the opposed game. Its worst cells are saddle points, so its worst outcome is v.
- s₂, a column of o, safe in the opposed game. Its best outcome is v.
- r₃, a row of i, safe in i's twin game. It is of one of two types:
  - *type γ*: r₃ holds c, and its c-cells lie in columns without a;
  - *type δ*: r₃ does not hold c. Its worst outcome is some m_j, and its m_j-cells lie in columns inside {m₁, …, m_j}.
- s₄, a column of o, safe in o's twin game, of one of two types:
  - *type α*: s₄ holds a, and its a-cells lie in rows without c;
  - *type β*: s₄ does not hold a. Its best outcome is some m_l, and its m_l-cells lie in rows inside {m_l, …, m_n}.

**Proved, for any number of outcomes:**
1. j ≥ q and l ≤ q. No row's worst outcome is above v, and no column's best outcome is below it.
2. No α together with γ. *Proof.* The common cell of r₃ and s₄ is not a: it would be an a-cell of s₄ in a row with c. It is not c either: it would be a c-cell of r₃ in a column with a. Take an a-cell of s₄, in a row r′ without c, and a c-cell of r₃, in a column s′ without a. The cell (r′, s′) is neither a nor c. On rows r₃, r′ and columns s₄, s′ the subform has no constant line. ∎ This generalises (F3).
3. No r₁ together with β with l = q. *Proof.* r₁ lies at or above v, and s₄ lies at or below m_l = v. So their common cell is v. It is an m_l-cell of s₄, so r₁ lies inside {m_q, …, m_n}: r₁ is constant v. Then all its cells are saddle points. So no column holds an outcome above v, and a does not occur. ∎
4. No s₂ together with δ with j = q. This is the mirror image of 3.

With three outcomes, n = 1 forces j = l = q, and 1–4 are the proof of the chain lemma.

What remains for n ≥ 2 are the cases in which r₃ is of type δ with j > q, or s₄ of type β with l < q: lines whose critical outcome lies strictly between v and an end of P. They occur in about 10% of the cases on stopping games with four outcomes, but never together with all three other safe lines.

On stopping games with four and five outcomes, every remaining combination is excluded by one of a few further patterns, none of them proved. Here r₁ and s₂ are refined by whether r₁ holds a and whether s₂ holds c, and each pattern comes with its mirror image:
- an r₁ without a never occurs together with an s₂ without c;
- three patterns of three lines never occur: α, r₁ with a and s₂ without c; β with l < q, r₁ with a and s₂ without c; β with l < q, δ with j > q and r₁ with a;
- one pattern needs all four lines: α, δ with j > q, r₁ with a and s₂ with c.

Over the same samples, at least one of the two tests in the opposed game fails, and at least one of the two tests in the twin games. Every pattern of failures allowed by this and by the conjecture occurs.

**Merging outcomes (proved).** Call the outcome that the opponent picks against a safe line its *critical outcome*: v for r₁ and s₂, the worst outcome of r₃, and the best outcome of s₄. Merge two middle outcomes that are adjacent in P into one. They are then adjacent in all four orders, since P* and (rev P)* only reverse the middle.
- The merged form is again totally tight, because a constant line stays constant.
- i still does not force a, and o still does not force c.
- A safe line whose critical outcome is not one of the two merged outcomes stays safe for the merged orders. Its critical outcome stays the opponent's choice, its cells holding that outcome are the same, and the merged outcome lies on the same side of it as both of the outcomes it replaces.
- More generally, the critical outcome y may itself be merged with a neighbour x that the line does not hold. The cells holding y are then unchanged, and the set of outcomes better than y for the tested player can only shrink.

*Checked* on random stopping games with four to six outcomes: in 994,458 merges avoiding the critical outcome of a safe line, the test still failed afterwards.

**Reduction (proved).** Suppose the conjecture fails, and take a counterexample with the fewest outcomes.
- Its critical middle outcomes are v and, by 1–4, at most two more: the worst outcome m_j of an r₃ of type δ, with j > q, and the best outcome m_l of an s₄ of type β, with l < q. By 2, at most one of the two lines is of type α or γ.
- No two adjacent middle outcomes can both be non-critical. Otherwise merging them would give a smaller counterexample.
- So the middle outcomes consist of the at most three critical ones, with at most one other outcome before, between and after them. That leaves at most seven middle outcomes, and so at most nine outcomes in all. With two critical middle outcomes there are at most seven outcomes.

Since the conjecture holds for four outcomes (checked exhaustively), it holds for every number of outcomes as soon as it holds for five to nine outcomes, in the configurations just described.

## 8. Towards a hand proof: a working configuration survives

A *configuration* is a triple (i, P, Q) with Q the reverse of P or P with its top moved to the bottom; configurations of forms with different outcome sets are compared on the outcomes present.

**Refutation in a stopping game.** In a stopping game a strategy of a player is its first stopping node, or never stopping; the outcome of two strategies is that of the earlier stop, or the terminal outcome. Fix i, P and Q, and a strategy s of i with outcome o_s (the terminal outcome if s never stops). Let y be the opponent's favourite among o_s and the outcomes of the opponent's nodes before s. Then s is refuted exactly when one of the following holds:
- (a) o_s = y, and some outcome of i's nodes, the terminal outcome or the outcome of an opponent node after s is better for i than y;
- (b) some opponent node before s has outcome y, and some node of i before that one has an outcome that i prefers to y.

This agrees with the matrix computation on 3,000 random stopping games.

**Survival.** Build a form by adding constant lines, and say that a line is *absorbed* if some configuration works both before and after it.

**Observation (computer-checked).** Let the form be valid and let the new line's outcome already be present. The line is absorbed exactly when the new form is valid.

The check covers every reachable summary of Section 3, so every form of the class, of any size:
- totally reducible forms: 1,596 line additions with three outcomes and 3,802,572 with four;
- forms with a core, from the pessimistic starting summaries: 1,062 and 4,918,164.

No exception was found. (A configuration that survives on a pessimistic summary also survives on the actual form.) Stopping games were also checked directly, without summaries, up to seven nodes with three outcomes and six with four.

The observation is stronger than the theorem. A line often makes new configurations work: in 57% of the front extensions of small stopping games. But some configuration that worked before always keeps working.

The two sides of the observation are easy to describe. Take a line of player j with outcome x.
- *Survival.* A working configuration of j survives exactly when x is not its top: the new constant row is then refuted, and the old rows only improve. A working configuration of the other player survives exactly when its opponent order ranks x at or below the favourite y of every row; the rows with y below x become (x, x), which are not refuted.
- *Validity.* The new form is dictatorial exactly when j forces every outcome other than x, since the other player now forces at most x.
- *New outcomes.* A line with an outcome not yet present is always absorbed. The outcome is inserted below the top of a configuration of j, or at the bottom of the opponent order of a configuration of the other player.

**Two facts used below.** Fix a configuration (i, P, Q) and a strategy s of i.
- *The favourite y is the opponent's favourite entry of the row of s.* The row's entries are the outcomes of the opponent's nodes before s, and o_s.
- *A row whose favourite is the lowest present outcome of Q is constant.* All its entries equal that outcome, so i forces it.

In both kinds the lowest outcome of Q is the top of P. A refuted row has an outcome better than y for i, so its y is not the top of P. Hence, in a working configuration whose top is present, every row's favourite lies above the lowest present outcome of Q.

**The base cases (proved).** Build a form from a single cell by adding constant lines, and consider the first line (j, x) after which the form is valid. Before it, the form had at most two outcomes or a dictator. A dictator must be the other player: if j forced every outcome before, it would still do so afterwards. In both cases a configuration of j with Q the reverse of P works afterwards.
- *(A) Two outcomes before, x new.* Since j is not a dictator afterwards, j did not force both old outcomes. Let u be an old outcome that j did not force, v the other, and P = (u, x, v). The new row has type (x, u), and j prefers u to x, so the row is refuted. An old row has favourite v or u. It is not u: u is the lowest outcome of Q = (v, x, u), and a row with favourite u would be constant, but j did not force u. So it is v, and after the line the row has an outcome at least as good as x, which is better than v.
- *(B) The other player was a dictator.* Its constant columns meet every row of j, so every row of j contains every old outcome. Take any P whose top and bottom both differ from x. Every old row's favourite is then the bottom of P, and the line gives the row x, which is better. The new row has type (x, best present outcome), and x is not the top.

Both rules were checked at every base transition of stopping games up to seven nodes with three outcomes and six with four: 16,524 and 12,018 orders, with no failure. For forms with a core, the core itself is already valid; it is the base, and the search of Section 4 covers it.

A hand proof of the theorem therefore reduces to one more statement, about where x sits in the working configurations. Lines with a new outcome are absorbed as described above.

**Position lemma (computer-checked).** Let the form be valid before and after a line (j, x) with x present. Then one of the following exists:
- a working configuration of j whose top among the present outcomes is not x;
- a working configuration of the other player whose top is present, and whose opponent order Q has x among its two lowest present outcomes.

Either configuration survives the line. The first does by the survival rule. For the second, every row's favourite lies above the lowest present outcome of Q, so at or above x. The check is made on the same reachable summaries as the observation, with no exception:
- totally reducible forms: 1,596 and 3,802,572 line additions;
- forms with a core: 1,062 and 4,918,164.

It was also checked directly on stopping games up to seven nodes with three outcomes and six with four: 343,422 and 142,178 valid extensions.

What remains open is the contrapositive, a statement about tops and positions only.

**Lemma (open).** Let a totally tight form be valid, let x be one of its outcomes, and let j be a player. Suppose that every working configuration of j has top x, and that every working configuration of the other player whose top is present has x above the two lowest present outcomes of its Q. Then j forces every outcome other than x.

With three outcomes, the second condition says that x is the favourite outcome of Q. For the reverse kind it is the bottom of P; for the rotated kind it is the second outcome of P. For three outcomes the position lemma holds by hand (Section 7), so the open lemma concerns four or more outcomes.

**What does not work.** Each of the following simpler forms of the inductive hypothesis fails on stopping games with three outcomes:
- *Tops only.* Suppose a line of j with outcome x is absorbed only when j works with some top other than x, or the other player works with the second kind and top x. This misses about a third of the valid extensions. If the other player may work with top x in either kind (x is then the lowest outcome of Q), about a fifth are still missed. Allowing the second-lowest place of Q as well closes the gap: this is the position lemma.
- *One canonical order.* Fix one order P for each player, top and kind: the top followed by the other outcomes by first or last appearance, either way round. Between 3,946 and 32,288 of the 61,926 games then have no working configuration left.
- *One configuration for the whole construction.* In about 20% of the runs of valid suffixes, no configuration works on all of them. The working configuration has to change along the way.
- *Small repairs.* Swapping two outcomes of P, or changing the kind of Q, does not always turn a working configuration that is not absorbed into one that is.

The inductive hypothesis therefore has to describe a family of working configurations, not one configuration.

## 9. Scripts

In `scripts/strategy/rational_diagonal/` (they import `diag2.py` and `recipes_core.py` from the same folder):
- `tr_automaton.py`: the summary search in Python, with the update rule documented;
- `tr_auto.cpp`: the same search in C++, reduced by renaming outcomes; `./tr_auto k zsrot [file]` runs it with the two kinds of opponent order, from a single cell or from starting summaries in a file;
- `tr_validate.py`: comparison of the update rule with matrix computation;
- `tr_random.py`: random stopping games with five and six outcomes;
- `core_struct.py`, `core_struct4.py`: pessimistic core summaries from the table, for three and four outcomes;
- `core_enum.py`, `core_summ.py`, `core_profiles.py`, `core_struct_check.py`, `core_struct_check4.py`: enumeration of cores, their summaries, and the coverage checks.

In `scripts/strategy/rational_diagonal/absorption/` (Sections 7 and 8):
- `sg.py`: stopping games, the characterisation of refutation and its check against the matrix;
- `collect.py k N`: all valid stopping games with up to N nodes and their working configurations, saved for the other scripts;
- `absorb.py`, `births.py`, `chain.py`: survival versus validity, newly working configurations, one configuration along a run;
- `abs_tops.py`, `canon_family.py`, `repair.py`, `absmode.py`: the simpler forms that fail, and which player's configurations survive;
- `tr_absorb.cpp`: the check on all reachable summaries; `./tr_absorb k zsrot [file]` as for `tr_auto`;
- `base_rule.py k N`: the two base-case rules at every base transition of the stopping games;
- `positions.py k N`, `tr_positions.cpp`: the position lemma on stopping games and on all reachable summaries; `./tr_positions k zsrot [file]` as for `tr_auto`;
- `k3_feat.py`: the properties and working conditions of Section 7, checked against the matrix test;
- `k3_cegar.py`, `k3_schemas.py`, `k3_minimise.py` (in this order, after `collect.py 3 7`): the search for short implications, their closure under renaming outcomes, and the minimal set;
- `k3_chain.py`: the chain lemma on random forms (totally tight or not) and on stopping games;
- `k4_chainsearch.py`: the smallest family of shapes on stopping games with four outcomes;
- `chain_k.py`, `tr_chain.cpp`: the chain conjecture on random forms with four to six outcomes, and on all reachable summaries; `./tr_chain k zsrot [file]` as for `tr_auto`;
- `chain_pairs.py`: the proved pieces 1–4 towards the conjecture, and how often the remaining cases occur;
- `chain_atoms.py`, `chain_triples.py`: the patterns of safe lines that never occur together, and the patterns of failing tests;
- `chain_mergecheck.py`: safe lines after merging two adjacent middle outcomes.

## References

- Boros, E., Gurvich, V., Makino, K. and Papp, D. (2010). Acyclic, or totally tight, two-person game forms: characterization and main properties. *Discrete Mathematics* 310, 1135–1151. (Preprint: DIMACS Technical Report 2008-10.)
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Edmonds, J. and Fulkerson, D. R. (1970). Bottleneck extrema. *Journal of Combinatorial Theory* 8, 299–306.
- Gurvich, V. A. (1975). Solution of positional games in pure strategies. *USSR Computational Mathematics and Mathematical Physics* 15(2), 74–87.
- *Walls and Strategy* (draft, this repository).
