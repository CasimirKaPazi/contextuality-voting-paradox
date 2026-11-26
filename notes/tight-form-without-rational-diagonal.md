# A tight form without a rational diagonal

*Working note on open problem 1 of* Walls and Strategy *(rational diagonal on tight forms). It gives a tight, non-dictatorial two-player game form with three outcomes in which, under every pair of strict preferences, both players have a strict Nash strategy. So the answer to the two-player question with strict preferences is no. The note gives the example, a proof that can be checked by hand, and how it was found. For three outcomes it then gives the complete picture (Section 5): a form without a rational diagonal needs an outcome that both players can force, and with such an outcome there is an exact criterion. Section 6 turns to lotteries: in approval with a veto and a lottery on ties, approving what one prefers to the fallback is always a strict Nash strategy, for any number of players, as long as the fallback does not read declared ideals. Scripts: `scripts/strategy/rational_diagonal/tight_counterexample.py`, `three_outcomes_veto.py`.*

## 1. The example

Rows are player 1's strategies r0, …, r5, columns player 2's strategies s0, …, s5, outcomes a, b, c:

```
      s0 s1 s2 s3 s4 s5
r0    c  c  c  c  c  c
r1    c  b  a  b  a  a
r2    c  b  c  b  b  b
r3    c  b  a  c  c  a
r4    c  c  a  a  a  a
r5    c  b  a  b  c  b
```

**Theorem.** This form is tight and not dictatorial, and all three outcomes occur. Under every pair of strict preferences (P for player 1, Q for player 2), each player has a strict Nash strategy. So neither player admits a rational diagonal.

Recall the condition (*Walls and Strategy*, Section 3). At fixed P and Q, a strategy of player i is a *strict Nash strategy* if it is a best reply to every best reply of the opponent. A rational diagonal for i exists exactly when i has no strict Nash strategy. In the words of *The rational diagonal on totally tight game forms*: a strategy is a strict Nash strategy exactly when it is not refuted. Take y, the opponent's favourite outcome in the strategy's line. The strategy is refuted when some cell of the line holding y lies in a crossing line that contains an outcome i prefers to y.

## 2. Proof

**Tightness.** A form with a constant row c and a constant column c is tight. Take a set S of outcomes. If S contains c, the row player forces S with the constant row. If not, the complement contains c, and the column player forces it with the constant column.

**Not dictatorial.** The constant lines are r0 and s0, both with outcome c. Neither player forces a or b.

**Strict Nash strategies of player 1.** Write P as a word, best first; "Q top x" means that x is player 2's favourite. Two facts are used throughout:
- A row whose favourite y is P's top is never refuted: nothing is better than y.
- Column s0 is constant c. So a c-cell in s0 never refutes.

| P | Q | strategy | reason |
|---|---|---|---|
| c on top | any | r0 | constant c, which is P's top |
| acb | any | r4 | r4 holds only a and c, and its c-cells lie in s0 and s1, which hold no a |
| bca | any | r2 | r2 holds only b and c, and its c-cells lie in s0 and s2, which hold no b |
| abc or bac | top c | r1 | r1's only c is in s0 |
| abc or bac | top equal to P's top | r1 | r1 holds a and b, so the favourite is P's top |
| abc | bac | r4 | r4 holds a and no b, so the favourite is a, P's top |
| abc | bca | r3 | the favourite is b; r3's only b is in s1, which holds no a |
| bac | abc | r2 | r2 holds b and no a, so the favourite is b, P's top |
| bac | acb | r5 | the favourite is a; r5's only a is in s2, which holds no b |

Each row of the table follows by reading one row and at most two columns. In the rows for acb and bca, the favourite is P's top or c, and a c-cell is refuted only by a better outcome in its column, which here would have to be P's top. The rows cover all 36 pairs: every P has c on top, in the middle or at the bottom. With c at the bottom, Q has c on top, or P's top on top, or else Q's top is P's second outcome and Q is one of the two orders listed.

**Strict Nash strategies of player 2.** The form is isomorphic to its transpose. Reorder the rows as r0, r2, r4, r5, r3, r1 and the columns as s0, s5, s1, s4, s2, s3: the result is the transpose. So player 2's situation is player 1's. Explicitly, the table for player 2 (columns now play the role of rows) reads: c on top, s0; acb, s2; bca, s1; c at the bottom and Q top c or top equal to P's top, s5; abc against bac, s2; abc against bca, s4; bac against abc, s1; bac against acb, s3. ∎

The script checks the table for both players against the matrix, checks tightness directly (every one of the 36 pairs of strict preferences has a pure equilibrium) and checks the isomorphism. The repository's brute-force test, `diag2.works_brute`, independently finds no rational diagonal. The theorem is also checked in Lean (`lean/TightCounterexample.lean`): tightness through the common veto, non-dictatorship, and for both players a strict Nash strategy under every pair of strict preferences, reduced to the 36 pairs of rankings.

## 3. How small it is

- Deleting any row or column destroys the property (computed).
- Earlier searches found no counterexample among all tight forms up to 4 × 4 and 3 × 5 with three outcomes (`scan.py`), and none in about 430,000 random tight forms up to 5 × 5 (`randtight.py`).
- Forms with a c-border, as here, are tight whatever the inside. An exhaustive scan of the inner forms found no example with an inner part of size 4 × 4, 4 × 5, 3 × 5, 3 × 6, 2 × 7 or 2 × 8 (computed; `border_scan.cpp`; 4 × 5 alone has about 3.5 billion inner forms). The property is symmetric under transposing, so 5 × 4 and the other transposed sizes are covered too. In particular, no square form with a c-border smaller than 6 × 6 is an example.

Whether a smaller tight counterexample exists without a c-border is open.

## 4. How it was found

For three outcomes, the working conditions of both kinds of opponent order depend on 24 yes-or-no properties of each player: forcing, leaving and reaching (Section 7 of *The rational diagonal on totally tight game forms*). On totally tight forms a short list of implications between these properties proves the theorem. The same search was run on tight forms: about 300,000 non-dictatorial tight forms (all forms up to 3 × 4 and 4 × 3, and 2 × 5 and 5 × 2, and random ones from 3 × 3 to 7 × 7) gave 12,256 joint values of the 48 properties. After 66 implications the search reached an assignment that no implication of up to four properties, valid on all collected forms, excludes. In it both players force c, and neither forces anything else. A local search over forms with a constant row and column c then realised the assignment as a 7 × 7 form, and deleting lines gave the 6 × 6 form above. The assignment only says that no configuration of the two kinds works; the direct check showed that no pair of strict preferences works at all.

## 5. Three outcomes: the complete picture

A constant row and a constant column meet in a cell. So if both players force single outcomes, they force the same one, and only that one. Call it a *common veto* c. A form with a common veto has a constant row c and a constant column c, so it is tight (Section 2), and every line contains c.

The words of Section 7 of *The rational diagonal on totally tight game forms* are used: a row *reaches* t from m if some m-cell of the row lies in a column holding t; it *leaves* w if some w-cell lies in a column holding another outcome; it is *inside* a set if all its cells lie in the set. The same words apply to columns. Fact (F1) of that note holds for every form: if the opponent does not force w, every row holding w leaves w.

**Theorem A (no common veto).** Let a two-player form with three outcomes be non-dictatorial, with no outcome forced by both players. Then some player works with Q the reverse of P or its rotation.

*Proof.* Some player o forces no single outcome, since otherwise there would be a common veto. Let i be the other player, and let t be an outcome i does not force; i is not a dictator. Let u and v be the other two outcomes.

By (F1), every row holding any outcome leaves it, since o forces nothing. So the configuration (i, (t, m, w), reverse) works exactly when every row inside {t, m} holding m reaches t from m. Suppose this fails both for m = u and for m = v: there are rows r_u inside {t, u} and r_v inside {t, v}, holding u and v, whose u-cells and v-cells lie in columns without t.

*Step 1.* Every column holding t reaches u from t. Otherwise take such a column c, all of whose t-cells lie in rows without u. The cell (r_u, c) lies in {t, u}. If it is u, it is a u-cell of r_u in a column holding t. If it is t, it is a t-cell of c in a row holding u. Both are excluded.

*Step 2.* Every column inside {u, v} holding v leaves v. Otherwise take such a column c′, each of whose v-cells lies in a row holding only v. The cell (r_v, c′) lies in {t, v} ∩ {u, v}, so it is v. So r_v holds only v, and its v-cells lie in every column. Then no column holds t, and t does not occur.

Now consider (o, (u, t, v), rotation), with i's order (t, v, u). By the working conditions of that note, read for columns, it works exactly when o does not force u, every column holding t reaches u from t, and every column inside {u, v} holding v leaves v. These are the hypothesis, Step 1 and Step 2. ∎

The proof uses neither tightness nor recombination. On a form without a common veto, the three configurations (i, (t, u, v), reverse), (i, (t, v, u), reverse) and (o, (u, t, v), rotation) always contain a working one.

**Theorem B (common veto).** Let a non-dictatorial form with three outcomes have a common veto c, and let a, b be the other outcomes. Read player i's strategies as rows. Call a row a *wall row* if all its c-cells lie in columns that are constant c. Then i has no rational diagonal exactly when all of the following hold, for (x, y) = (a, b) and (b, a):
- (W) there is a wall row;
- (A_x) some row inside {x, c} has its c-cells in columns without x;
- (E_xy) some row holding y has its y-cells in columns without x, or some wall row does not hold y.

*Proof.* Every row and every column holds c. A row whose favourite, for the opponent, is i's top is never refuted. Go through i's orders P.
- *c on top.* The constant row c is never refuted.
- *P = (x, c, y).* A row as in (A_x) has favourite x or c, and its c-cells lie in columns without x, the only better outcome. So it is never refuted. If (A_x) fails, i works under Q = (y, c, x). Rows holding y have favourite y, which is i's worst, and every column holds c. The other rows lie inside {x, c} and have favourite c, and each has a c-cell in a column holding x.
- *P = (x, y, c), Q with c on top.* Every row has favourite c. A wall row is not refuted. Without a wall row, every row has a c-cell in a column holding x or y, and i works.
- *P = (x, y, c), Q with x on top.* A row holding x has favourite x and is not refuted. Such a row exists, since x occurs.
- *P = (x, y, c), Q = (y, x, c).* A row as in (A_x) holds x and not y, so its favourite is x: not refuted.
- *P = (x, y, c), Q = (y, c, x).* Rows holding y have favourite y and are refuted exactly when some y-cell lies in a column holding x. Rows without y have favourite c and are refuted exactly when they are not wall rows. So i has a strict Nash strategy exactly when (E_xy) holds. ∎

So a form with three outcomes has no rational diagonal exactly when it has a common veto and both players satisfy (W), (A_a), (A_b), (E_ab) and (E_ba). In the example, player 1's rows r0, r1, r4, r2, r3, r5 are the constant row, a wall row, the rows for (A_a) and (A_b), and the rows for (E_ab) and (E_ba).

*Checks.* The criterion agrees with the brute-force test on all forms with a c-border and an inner part of 3 × 3, 2 × 4 or 3 × 4 (1,095,920 player checks), and on 28,859 random forms with a common veto. Theorem A held on 20,314 random forms without one.

*Why small forms do not suffice.* One row can serve several conditions for player 1: a row holding a except for c in the constant-c columns is a wall row and satisfies (A_a) and (E_ab). But then every column that is not constant c holds a, so no column is inside {b, c}, and player 2 fails (A_b). The conditions of the two players pull against each other. *(Reading; the exact minimum is not known.)*

**How Theorem A was found.** The implication search of Section 4 was rerun with the extra hypothesis that no outcome is forced by both players. It ended after 97 implications; up to renaming outcomes and swapping players, six of them suffice, and each has a short proof. For each pattern of forcing, a search for the fewest configurations of which one must work returned the three configurations of the proof.

## 6. Lotteries on ties: approval with a veto

A common veto is the shape of a consensus procedure with a fallback: either participant can refuse everything and so impose the fallback. The simplest such procedure shows what a lottery adds.

**The procedure.** There is a finite set of proposals and a fallback F, which may itself be a lottery. Each of n ≥ 2 players approves a set of proposals; the empty set is a veto. If all the sets meet in I, the outcome is a lottery λ_I over I that gives every member of I positive probability. If they have no common member, the outcome is F. The fallback is a common veto; with two players the form is therefore tight.

With more than two players, a rational diagonal for i asks, for every strategy b of i, for a profile of the others that is an equilibrium among them given b and leaves b not a best reply (*Walls and Strategy*, Section 3). Player i has none exactly when some strategy b is a best reply to every such profile; call b a strict Nash strategy in that case too.

**Proposition (sincere approval is safe).** Let all players have expected utilities, generic in the sense that each player's utilities of F and of the proposals are all different. Then approving exactly the proposals one prefers to F is a strict Nash strategy. So no player has a rational diagonal.

*Proof.* Let A be player i's sincere set. Take a profile of the others' sets that is an equilibrium among them given A, and let K be the intersection of their sets.
- *K meets A in at most one proposal.* Otherwise let k be another player and z k's favourite in K ∩ A. By approving only z, player k gets z instead of a lottery with full support on at least two proposals, which k values strictly less. So the profile was not an equilibrium.
- *If K ∩ A = {y}*, i gets y. Every other proposal in K lies outside A, so i likes it less than F, and F less than y. Whatever i approves, it gets F or a lottery over K, worth at most y.
- *If K ∩ A is empty*, i gets F. Every proposal in K lies outside A, so every lottery over K is worse for i than F. ∎

The lottery on ties is what the proof uses. Two comparisons show that it is needed:
- *Ties broken deterministically.* With two proposals a, b and ties going to a, each player still works under one pair of strict orders; with ties going to F, under four. With random utilities and two to four proposals and ties broken by a fixed order, between 3 and 8 percent of the players have a rational diagonal.
- *The coin as a fourth outcome with arbitrary orders.* With two proposals, ties settled by a fair coin, and all strict orders on a, b, F and the coin, each player works under 36 pairs of orders. All of them rank the coin outside the interval between a and b, which no expected utility does. Among the orders an expected utility allows, none works.

*(Proved; the comparisons computed, `approval_veto.py`. With random generic utilities, for two players with two to four proposals and for three and four players with two or three proposals, no player had a rational diagonal and sincere approval was a strict Nash strategy in every case. With deterministic ties, rational diagonals occurred for three and four players too.)*

*A fallback that reads declared ideals.* The proof needs F to be fixed. In the CORE proposal the fallback is the random ballot over the participants' ideals. If each of two players also declares an ideal, used only when the approved sets do not meet, the rational diagonal returns: with three proposals and random utilities, 68 of 2,000 players have one; with two proposals, none. The mechanism is again a tie. When the sets meet, the opponent's declared ideal costs the opponent nothing, so every declaration is a best reply, and the opponent can choose one that makes i's veto worth more than the agreement i accepted. In the example found, player i values y, x and z at 0.92, 0.71 and 0.40, and the opponent prefers z to x to y; when i accepts x, the opponent accepts x and declares x, and then i's veto would give the even lottery over x and y, which i prefers to x. With the fallback fixed in advance by the true ideals, it is a fixed lottery and the proposition applies. *(Computed; the reading of the mechanism is checked on the example.)*

*Stages with a random exclusion.* In the call structure of CORE, a group that does not agree loses a member drawn at random, and the process goes on at the smaller group. If each group voted by approval with a veto, the fallback at a group would be the lottery over what the smaller groups do. For two members this is fixed: the remaining member enacts their ideal, so the fallback is the even lottery over the two ideals, and the proposition applies. For three or more members the fallback is a lottery over what the smaller groups do, and that is itself strategic. Approval with a veto has many equilibria, even in undominated strategies: two members who both prefer x and y to the fallback can coordinate on approving only x, or only y. So the preferences alone do not fix the fallback, and a member who wants to approve what is worth more than it must first predict how the smaller groups will play. This is the anticipation of Lemma 2 again, one stage down. Whether it yields a rational diagonal at the larger group is open. *(The case of two members is proved; the multiplicity of equilibria is elementary.)*

Sincere approval is not dominant: if the opponent approves two proposals that i likes, i does better by approving only the better one. So with arbitrary opponents Lemma 2 of *Walls and Strategy* still applies, and the barrier of Theorem 3 remains. What the lottery removes is the rational diagonal: against an opponent who plays some best reply, the sincere set is always right, and it needs only i's own utilities and the fallback.

*Reading.* In the 6 × 6 form the strict Nash strategies are combinatorial and depend on the order P; in approval with a veto there is one strategy, the same rule for every utility. The sequential call game of *CORE and the Formal Results* (Section 3g) arrives at the same rule: there accepting exactly the proposals worth at least the call is weakly dominant, by sequential rationality. In the simultaneous procedure the lottery on ties does the work of the visible turns. *(Interpretation.)*

## 7. Where it sits

- *Totally tight forms* and *games of perfect information* always admit a rational diagonal, by the reduction and the exact searches of *The rational diagonal on totally tight game forms*. The example is neither. Its 2 × 2 subform on rows r2, r3 and columns s2, s3 is (c, b | a, c), which has no constant line, so it is not totally tight. It also fails the recombination property (R) of that note, which every game tree has.
- What fails is the step (F3) of the three-outcome proof, for the pair a, b: some row holding b reaches no a from b, and some column holding a reaches no b from a. On totally tight forms and on game trees this cannot happen.
- The structure is a common veto: each player can impose c, and nobody can impose a or b. With three outcomes this is necessary (Section 5). Every strategy then contains c, so the opponent can always fall back on c, and the constant c lines make that fallback safe against any refutation. With c at the top of P, i keeps the constant c line; with c in the middle, i has a line that holds only its top and c, whose c-cells lie in columns without its top; with c at the bottom, the remaining lines answer the four possible opponent orders one by one. *(Interpretation.)*
- For the dichotomy of *Walls and Strategy* (Theorem 3) nothing changes: it uses arbitrary opponent programs. What changes is the strengthening to rational opponents. On this form, whatever the strict preferences, each player has a strategy that is right against every rational opponent: a best reply to every best reply.

## 8. Open

- Whether tight forms with property (R) always admit a rational diagonal. The chain of four configurations fails on some of them with four outcomes, but no form with (R) without a rational diagonal is known.
- With three outcomes, Section 5 settles the question. With four or more outcomes: whether a form without a rational diagonal still needs a common veto, whether Theorem A extends, and whether there is any counterexample at all. A local search over 7 × 7 forms with four outcomes found none, with or without a common veto; at best 18 of the 1,152 configurations still worked (computed, not exhaustive; `local_search.cpp`). Neither did turning one or two cells of the example into a fourth outcome.
- The smallest counterexample.
- More players: the question for three or more players is untouched, except for approval with a veto, where Section 6 covers any number of players.
- Which consensus procedures with a random fallback admit a rational diagonal. Approval with a veto has none when the fallback is fixed; with a random ballot over declared ideals it has some. In between lie fallbacks from ideals declared before the votes, or call games with simultaneous votes.

## Scripts

In `scripts/strategy/rational_diagonal/`:
- `tight_counterexample.py`: the checks of Section 2 and the deletion check of Section 3; plain Python, no arguments;
- `border_scan.cpp`: all inner forms of a given size inside a c-border, tested for a rational diagonal; `./border_scan n m [from to]` (4 × 5 takes about an hour on one core);
- `three_outcomes_veto.py`: Theorems A and B of Section 5 against the brute-force test, on random forms and on all small forms with a c-border;
- `approval_veto.py`: approval with a veto, Section 6; the ordinal comparisons, random expected utilities for two to four players, and the fallback from declared ideals;
- `local_search.cpp`: local search for tight forms without a rational diagonal, with any number of outcomes and optional constraints; `./local_search n m seed restarts flags k`.
