# A tight form without a rational diagonal

*Working note on open problem 1 of* Walls and Strategy *(rational diagonal on tight forms). It gives a tight, non-dictatorial two-player game form with three outcomes in which, under every pair of strict preferences, both players have a strict Nash strategy. So the answer to the two-player question with strict preferences is no. The note gives the example, a proof that can be checked by hand, how the example was found, and where it sits relative to the positive results. Script: `scripts/strategy/rational_diagonal/tight_counterexample.py`.*

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

The script checks the table for both players against the matrix, checks tightness directly (every one of the 36 pairs of strict preferences has a pure equilibrium) and checks the isomorphism. The repository's brute-force test, `diag2.works_brute`, independently finds no rational diagonal.

## 3. How small it is

- Deleting any row or column destroys the property (computed).
- Earlier searches found no counterexample among all tight forms up to 4 × 4 and 3 × 5 with three outcomes (`scan.py`), and none in about 430,000 random tight forms up to 5 × 5 (`randtight.py`).
- Forms with a c-border, as here, are tight whatever the inside. An exhaustive scan of the inner forms found no example with an inner part of size 4 × 4, 4 × 5, 3 × 5, 3 × 6, 2 × 7 or 2 × 8 (computed; `border_scan.cpp`; 4 × 5 alone has about 3.5 billion inner forms). The property is symmetric under transposing, so 5 × 4 and the other transposed sizes are covered too. In particular, no square form with a c-border smaller than 6 × 6 is an example.

Whether a smaller tight counterexample exists without a c-border is open.

## 4. How it was found

For three outcomes, the working conditions of both kinds of opponent order depend on 24 yes-or-no properties of each player: forcing, leaving and reaching (Section 7 of *The rational diagonal on totally tight game forms*). On totally tight forms a short list of implications between these properties proves the theorem. The same search was run on tight forms: about 300,000 non-dictatorial tight forms (all forms up to 3 × 4 and 4 × 3, and 2 × 5 and 5 × 2, and random ones from 3 × 3 to 7 × 7) gave 12,256 joint values of the 48 properties. After 66 implications the search reached an assignment that no implication of up to four properties, valid on all collected forms, excludes. In it both players force c, and neither forces anything else. A local search over forms with a constant row and column c then realised the assignment as a 7 × 7 form, and deleting lines gave the 6 × 6 form above. The assignment only says that no configuration of the two kinds works; the direct check showed that no pair of strict preferences works at all.

## 5. Where it sits

- *Totally tight forms* and *games of perfect information* always admit a rational diagonal, by the reduction and the exact searches of *The rational diagonal on totally tight game forms*. The example is neither. Its 2 × 2 subform on rows r2, r3 and columns s2, s3 is (c, b | a, c), which has no constant line, so it is not totally tight. It also fails the recombination property (R) of that note, which every game tree has.
- What fails is the step (F3) of the three-outcome proof, for the pair a, b: some row holding b reaches no a from b, and some column holding a reaches no b from a. On totally tight forms and on game trees this cannot happen.
- The structure is a common veto: each player can impose c, and nobody can impose a or b. Every strategy then contains c, so the opponent can always fall back on c, and the constant c lines make that fallback safe against any refutation. With c at the top of P, i keeps the constant c line; with c in the middle, i has a line that holds only its top and c, whose c-cells lie in columns without its top; with c at the bottom, the remaining lines answer the four possible opponent orders one by one. *(Interpretation.)*
- For the dichotomy of *Walls and Strategy* (Theorem 3) nothing changes: it uses arbitrary opponent programs. What changes is the strengthening to rational opponents. On this form, whatever the strict preferences, each player has a strategy that is right against every rational opponent: a best reply to every best reply.

## 6. Open

- Whether tight forms with property (R) always admit a rational diagonal. The chain of four configurations fails on some of them with four outcomes, but no form with (R) without a rational diagonal is known.
- The smallest tight counterexample, and whether there are counterexamples without a common veto, for instance with the effectivity function of the cores of totally tight forms (each player forces any two of three outcomes and no single one).
- More players: the question for three or more players is untouched.

## Scripts

In `scripts/strategy/rational_diagonal/`:
- `tight_counterexample.py`: the checks of Section 2 and the deletion check of Section 3; plain Python, no arguments;
- `border_scan.cpp`: all inner forms of a given size inside a c-border, tested for a rational diagonal; `./border_scan n m [from to]` (4 × 5 takes about an hour on one core).
