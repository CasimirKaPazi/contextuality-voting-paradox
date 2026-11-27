# The Ballot Polytope

*Working note, part of [Strategic Information](README.md), first draft. It concerns all methods at once. In a large electorate the value of a ballot is linear in what the ballot adds to the count, so a best reply is a corner of the set of things a ballot can add. This decides which changes to a ballot design can matter under the common rationale and which cannot, among them the allowing of equal ranks. Conventions and the definition of the count as in the README, Section 2. The checks are in `scripts/information/ballot_polytope.py`.*

## 1. The linear regime

Every ballot b has a *count vector* τ(b), what the ballot adds to the count of its method (README, Section 2): a vector of scores up to a number added to all of them, a vector of pairwise margins, a place in the histogram. The outcome is a function of the total count.

Let a voter with utilities u hold a belief about the count of the other ballots, and write F_u(x) for the expected utility of the winner when x is added to that count. The value of a ballot is F_u(τ(b)).

**Proposition 1 (linear regime).** If F_u is differentiable at 0, then

  F_u(τ(b)) = F_u(0) + g_u · τ(b) + (terms that vanish faster than τ(b)),

where g_u is the gradient of F_u at 0. The gradient is linear in the utilities; in particular g_{−u} = −g_u.

*Proof.* The first statement is the definition of the derivative. F_u is an expectation of u at the winner, which is linear in u, and so is its gradient. ∎

A single ballot is small against the count of a large electorate. If the voter's uncertainty about the count is spread over many ballots, the first term decides between any two ballots that it tells apart. This is the *linear regime*. For scoring rules it is the calculus of pivotal events of Myerson and Weber (1993), where g_u is the vector of coefficients c(x) of *The Common Rationale*, Section 2. Stated through the count, it holds for every method, with whatever events decide its outcome. In a corner the voter maximises several such linear functions one after another.

The regime fails where one ballot is not small against the uncertainty: in small electorates and with sharp knowledge of the other ballots. The windows of *Score and Approval*, Section 2, are of that kind.

## 2. Best replies are vertices

The *ballot polytope* of a method is the convex hull of the count vectors of its ballots (the smallest convex set that contains them). Its *vertices* are the count vectors that are not averages of others. *(Term introduced here. For Borda the polytope is the permutohedron; for approval and score it is a cube seen along its diagonal.)*

**Proposition 2.** In the linear regime:

1. some best reply is a vertex, and a unique best reply is always a vertex;
2. a ballot whose count vector is not a vertex is a best reply only for a voter to whom several vertices are equally good, which a slight change of utilities or beliefs removes;
3. every vertex is the unique best reply for some gradient g.

*Proof.* A linear function on a polytope takes its maximum on a face, and every face contains vertices; a point that is not a vertex and is a maximiser lies inside a face of dimension at least one, on which the function is constant. For 3, a vertex of a polytope is the unique maximiser of some linear function. In a corner the same holds step by step, each step on the face left by the one before. ∎ *(Proved. Whether the gradient of statement 3 arises from some poll and some utilities depends on the method.)*

So under the common rationale a method offers its voters, in effect, only the vertices of its ballot polytope. The number of vertices bounds what a strategic ballot can say, as the number of ballots bounds what a ballot can say at stage 1.

| Method | Ballots (m = 3, 4) | Vertices (m = 3, 4) | Centrally symmetric |
|---|---|---|---|
| Plurality | 3, 4 | 3, 4 | no |
| Cumulative voting, 3 points | 10, 20 | 3, 4 | no |
| Approval | 8, 16 | 6, 14 | yes |
| Score 0 to 2 | 27, 81 | 6, 14 | yes |
| Borda, strict rankings | 6, 24 | 6, 24 | yes |
| Borda, equal ranks with averaged scores | 13, 75 | 6, 24 | yes |
| Borda, truncated ballots (unranked candidates get 0) | 15, 64 | 9, 40 | no |
| Margins only, strict rankings | 6, 24 | 6, 24 | yes |
| Margins only, equal ranks | 13, 75 | 6, 24 | yes |
| First preferences and margins (BTR-plurality), strict rankings | 6, 24 | 6, 24 | no |
| The same, candidates ranked equal at the top share one first preference | 13, 75 | 6, 24 | no |
| The same, each gets a whole first preference | 13, 75 | 10, 41 | no |

*(Computed by linear programming, part 1 of the script. The vertices of approval are the 2^m − 2 ballots that approve some and not all candidates; those of Borda and of the margins are the m! strict rankings.)*

## 3. Which changes of design matter

**Proposition 3.** Let two methods have the same count and the same rule from the count to the outcome, and let their ballot polytopes have the same vertices. Then in the linear regime, at every belief about the count, every voter with a unique best reply adds the same count vector under both. The strategic counts, the self-confirming beliefs and the outcomes are the same. *(Proved, from Proposition 2; the polls of the two methods are matched as beliefs about the count.)*

A change of the ballot that adds ballots without adding vertices therefore changes nothing at stage 2, however much it adds at stage 1:

- **Score and approval.** Intermediate scores are averages of approval ballots. This is the reduction of *Score and Approval*, Section 1, now for any belief about the totals and not only for weights of pairwise ties.
- **Cumulative voting and plurality.** Points spread over several candidates are averages of ballots that give all points to one.
- **Equal ranks.** Where a ballot with an equal rank is counted as the average of the strict rankings it lies between, it is not a vertex: Borda with averaged scores, every method that reads only the margins (a pair ranked equal adds nothing to its margin), and BTR-plurality, or instant runoff with three candidates, when candidates ranked equal at the top share one first preference. Leaving candidates unranked at the bottom is a case of this, where they are counted as ranked equal.

A change that adds vertices can matter:

- **Whole first preferences.** If each of the candidates ranked equal at the top gets a whole first preference, the ballots with equal tops are new vertices (10 against 6 for three candidates, 41 against 24 for four).
- **Truncated Borda.** If unranked candidates get no points and the ranked ones get m − 1, m − 2 and so on, a ballot that names one candidate is a new vertex: it sets that candidate further apart from the rest than any full ranking can.
- **Approval after plurality**, with 2^m − 2 vertices in place of m, and **score in place of Borda**, where the vertices are different sets.

So equal rankings matter under the common rationale exactly when a ballot with an equal rank counts for more than the average of the strict ballots it lies between. *(From Proposition 3 and the table; large electorates.)*

*Check in the smooth model.* Three candidates, Dirichlet beliefs around the sincere shares, rankings with equal ranks allowed, 1600 voters (*computed*, part 3). With shared first preferences under BTR-plurality, and under a rule that reads the margins only, the voters whose best reply has an equal rank fall from 72 and 67 to 17 and 29 as the number of samples grows from 10 000 to 160 000, and their gain in expected utility falls to less than 0.005 per cent of what is at stake for them between strict ballots: sampling noise among ballots that are equally good. With whole first preferences 210 to 260 of the 1600 voters (13 to 16 per cent) have a best reply with an equal rank at every number of samples, and gain about 0.3 per cent of what is at stake: a small gain, but one that does not go away.

## 4. Opposite voters

A polytope is *centrally symmetric* if with every vertex v it has the vertex c − v, for one fixed vector c.

**Proposition 4.** In the linear regime a method keeps opposite voters equal (README, Section 6) at every belief and for all voters with unique best replies exactly when its ballot polytope is centrally symmetric. If a ballot and its reverse together have the count of the empty profile, as the Equality Criterion asks, the polytope is centrally symmetric.

*Proof.* Opposite voters have gradients g and −g (Proposition 1). On a centrally symmetric polytope the maximiser of −g is c − v when the maximiser of g is v, so the two ballots add c together. Conversely, if the two maximisers add up to the same c for every g, then every vertex v, being the maximiser of some g, has c − v as a vertex. For the last statement, τ(b) + τ(b̃) is the same vector for every ballot b, so the set of count vectors is symmetric and its hull is. ∎ *(Proved. As in Proposition 2, the converse speaks of all gradients, not only of those that arise from polls.)*

So approval, score, Borda and every method that reads only the margins keep opposite voters equal at every poll in the linear regime, not only in their corners. This extends *Plurality and Approval*, Proposition 5, part 3, from approval to all of them. The polytope of plurality is a simplex, which is not centrally symmetric for three or more candidates; in plurality's corner the gradient lies along the edge between the two front-runners, and an edge is symmetric. The first preferences in the count of instant runoff and of BTR-plurality break the symmetry in the same way.

## 5. Reading

At stage 2 a method enters only through the vertices of its ballot polytope and its rule on the count. The changes of design met in the pair notes are then of three kinds:

- *more ballots, the same vertices*: approval to score, strict rankings to rankings with averaged equal ranks. Nothing changes in large electorates;
- *other vertices*: plurality to approval, Borda to score, shared to whole first preferences. The strategic ballots change, and the pair has to be examined;
- *the same ballots, another count or rule*: instant runoff to BTR-plurality. The vertices are the same where the counts agree (three candidates), and the difference lies in which vertex a voter picks.

*(Interpretation.)*

## 6. Open questions

1. Which vertices are used. Proposition 2 bounds the strategic ballots by the vertices; the gradients that arise from polls and utilities may reach only some of them, as in the corner of approval, where only the ballots of the leader rule occur. A description of the reachable vertices per method would give the strategic ballot space exactly.
2. Small electorates. Outside the linear regime interior ballots can be best (the windows of score voting). How fast does the share of such voters fall with the size of the electorate, for score and for rankings with equal ranks?
3. Does adding vertices ever lower a method in the order? Away from the corner the plurality ballot keeps information about intensities that the approval ballot lacks (*Plurality and Approval*, Section 11), although approval's vertices include plurality's.
4. Whole first preferences in BTR-plurality and instant runoff: a pair of its own, strict against whole equal tops, with self-confirming polls and the worst case.

## References

- Myerson, R. B. and Weber, R. J. (1993). A theory of voting equilibria. *American Political Science Review* 87, 102–114.
