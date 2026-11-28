# What a Ballot Reveals

*Working note, part of [Strategic Information](README.md), first draft. [Bounds from Criteria](bounds.md) ends with a ladder: a strategic count can certify one comparison, the leader's row, or the whole majority relation, and the top level asks that the strategic ballot reveal the voter's whole ranking. This note asks when a ballot reveals anything, and how the theorem of Gibbard and Satterthwaite bears on the top of the ladder. The answer has two parts. What a voter reveals is a choice from a menu of lotteries, and the menu is made by the voter's uncertainty: under certainty about the other ballots it reveals one comparison at most, whatever the method. And the theorem of Gibbard and Satterthwaite excludes a revealing ballot that does not depend on the belief. Between the two, the top of the ladder is reached only at beliefs of a particular shape. Everything is proved; nothing is computed. Conventions as in the README.*

## 1. The menu

Fix a method and a voter's belief about the other ballots. For every ballot b let P(b) be the lottery over the candidates that the voter expects when casting b: P(b) gives each candidate the probability of winning. The expected utility of b is u · P(b).

**Proposition 1 (menu).** The voter chooses among the lotteries P(b), and chooses one that maximises a linear function of the lottery given by the utilities. A unique best lottery is a vertex of the *menu polytope*, the convex hull of the P(b). Two ballots with the same lottery are the same to the voter.

*Proof.* The expected utility is linear in the lottery. ∎ *(Proved; exact for every method, electorate and belief. The term menu polytope is introduced here. In a large electorate the menu is the image of the ballot polytope under the gradient of* The Ballot Polytope*, Proposition 1.)*

What a voter can be led to reveal by the incentives of a method is therefore which lottery of the menu the voter likes best. A convention for voters who are indifferent, such as the sincere ballot, reveals more, but not through any incentive, and a voter loses nothing by departing from it.

## 2. Revealing a comparison

A ballot *reveals the comparison* of two candidates i and j, at a belief, if any two voters with unique best lotteries who choose the same lottery agree on whether they prefer i to j.

**Proposition 2.** Suppose the ballot reveals the comparison of i and j. Then:

1. no vertex of the menu polytope is the best lottery both of a voter who prefers i to j and of one who prefers j to i;
2. a voter who is close to indifferent between i and j, and who changes sides, moves from one vertex to another that differs from it only in the probabilities of i and j: the difference of the two lotteries is a multiple of e_i − e_j.

*Proof.* The first statement is the definition. For the second, the utilities for which a given vertex is best form a cone, and by 1 the wall u_i = u_j passes through the inside of none of these cones. So near a generic point of the wall there is one cone on each side, with vertices v and v′, and both are best on the wall between them: u · (v − v′) = 0 for all u in an open piece of the wall. The difference v − v′ has entries adding up to zero and is orthogonal to the wall, so it is a multiple of e_i − e_j. ∎ *(Proved.)*

So a comparison is revealed exactly where the method keeps its race apart from the others: a voter's stake in i against j is exercised on the chances of i and j alone. Where expressing i over j would also move the chances of a third candidate, some voters will let the third candidate decide how they mark i and j, and the ballot stops revealing the comparison.

Revealing the comparisons of a graph G on the candidates takes at least a(G) vertices of the menu polytope, the number of ways of directing the edges of G without a cycle, as in *Bounds from Criteria*, Proposition 7, and now counted in lotteries: 2^{m−1} for the leader against all others, m! for all pairs. When all pairs are revealed and nothing else is, the menu polytope has one vertex for every ranking and all its edges are parallel to differences e_i − e_j, as the permutohedron has (the polytope whose vertices are the rearrangements of 0, 1, …, m − 1).

## 3. Certainty reveals least

**Proposition 3.** Let the method choose a single winner from the ballots, without chance, and let the voter's belief give positive probability to k possibilities for the other ballots. Then the menu has at most m^k different lotteries. Under certainty (k = 1) the lotteries are sure winners, the voter chooses the best candidate among those the ballot can still make win, and the ballot reveals the comparison of i and j only if these two are the only candidates that the voter can make win.

*Proof.* In each of the k possibilities a ballot makes one of m candidates win, and the lottery is determined by these k winners. Under certainty the menu polytope is spanned by sure winners, and a voter's best is the favourite among them. If a third candidate c is among them, voters with c as favourite stand on both sides of i against j and choose the same lottery. ∎ *(Proved.)*

With three or more candidates this puts a price on every level of the ladder above the first:

| Level | Vertices of the menu needed | Possibilities the voter must hold open |
|---|---|---|
| One comparison | 2 | 1: certainty will do, if only two candidates can still win |
| The leader's row | 2^{m−1} | at least (m − 1)/log₂ m |
| The whole ranking | m! | at least log₂ m!/log₂ m |

A voter who knows the other ballots has nothing to say but which of the attainable winners is best. The first level, and with it plurality's corner in which two candidates are in contention, is the whole of what certainty supports. Everything a method learns beyond that it learns from voters who are unsure of the outcome, and it is the spread of their uncertainty over many possible outcomes that gives the menu its vertices. This holds for every method; no property of the method enters. *(Interpretation of Proposition 3.)*

## 4. The theorem of Gibbard and Satterthwaite

The theorem says that a rule which chooses one winner from the voters' rankings, can elect at least three candidates, and gives no voter a reason ever to report another ranking than the true one, is a dictatorship (Gibbard 1973; Satterthwaite 1975†). In the terms of this note:

**Proposition 4.** Let a method choose a single winner from the ballots, without chance. Suppose there is a way of filling in the ballot from the ranking alone, the same at every belief, that is a best reply for every voter whatever the other ballots are, and suppose that at least three candidates can win when all ballots are filled in this way. Then, on the ballots filled in this way, the method is a dictatorship.

*Proof.* Compose the method with the way of filling in the ballot. The result chooses a winner from the voters' rankings, and reporting the true ranking is best whatever the others report. By the theorem it is a dictatorship or elects at most two candidates. ∎ *(Proved, from the cited theorem; this is the argument known as the revelation principle.)*

So the theorem excludes a revealing ballot that is the same at every belief. It does not exclude a ballot that reveals the ranking at some beliefs and in a way that depends on them; Proposition 3 excludes that at sharp beliefs, by counting, and for the second level as well as the third. The two results meet in one picture. At a sharp belief the menu is small, and the voter's best reply is a manipulation in the sense of the theorem: a choice among attainable winners that tells little about the ranking. For the best reply to reveal the ranking the menu must be large, which takes uncertainty, and of the right shape, which by Proposition 2 means that every pair of candidates has a race of its own.

## 5. Where the top is reached

**Borda at the symmetric belief.** In a large electorate, with weights p(x, y) of the pairwise ties (*The Common Rationale*, Section 2), moving one point from j to i on a Borda ballot changes the chance of a third candidate c by p(c, j) − p(c, i). By Proposition 2 the Borda ballot reveals the whole ranking exactly when these all vanish: when all pairwise ties are equally likely. There the best Borda ballot is the sincere ranking, and the menu is a permutohedron. At every other belief some comparison is not revealed. *(Proved for the linear regime, from Proposition 2 and* Borda and Score*, Proposition 1.)* What the ballots reveal there, the count does not keep: Borda adds them up into totals, m − 1 numbers where the whole majority relation takes m(m − 1)/2 (*Bounds from Criteria*, Proposition 7). The top of the ladder asks for both, a menu that makes the voters reveal their rankings and a count that keeps the margins.

**Approval in its corner.** Approving x, to the leading order of the corner, moves chances between x and the leader only. The comparisons of the leader with every other candidate are revealed, which is the second level, and no other comparison is.

**Reading.** The ladder of *Bounds from Criteria* has a third column. A level asks for enough vertices of the ballot polytope, enough rank in the count, and enough uncertainty of the right shape in the voters' beliefs. The first two are properties of the method and are settled once. The third is a property of the poll, and it is where the impossibility theorems enter: no method can make the top level hold at every belief, since at sharp beliefs no level above the first holds, and a method cannot choose the beliefs at which it is used. A method can be judged by how much of the ladder it reaches at the beliefs that its own strategic ballots sustain. *(Interpretation.)*

## 6. Open questions

1. The beliefs at which a method reveals a given set of comparisons, as a region in the space of beliefs, and which of them are self-confirming. For Borda the region for all comparisons is the single symmetric point in the linear regime, and Borda has no self-confirming poll in its corner; is the symmetric belief ever self-confirming?
2. A measure of how far a menu polytope is from revealing a comparison, to make Proposition 2 quantitative in the smooth model: for instance the share of voters, under a culture, whose marking of i and j is decided by a third candidate.
3. The menus of instant runoff and BTR-plurality with three candidates at their resting polls: which comparisons are revealed, and whether BTR-plurality, which reads all margins, reveals more of them than instant runoff.
4. Random rules. Under random ballot the menu polytope is a simplex with one vertex for each candidate at every belief, and the favourite is always revealed; what the ladder looks like for rules that give lotteries, such as maximal lotteries, is not examined here.

## References

- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41(4), 587–601.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10, 187–217. †
