# Bounds from Criteria

*Working note, part of [Strategic Information](README.md), first draft. The pair notes compare methods two at a time, by proof in a corner and by computation outside it. This note asks what can be said without either: which properties of a method put a ceiling on what it can achieve under any rationale in which best replies are vertices of the ballot polytope. Three bounds are proved. The Equality Criterion turns out to be a ceiling for methods that count totals, and a cost without a ceiling for methods that count more. Conventions as in the README; the count, the strategic count M and the ballot polytope as in the README, Section 2, and [The Ballot Polytope](ballot-polytope.md). Nothing here is computed.*

## 1. Certifying the leader

Fix a poll and let a be its leader, the candidate the poll expects to win. For another candidate x, write μ_x for the margin of a over x among the voters' sincere preferences: +1 for every voter who prefers a to x, −1 for every voter who prefers x to a. The leader is the Condorcet winner exactly when every μ_x is positive.

A method *certifies its leader* at the poll if the strategic count determines, for every x, whether a beats x: two profiles with the same strategic count never differ in the sign of a margin μ_x. *(Term introduced here.)* A method that does not certify its leader cannot tell, from what it counts, a profile in which the leader is the Condorcet winner from one in which the leader is beaten. Whether the poll confirms itself depends only on the strategic count. So if the poll is self-confirming at the first profile, it is at the second, with a leader who is not the Condorcet winner.

**Lemma 1.** Suppose every ranking occurs among the types. A method certifies its leader at a poll exactly when every margin μ_x, as a function of the histogram of types, is a combination of the rows of M and the size of the electorate.

*Proof.* If μ_x is such a combination, the strategic count determines it. Conversely, if it is not, there is a vector v of whole numbers with Mv = 0, with entries adding up to zero, and μ_x(v) ≠ 0 (README, Section 2, proof of the Proposition). Let h be the profile with c voters of every type, where c is at least the largest entry of v. All its margins are zero. Then h + v and h − v are profiles with the same strategic count, and a beats x in one and loses to x in the other. ∎ *(Proved.)*

Certification is what the majority target asks of the information: the best case of the README, Section 3, can single out the Condorcet winner at a poll only if the leader is certified there. It is necessary for the guarantee "every self-confirming poll elects the Condorcet winner", by the remark before the lemma, as far as the profiles at which the poll confirms itself include close contests.

## 2. A bound from the number of vertices

**Proposition 2.** If a method certifies its leader at a poll, the strategic ballot of a voter determines the set of candidates that the voter prefers to the leader. With m candidates and every ranking among the types, at least 2^{m−1} different count vectors are in use.

*Proof.* By Lemma 1, μ_x is a combination of rows of M, and the column of M for a type is the count vector of that type's ballot. Two types with the same ballot have the same column and therefore the same value of μ_x, for every x: they agree on whether they prefer x to a. The sets of candidates preferred to a, over all rankings, are all subsets of the other m − 1 candidates. ∎ *(Proved.)*

In the linear regime the count vectors in use are vertices of the ballot polytope (*The Ballot Polytope*, Proposition 2). So a method with fewer than 2^{m−1} vertices certifies its leader at no poll, under any model of beliefs:

- plurality and cumulative voting, with m vertices, for three or more candidates;
- voting for exactly two of four candidates, with 6 vertices where 8 are needed, and in general voting for exactly k candidates wherever the number of such ballots is below 2^{m−1}.

Approval has 2^m − 2 vertices, and the leader rule of its corner uses exactly 2^{m−1} of them, one for each set of candidates preferred to the leader (*Plurality and Approval*, Section 11). The bound is met with nothing to spare. That plurality has self-confirming polls led by candidates who are not Condorcet winners (*Plurality and Approval*, Proposition 2) and keeps them in the smooth model at nearly every profile (*The Smooth Model across Methods*, Section 2) is then no accident of a model: its ballot cannot carry what certification takes.

## 3. A bound from the size of the count

**Proposition 3.** Certifying the leader takes a strategic count of rank at least m − 1, not counting the size of the electorate. A method that counts totals has rank at most m − 1. If such a method certifies its leader at a poll, the row space of its strategic count is exactly the span of the margins μ_x, the row of the leader in the matrix of pairwise counts.

*Proof.* The m − 1 margins μ_x are independent as functions of the histogram of rankings, and by Lemma 1 all lie in the row space of M together with the size of the electorate. Totals up to a number added to all of them are m − 1 numbers. With equality of dimensions the two spaces coincide. ∎ *(Proved.)*

Two consequences for every method that counts totals (plurality, approval, score, Borda, cumulative voting, and any other scoring of ballots):

- *One row is the ceiling.* Such a method can verify that a given candidate is the Condorcet winner and nothing beyond it. It can never hold a second row of the pairwise matrix at the same poll, so it cannot find the Smith set from one poll when there is no Condorcet winner. The walk with memory of *Plurality and Approval*, Section 6, reaches the Smith set by collecting rows over several polls, which is the only way left to a count of this size.
- *Approval's corner is the maximum.* A method that counts totals and certifies its leader has, at that poll, the same strategic count as approval under the leader rule, up to a change of coordinates. In what a count can hold about the majority relation at one poll, no method that counts totals lies above approval in its corner; every one of them holds less or the same. (This is the information half of the order; the worst case is a separate matter.)

Borda in its corner has rank m − 2 (README, Section 5), one short of the m − 1 that certification takes, and so does not certify its leader for any number of candidates. This is the information side of its having no self-confirming poll there (*Borda and Score*, Proposition 3).

## 4. A bound from the Equality Criterion

A row of M gives every type a value r(t), what a voter of that type adds. Write t̃ for the opposite type (utilities negated, or the ranking reversed). The *even part* of r is the function ½(r(t) + r(t̃)), what a pair of opposite voters adds, halved; r is *odd* if its even part is the same for all types, so that pairs of opposite voters enter only through the size of the electorate. The margins μ_x are odd. So is the total utility of one candidate minus that of another. Both targets of the README, Section 3, depend on the profile only through odd functions: a pair of opposite voters changes neither the majority relation nor the order of the candidates by total utility.

A method keeps opposite voters equal at the poll (README, Section 6) exactly when all its rows are odd.

**Proposition 4.** Let d be the rank of the strategic count at a poll, and e the rank of the even parts of its rows, both not counting constants (the size of the electorate). The odd functions in the row space of M form a space of dimension d − e. In particular a method that does not keep opposite voters equal at a poll has fewer than d independent numbers that bear on either target.

*Proof.* Taking the even part, up to constants, is a linear map on the row space. Its kernel is the odd functions in the row space, and its image has dimension e. ∎ *(Proved.)*

Each independent way in which opposite voters fail to cancel uses up one of the numbers that the count keeps, on something that neither target depends on. What follows depends on how much room the count has.

**Corollary 5 (totals).** A method that counts totals and certifies its leader at a poll keeps opposite voters equal at that poll. Equivalently: a method that counts totals and does not keep opposite voters equal at a poll does not certify its leader there.

*Proof.* By Proposition 3 its row space is spanned by the margins, which are odd, so e = 0. ∎ *(Proved.)*

For methods that count totals the strategic form of the Equality Criterion is therefore a ceiling in the sense asked for: every such method that fails it at a poll lies, at that poll, below the bound that approval reaches in its corner. In large electorates a method that passes the Equality Criterion keeps opposite voters equal at every poll (*The Ballot Polytope*, Proposition 4), so among methods that count totals the criterion is necessary for reaching the bound at every poll, though not sufficient: Borda passes it and falls short by Proposition 3. Plurality fails it and reaches the bound nowhere; that it keeps opposite voters equal in its corner does not help, since there it fails by Proposition 2.

**For methods that count more, the criterion is a cost and not a ceiling.** Instant runoff and BTR-plurality with three candidates count the whole histogram, five numbers where certification takes two. They do not keep opposite voters equal (README, Section 6), and by Proposition 4 some of their numbers go to even functions; enough remain, and in their corners both elect the Condorcet winner at every self-confirming poll (*Instant Runoff and Plurality*, Proposition 3; *Instant Runoff and BTR-Plurality*, Proposition 2). Failing the criterion does not put these methods below any bound found here. What it leaves is the even part itself: an outcome that can depend on how many pairs of opposite voters there are, which neither target can justify. Whether that dependence accounts for the profiles at which these methods rest on the wrong winner in the smooth model is open.

**Proposition 6 (the worst case sees what the count sees).** Let a method keep opposite voters equal at every poll, and suppose that what a pair of opposite voters adds to the count, which is then the same for every pair, does not change the summary of the count that a poll reports (the same number added to every total does not change their order). Then adding pairs of opposite voters to a profile changes neither which polls are self-confirming nor who wins at them: its worst case depends on the profile only through the odd functions, like the targets. For a method that does not keep opposite voters equal, pairs of opposite voters can make a poll self-confirming or undo it, at profiles between which neither target sees a difference.

*Proof.* Every pair adds the same vector to the strategic count at a given poll, so the summary is unchanged, and with it the answer to whether the poll is reproduced. The second statement is the definition of failing: some two pairs add different vectors, and the count, on which self-confirmation depends, differs between two profiles with the same odd part. ∎ *(Proved. The second half says that the dependence is possible, not that it occurs at a given poll.)*

## 5. A ladder of ceilings

Lemma 1 and Propositions 2 and 3 are the case of one candidate compared with all others. The same argument gives a bound for any set of comparisons. Let G be a graph on the candidates, its edges the pairs whose majority comparison is in question. A method *certifies G* at a poll if the strategic count determines who beats whom for every edge of G.

**Proposition 7.** If a method certifies G at a poll at which every ranking occurs among the types, then the strategic ballot of a voter determines the voter's preference on every edge of G; at least a(G) different count vectors are in use, where a(G) is the number of ways of directing the edges of G without a cycle; and the strategic count has rank at least the number of edges of G.

*Proof.* As for Lemma 1 and Proposition 2, with the margins of the edges in place of the μ_x. The preferences of a ranking on the edges of G direct them without a cycle, and every such direction comes from a ranking. The margins of different pairs are independent as functions of the histogram of rankings. ∎ *(Proved. The number a(G) is 2^k for a tree with k edges, 2^{m−1} for the star of Proposition 2, and m! for the complete graph.)*

This gives three levels, each with its price in vertices and in rank:

| What the count certifies at a poll | Vertices in use | Rank | Who can |
|---|---|---|---|
| One comparison, the two front-runners | 2 | 1 | every method; plurality in its corner holds exactly this |
| The leader's row: whether the leader is the Condorcet winner | 2^{m−1} | m − 1 | approval and score in their corner; no method with fewer vertices; the most a count of totals can hold |
| The whole majority relation | m! | m(m − 1)/2 | only methods whose ballots can tell all rankings apart and whose count has that rank: ranked ballots with a count that contains the margins |

**Corollary 8.** If a method does not certify the comparison of some pair x, y at a poll, there are two profiles with the same strategic count at that poll and different Condorcet winners. So a method that can name the Condorcet winner from its strategic count at a poll, whoever leads the poll, certifies the whole majority relation there.

*Proof.* Take the two profiles h + v and h − v of Lemma 1 for the pair, and add to both the same voters, who rank x and y above all others, half of them with x first and half with y first, more of them than any margin of v. The counts are still equal, x and y beat every other candidate in both profiles, and x beats y in one and loses in the other. ∎ *(Proved.)*

So the second level is tied to the poll: a method on it can confirm a leader who is the Condorcet winner and reject one who is not, but it cannot say who the Condorcet winner is. The right leader has to come from the poll, which is information from outside the ballots (README, Section 3), or from a sequence of polls, as in the walk with memory. This is the position of approval, and by Proposition 3 of every method that counts totals at best. Only the third level is free of the poll, and its price is that the strategic ballot reveals the voter's whole ranking. With three candidates that means all six rankings in use and rank three; instant runoff has corner polls with rank two (README, Section 2) and is not on the third level there.

*(Interpretation of Propositions 3 and 7 and Corollary 8.)*

## 6. What the bounds settle

| Method | Vertices against 2^{m−1} | Rank against m − 1 | Opposite voters equal | Certifies its leader |
|---|---|---|---|---|
| Plurality, cumulative voting | m, too few from three candidates | at most m − 1; 1 in the corner | only in the corner | at no poll (Proposition 2) |
| Approval, score | 2^m − 2 | m − 1 in the corner | at every poll | in the corner, and this is the most a count of totals can do (Proposition 3) |
| Borda | m! | m − 2 in the corner | at every poll | not in the corner (Proposition 3) |
| Instant runoff, BTR-plurality, three candidates | 6 against 4 | 2 to 5 | at no poll of the corner | not excluded by any bound here |

The first row needs no computation and no model of beliefs beyond the linear regime: plurality is below approval's corner because of what its ballot is. The second and third rows say that among counts of totals the question of the majority target is closed at the top, with approval in its corner as the bound. The fourth row is where bounds of this kind stop, and the pair notes and the smooth model are still needed.

*Limits.* Certification is about the majority target. For the utilitarian target the corresponding functions are the differences of total utilities, which take a continuum of values per voter, and no method with finitely many ballots holds them exactly; a bound for that target has to be about approximation. [Intensities and the Utilitarian Target](intensity.md) gives the counterpart for methods that count totals: what such a method holds is a sum of utilities normalised by the shape of its ballot polytope, and the shape that certifies the leader reveals no intensity. The bounds concern the information a method can hold at a poll. They are ceilings: they do not say that a method reaches its ceiling away from a corner, and approval in the smooth model does not (*The Smooth Model across Methods*, Section 4).

## 7. Open questions

1. The third level of Section 5. [What a Ballot Reveals](revelation.md) shows that no level above the first holds at sharp beliefs, and that the theorem of Gibbard and Satterthwaite excludes a revealing ballot that is the same at every belief. At which polls the strategic counts of instant runoff, BTR-plurality and other ranked methods certify the whole majority relation is still open.
2. The even part of instant runoff and BTR-plurality: the rank e at their corner polls, and whether the profiles at which they rest on a wrong winner are those where the even part decides.
3. Approximate certification, in the smooth model: how far the strategic count of approval is from the leader's row as the beliefs widen, as a number that bounds the worst case.
4. A bound for the utilitarian target: how well the vertices of a ballot polytope can approximate the differences of utilities, and whether central symmetry enters there as it does in Corollary 5.
5. Other criteria read in the same way: independence of clones as a property of the ballot polytope and the count (*Equality of Voters and Alternatives*), and what it bounds.
