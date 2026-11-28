---
title: "What a Ballot Can Carry"
subtitle: "A ladder for comparing voting methods under strategy (draft)"
author: "Kōmyō (Hiveism) and Claude (Anthropic)"
date: 2026-11-28
abstract: |
  Voting methods are usually compared by criteria they pass or fail, or by simulated outcomes. We compare them by information: what a method's ballots and its way of counting can hold about the electorate when every voter responds to the same poll in the same way. The count of a method is the coarsest additive summary of ballots that determines the outcome, and at a fixed poll it is a linear map of the electorate. This gives an exact order between methods, a function between their counts, and a set of bounds that need no simulation. In a large electorate a best reply is a vertex of the *ballot polytope*, the convex hull of what single ballots add to the count; for scoring rules this is known (Núñez and Laslier 2014), and stated through the count it holds for every method. A method can tell whether the leader of a poll is the Condorcet winner only if its count holds the leader's row of pairwise margins, which takes $2^{m-1}$ vertices and rank $m-1$ for $m$ candidates; naming the Condorcet winner without help from the poll takes the whole majority relation, $m!$ vertices and rank $m(m-1)/2$. Plurality cannot reach the second level, no method that counts totals can pass it, and approval in the limit of a close two-way race reaches it exactly. For methods that count totals, treating a voter and the opposite voter as cancelling is necessary for reaching it. Each level also takes uncertainty: a voter who knows the other ballots reveals at most one comparison, under any method. For the utilitarian target, no ballot reveals the scale of a voter's utilities, a count of totals is a sum of utilities normalised by the shape of the ballot polytope, and the shape that serves the majority target reveals no intensity. Honest voting is the best reply of an uninformed voter for several methods, and polls move voters from that end towards the strategic one. Computations for three candidates under one model of beliefs agree: plurality is far behind four other methods under both targets, and those four are not ordered.
documentclass: article
mainfont: "Libertinus Serif"
mainfontoptions:
  - FallbackFonts={DejaVu Sans}
---

\newpage

\tableofcontents

*Draft, November 2026. First assembly of the working notes in `notes/strategic-information/`, which hold the details, the computations and the individual comparisons of methods. Statements are marked as cited, proved, computed, or interpretation.*

## 1. Introduction

Two kinds of statement are made about voting methods. Some say that a method is worse than another without qualification: plurality, for instance, can elect a candidate whom a majority ranks last, and nothing is gained in exchange. Others describe trade-offs: by the theorems of Arrow and of Gibbard and Satterthwaite no method has every desirable property, and among good methods the choice depends on what is wanted. The first kind of statement concerns methods below a frontier, the second kind methods on it. This paper proposes a way of telling the two apart that does not depend on a list of criteria or on a particular simulation.

The idea is to ask what a method can know. A ballot is a message, and a method reads the messages through its count. Under honest voting the capacity of the ballot and the count is all there is to compare. Under strategic voting the messages are chosen, and a method may be offered much less than its ballot could hold: under score voting a strategic voter in a large electorate uses only the highest and the lowest score. We therefore compare methods at two stages, what the ballots and the count can carry and what they carry when every voter follows the same strategic rationale, and we ask of each method what is the most that could be done with what it carries, and what is the worst it does.

The comparison has two axes that are not of the same kind (Section 7). On one, voters are honest and the natural target is the candidate with the largest total utility. On the other, voters respond to polls, and the target that strategy can still serve is the majority relation. The first is the ideal and cannot be sustained; the second is where the first ends up. A method is described by what it holds at each end.

The main results are bounds (Sections 4 to 6). They form a ladder of three levels, each with a price in the method's ballots, in its count and in the voters' uncertainty. Several known facts find a place on it: that plurality supports two candidates, that approval voting needs the right poll to find a Condorcet winner, that a Condorcet method can do without one. Some facts seem to be new: that the level of approval is the most any method that adds up scores can reach, that for such methods the cancelling of opposite voters is a condition for reaching it, and that under certainty about the other ballots no method reveals more than one comparison.

## 2. The setting

There are $m$ candidates and a large number of voters. A method has a set of *ballots*, and a rule that chooses a winner from the ballots cast. We leave ties aside.

**The count.** A profile of ballots is recorded by its histogram. A summary of profiles is additive if its value on two electorates together is the sum of its values on each. The *count* of a method is the coarsest additive summary that determines the outcome: two sets of ballots have the same count when adding either to any profile gives the same winner. For plurality, approval, score and Borda the count is the candidates' totals, up to a number added to all of them; we call these the methods that count totals. For a method that depends only on pairwise margins the count is at most the margins. For instant runoff with three candidates it is the whole histogram of rankings. What a ballot $b$ adds to the count is its *count vector* $\tau(b)$. Without additivity this notion is the compilation of the votes of a subelectorate (Chevaleyre et al. 2009; Xia and Conitzer 2010).

**Types and the strategic count.** A voter's *type* is what the voter's ballot depends on: the ranking of the candidates and, where they matter, the utilities. A *poll* is a belief about the other ballots, shared by all voters. At a poll every type casts a best reply, and the *strategic count* is the count of these ballots. Since the count is additive, the strategic count is a linear map $M$ of the histogram $h$ of types: the column of $M$ for a type is the count vector of its ballot. We group types into finitely many classes on which the ranking and the ballot are constant, for the voter and for the *opposite* voter, whose utilities are the negatives.

**The order.** The map from the electorate to the strategic count is an experiment in the sense of Blackwell (1953), and one experiment is at least as informative as another, for every decision problem at once, exactly when the second can be produced from the first. For counts without chance this means that one is a function of the other.

**Proposition 1.** At a poll, the strategic count of method $A$ is a function of that of method $B$ on every profile exactly when every row of $M_A$ is a combination of rows of $M_B$.

*Proof.* If $M_A = L M_B$ for a matrix $L$, the claim is clear. Conversely, a vector $v$ of whole numbers with $M_B v = 0$ is the difference of two histograms with the same count under $B$, hence under $A$, so $M_A v = 0$. The matrices have whole entries, so such $v$ span the kernel of $M_B$, which therefore lies in the kernel of $M_A$. $\square$ (Checked in Lean, `lean/StrategicCount.lean`.)

The *rank* of $M$, not counting the size of the electorate, is the number of independent numbers about the electorate that the strategic count keeps.

**Targets and the worst case.** A target says how good each candidate would be as winner. We use two: the *majority target*, under which the Condorcet winner is the acceptable winner where there is one, and the *utilitarian target*, the total utility of the winner. A poll is *self-confirming* for a method at a profile if the strategic ballots reproduce it; these are the voting equilibria of Myerson and Weber (1993). The *best case* of a method is the best use any rule could make of its strategic count, and Proposition 1 compares best cases. The *worst case* is the worst winner the method's own rule elects at a self-confirming poll.

**The rationale.** All methods are played by voters who follow one rationale: a model of the voter's uncertainty turns the poll into the likelihood of the events in which one ballot decides the outcome, and the voter maximises expected utility. We use the *linear regime*: the electorate is large and the voter's uncertainty about the count is spread over many ballots, so that the value of a ballot $b$ to a voter with utilities $u$ is, to first order, linear in its count vector,

$$\text{value of } b \;=\; g_u \cdot \tau(b),$$

where $g_u$ is the gradient, at the believed count, of the expected utility of the winner. The gradient is linear in the utilities, so that the opposite voter has gradient $-g_u$. For scoring rules this is the pivotal calculus of Myerson and Weber. Some results are proved in a *corner* of the regime, in which one pivotal event dominates another; the corner of approval and plurality is a race of a leader and a runner-up in which every candidate's most likely tie is with the leader (Laslier 2009 for approval). The corners are separate assumptions for each method and are named where they are used.

## 3. Best replies are vertices

The *ballot polytope* of a method is the convex hull of the count vectors of its ballots.

**Proposition 2.** In the linear regime a unique best reply is a vertex of the ballot polytope, and every vertex is the unique best reply for some gradient. Two methods with the same count, the same rule, and the same vertices up to a factor have the same strategic counts, self-confirming polls and outcomes.

*Proof.* A linear function on a polytope is maximal on a face; a unique maximiser is a vertex, and each vertex is the unique maximiser of some linear function. $\square$

For methods that count totals this is the result of Núñez and Laslier (2014), whose extremal ballots are the vertices. Through the count it applies to any method, and it sorts changes of ballot design into those that can matter under strategy and those that cannot. Intermediate scores are averages of approval ballots, so score voting counts as approval does; points spread over several candidates under cumulative voting are averages of ballots for one candidate, so cumulative voting counts as plurality does. Allowing equal ranks changes nothing wherever a ballot with an equal rank is counted as the average of the strict rankings it lies between: under Borda with averaged scores, under every method that reads only the margins, and where candidates ranked equal at the top share one first preference. It can matter where such a ballot counts for more than that average, as when each of the candidates ranked equal at the top receives a whole first preference: the ballot polytope then has 9 vertices instead of 6 for three candidates (computed). Counting a tie as nothing for either side, as under winning votes, is also not counting it as the average, and makes the ballots with equal ranks vertices (computed in the Ballot Front Finder Lab). The number of vertices bounds what a strategic ballot can say, as the number of ballots bounds what an honest one can.

## 4. The ladder

Fix a poll with leader $a$. For another candidate $x$ let $\mu_x$ be the margin of $a$ over $x$ among the voters' true preferences. The leader is the Condorcet winner exactly when all $\mu_x$ are positive. A method *certifies its leader* at the poll if its strategic count determines the sign of every $\mu_x$. If it does not, there are two electorates that the method cannot tell apart, in one of which the leader is the Condorcet winner and in the other of which the leader is beaten; and if the poll is self-confirming at one of them it is at the other.

**Lemma 3.** Suppose every ranking occurs among the types. A method certifies its leader at a poll exactly when every $\mu_x$ is a combination of the rows of $M$ and the size of the electorate.

*Proof.* One direction is clear. For the other, if $\mu_x$ is not such a combination there is a vector $v$ of whole numbers with $Mv = 0$, entries adding to zero, and $\mu_x(v) \neq 0$. Take a profile $h$ in which every type occurs often enough and every ranking has the same number of voters, so that all its margins vanish. Then $h + v$ and $h - v$ have the same strategic count, and $a$ beats $x$ in one and loses in the other. $\square$ (Checked in Lean for any family of comparisons, `lean/Certification.lean`.)

**Proposition 4 (the leader's row).** If a method certifies its leader at a poll, then (i) the ballot of a voter determines the set of candidates the voter prefers to the leader, so that at least $2^{m-1}$ different count vectors are in use, and (ii) the strategic count has rank at least $m-1$. If the method counts totals, its strategic count is then exactly the leader's row of margins, up to a change of coordinates.

*Proof.* (i) By the lemma $\mu_x$ is a function of the column of $M$, so two types with the same ballot agree on $x$ against $a$; the sets of candidates preferred to $a$, over all rankings, are all subsets of the others. (ii) The $m-1$ margins are independent functions of the histogram of rankings. A count of totals has $m-1$ numbers, so the two spaces coincide. $\square$ (The first half of (i), that the ballot determines the set of candidates preferred to the leader, is checked in Lean, `lean/Certification.lean`; the count $2^{m-1}$ and (ii) are not.)

The same argument applies to any set of comparisons. Let $G$ be a graph on the candidates. A method that certifies the majority comparison on every edge of $G$ has ballots that reveal the voter's preference on every edge; it uses at least as many count vectors as there are ways of directing the edges of $G$ without a cycle; and its count has rank at least the number of edges. For all pairs this is $m!$ count vectors and rank $m(m-1)/2$.

**Proposition 5 (naming the winner).** If a method does not certify the comparison of some pair at a poll, there are two electorates with the same strategic count and different Condorcet winners.

*Proof.* Take $h \pm v$ as in the lemma for the pair $x, y$, and add to both the same voters who rank $x$ and $y$ above all others, half with $x$ first and half with $y$ first, in sufficient number. $\square$

| What the strategic count certifies | Count vectors in use | Rank | Reached by |
|---|---|---|---|
| One comparison | $2$ | $1$ | every method |
| The leader's row | $2^{m-1}$ | $m-1$ | approval and score in their corner; the most a count of totals can hold |
| The whole majority relation | $m!$ | $m(m-1)/2$ | only rankings with a count that contains the margins |

Three consequences follow without computation.

*Plurality is below the second level.* It has $m$ ballots, fewer than $2^{m-1}$ for three or more candidates, and certifies its leader at no poll, in any electorate and under any beliefs. Cumulative voting, with as many vertices, is in the same position in the linear regime. That plurality has self-confirming polls led by candidates who are not Condorcet winners, one for every pair of which one candidate beats the other in its corner, is what the bound allows.

*The second level is the ceiling for counts of totals, and approval reaches it.* In its corner the best approval ballot approves the leader if preferred to the runner-up and any other candidate if preferred to the leader. The ballot is in one-to-one correspondence with the set of candidates the voter prefers to the leader, the tallies are the leader's row, and the only self-confirming poll has the Condorcet winner as leader (Laslier 2009; checked in Lean, `lean/LeaderRule.lean` for the counts and the self-confirming polls and `lean/StrategicInformation.lean` for the best ballot in the corner, with the order of the ties as an assumption. Laslier derives that order from a model of ballot mistakes; exact computations in the notes confirm the derivation for the ties of the two front-runners and not for those of the other candidates, so we state the order as an assumption). By Proposition 4 no method that adds up scores holds more about the majority relation at one poll. Borda, in its corner, holds $m-2$ numbers and does not certify its leader.

*The second level depends on the poll.* By Proposition 5 a method on it can confirm a leader who is the Condorcet winner and reject one who is not, but cannot say who the Condorcet winner is. The right leader has to come from the poll, or from a sequence of polls: with approval ballots, a walk of polls in which a leader who has led before is not eligible again reaches the Smith set within $2(m-1)$ rounds (proved in the notes and checked in Lean, `lean/MemoryWalk.lean`). Only the third level is free of the poll, and its price is that the strategic ballot reveals the voter's whole ranking.

The count of totals is taken as defined in Section 2, up to a number added to all totals, which is what the method's rule can use. An observer of the published totals has one number more, and the statements about counts of totals then hold with $m$ in place of $m-1$.

## 5. Opposite voters

The Equality Criterion asks that a ballot together with its reverse never changes the outcome: in our terms, that the pair has the count of no ballots at all. Approval, score, Borda and every method that reads only the margins satisfy it; plurality as a rule on rankings and instant runoff do not. Its strategic form is that a voter and the opposite voter together add the same to the strategic count, whoever they are; we say the method *keeps opposite voters equal* at the poll.

**Proposition 6.** In the linear regime a method whose ballot polytope is centrally symmetric keeps opposite voters equal at every poll, and a method that satisfies the Equality Criterion has a centrally symmetric ballot polytope.

*Proof.* Opposite voters have gradients $g$ and $-g$, whose maximisers on a centrally symmetric polytope add up to a constant. If $\tau(b) + \tau(\tilde b)$ is the same for every ballot $b$ with reverse $\tilde b$, the set of count vectors is symmetric. $\square$

Both targets depend on the electorate only through functions on which opposite voters cancel: a pair of opposite voters changes neither a margin nor a difference of total utilities. Call such functions *odd*.

**Proposition 7.** Let $d$ be the rank of the strategic count at a poll and $e$ the rank of what pairs of opposite voters add to its rows, beyond a constant. The odd functions in the row space of $M$ have dimension $d - e$.

*Proof.* Rank and nullity of the map that sends a row to what a pair of opposite voters adds to it. $\square$ (Checked in Lean, `lean/OppositeVoters.lean`.)

Every independent way in which opposite voters fail to cancel uses up one of the numbers the count keeps, on something neither target depends on. What follows depends on the room the count has.

**Corollary 8.** A method that counts totals and certifies its leader at a poll keeps opposite voters equal there.

*Proof.* By Proposition 4 its row space is spanned by the margins, which are odd. $\square$

So for methods that count totals the strategic form of the Equality Criterion is a ceiling: one that fails it at a poll is below the level of approval there. It is necessary and not sufficient, since Borda satisfies it. For methods that count more it is a cost without a ceiling. Instant runoff with three candidates counts five numbers where certification takes two; it does not keep opposite voters equal, some of its numbers go to functions that are not odd, and enough remain: in its corner every self-confirming poll elects the Condorcet winner (proved in the notes for three candidates). What failing the criterion leaves such a method is an outcome that can depend on how many pairs of opposite voters there are, which neither target can justify.

## 6. What revealing takes

The bounds of Section 4 concern the method. A third requirement concerns the voters' beliefs.

For every ballot $b$ let $P(b)$ be the lottery over winners that the voter expects when casting $b$. The value of $b$ is $u \cdot P(b)$, exactly and for every method, so the voter chooses from a *menu* of lotteries and a unique best choice is a vertex of the menu's convex hull. A ballot *reveals the comparison* of candidates $i$ and $j$ if voters who choose the same lottery agree on $i$ against $j$.

**Proposition 9.** If the comparison of $i$ and $j$ is revealed, a voter close to indifferent between $i$ and $j$ who changes sides moves between two lotteries that differ only in the chances of $i$ and $j$.

*Proof.* The utilities for which a given lottery is best form a cone, and the wall $u_i = u_j$ cuts through the inside of none. Near a point of the wall there is one cone on each side, with lotteries $v$ and $v'$ equally good on the wall; so $v - v'$ is orthogonal to the wall, a multiple of $e_i - e_j$, where $e_i$ is the lottery that elects $i$ for sure. $\square$

A comparison is revealed where its race is kept apart from the others. Where marking $i$ above $j$ would also move the chances of a third candidate, some voters let the third candidate decide how they mark $i$ and $j$.

**Proposition 10.** Let the method choose a winner without chance, and let the voter's belief give positive probability to $k$ possibilities for the other ballots. The menu has at most $m^k$ lotteries. Under certainty the voter chooses the best of the candidates who can still win, and reveals the comparison of $i$ and $j$ only if those two are the only such candidates.

*Proof.* A lottery is determined by the winner in each of the $k$ possibilities. Under certainty, if a third candidate can win, the voters with that candidate as favourite are on both sides of $i$ against $j$ and choose alike. $\square$

Revealing the leader's row therefore takes at least $(m-1)/\log_2 m$ possibilities held open, and the whole ranking at least $\log_2 m!\,/\log_2 m$. A voter who knows the other ballots has nothing to say but which attainable winner is best. Everything a method learns beyond one comparison it learns from voters who are unsure of the outcome, whatever the method.

The theorem of Gibbard (1973) and Satterthwaite (1975) enters as follows. If a way of filling in the ballot from the ranking alone were a best reply at every belief, the method composed with it would be a rule on rankings that no voter can manipulate, hence dictatorial if at least three candidates can win. So no method has a revealing ballot that is the same at every belief; and by Proposition 10 none reveals more than one comparison at sharp beliefs. The top of the ladder is reached only at beliefs of a particular shape. Borda is an example: in the linear regime its ballot reveals the whole ranking exactly at the belief in which all pairwise ties are equally likely, where the sincere ranking is the best reply. Its count does not keep what the ballots reveal there, since it adds them up to $m-1$ numbers. The third level asks for both a menu that makes voters reveal their rankings and a count that keeps the margins.

## 7. The utilitarian target and the honest axis

**Proposition 11.** Under every method and at every belief, a voter's best replies are unchanged when the utilities are multiplied by a positive number or shifted by a constant.

*Proof.* The value of a ballot is $u \cdot P(b)$, and the order of these values is the same for $\lambda u + c$ with $\lambda > 0$. $\square$

So no method holds the sum of the voters' utilities; what can be held is a sum of utilities brought to a common scale voter by voter. For a method that counts totals the scale is fixed by the ballot polytope $K$. In the linear regime the voter casts the point of $K$ furthest in the direction of the gradient, and at the belief in which all pairwise ties are equally likely the gradient is the utility vector with its mean subtracted.

**Proposition 12.** At that belief a method that counts totals elects the candidate with the largest sum of $N_K(u)$, the point of $K$ furthest in the direction of the voter's utilities: the candidates above the voter's mean for approval and score, the ranking for Borda, the favourite for plurality, and the utilities with mean zero and variance one if $K$ is a ball.

A polytope with $V$ vertices reveals one of $V$ sets of directions. A ballot reveals the direction itself only if the boundary of $K$ has no corners. Finer scores do not approach this, since they add no vertices; a round set of ballots would, for instance score vectors with a fixed sum of squared deviations from their mean. Its ballot polytope is centrally symmetric.

**Proposition 13 (a trade-off).** A method that counts totals and certifies its leader at a poll has ballots that depend on the utilities only through the set of candidates preferred to the leader, and reveals no intensity there. A method whose ballots reveal the direction of the gradient does not certify its leader.

*Proof.* By Proposition 4 the strategic count is an invertible linear function of the margins, so what a voter adds to it is determined by the voter's side on each margin. $\square$

Among counts of totals the two targets pull the ballot polytope apart: the majority target wants the corners of the cube, the utilitarian target no corners. Neither end is below the other.

**Honest voting.** Under honesty a ballot is a report, with the same count. Score voting with a fine scale holds the sum of utilities scaled to the range from 0 to 1, the relative utilitarianism of Dhillon and Mertens (1999): with scores $0$ to $k$ the honest winner is within $1/k$ per voter of the best. A ranking, an approval ballot above the mean and a favourite are reductions of that report, so that on the honest axis the order of methods is the order of what their ballots can carry.

**Proposition 14.** In the linear regime, at the belief in which all pairwise ties are equally likely, the honest ballot is a best reply under plurality, approval (above the mean; Merrill 1979, Weber 1978), Borda and round ballots. An honest score ballot with an intermediate score is the unique best reply at no belief.

That belief is the belief of a voter who knows nothing about the race. For these methods honesty is the strategy of the uninformed, and the honest count is the strategic count at the empty poll. A voter's belief lies between knowing nothing and knowing the other ballots; at the first end the ballot reveals the most, at the second one comparison. Polls move voters from the first towards the second. The empty poll does not confirm itself, since once tallies are known the ties are no longer equally likely, and the polls that do confirm themselves are, in the corners, on the side of the majority relation. The two axes are the ends of one line, and a method is described by what it holds at each end. Score voting has the widest gap: honest it holds the utilitarian sum, under strategy it is approval. No method leads at both ends. *(The direction is interpretation.)*

## 8. Computations

Three sets of computations stand beside the bounds; the notes give them in full.

**Corners.** For pairs of methods in their corners: plurality's strategic count is contained in approval's (ranks $1$ and $m-1$), and for three candidates in instant runoff's; score is equivalent to approval; Borda's count is contained in score's for three candidates and unordered with it from four; instant runoff and a Condorcet method with the same ballots (bottom-two runoff in the order of first preferences) both elect the Condorcet winner at every self-confirming poll, for three candidates.

**One model for five methods.** With three candidates, beliefs spread around the poll (after Eggers and Nowacki 2024), and polls moved towards the best replies until they come to rest, on forty profiles per setting: plurality has a resting poll with a winner other than the Condorcet winner at 22 to 36 of 36 to 40 profiles, approval, Borda, instant runoff and bottom-two runoff at 1 to 7, with one exception of 12; under the utilitarian target the picture is similar. The four are not ordered. Approval's resting polls are not all led by the Condorcet winner, and Borda's polls do come to rest; the sharper statements for these two belong to their corners.

**Honest against strategic.** With honest voters on 4000 profiles, instant runoff and bottom-two runoff elect the Condorcet winner most often (96 to 100 per cent) and the score ballots the winner by normalised utilities (93 to 100 per cent). On the profiles of the previous paragraph under impartial culture, plurality, approval, Borda and instant runoff give at least as much total utility at their resting polls as with honest voters, as Lehtinen (2007, 2008) found by simulation: a coarse honest ballot leaves intensities out, and a strategic ballot brings some back.

These computations are small, for three candidates, and their strategic outcomes come from chosen starting polls. They show directions and are not estimates.

## 9. Relation to other work

The linear value of a ballot and the notion of a voting equilibrium are Myerson and Weber's (1993). The corner of approval, its best reply and the election of the Condorcet winner are Laslier's (2009). That only extremal ballots are used in large elections, and that rules with the same extremal ballots are strategically equivalent, is Núñez and Laslier (2014) for rules that add up scores; Section 3 restates it through the count. The count without additivity is the compilation of Chevaleyre et al. (2009). The order on experiments is Blackwell's (1953). That strategic voting can raise utilitarian efficiency is Lehtinen's finding. We did not find the ladder of Section 4, the role of opposite voters in Section 5, or the bound from the voters' uncertainty in Section 6 in the literature; our search was short.

## 10. Status and open problems

The propositions are short and proved by hand. Proposition 1, Lemma 3, the first half of Proposition 4 (i) and Proposition 7 are checked in Lean (`lean/StrategicCount.lean`, `lean/Certification.lean`, `lean/OppositeVoters.lean`); the other targets are listed in the repository's Lean roadmap (`lean/roadmap.md`). The results on approval's corner and on the walk with memory are checked in Lean (`lean/LeaderRule.lean`, `lean/StrategicInformation.lean`, `lean/MemoryWalk.lean`).

Open:

1. The third level. At which polls the strategic counts of ranked methods certify the whole majority relation, and how often such polls confirm themselves.
2. More than three candidates for the methods on rankings, in the corners and in the smooth model.
3. Existence of a self-confirming poll for every profile in the smooth model, and the worst case as a frequency with a known error.
4. Round ballots under sharpening beliefs.
5. Whether the dependence on pairs of opposite voters accounts for the profiles at which instant runoff rests on the wrong winner.
6. A bound for the utilitarian target in terms of how well a ballot polytope with $V$ vertices approximates a ball.
7. Other criteria read as bounds, independence of clones first.

## References

*Entries marked † are cited from memory and have not been checked against the original.*

- Blackwell, D. (1953). Equivalent comparisons of experiments. *Annals of Mathematical Statistics* 24(2), 265-272.
- Chevaleyre, Y., Lang, J., Maudet, N. and Ravilly-Abadie, G. (2009). Compiling the votes of a subelectorate. *Proceedings of IJCAI 2009*, 97-101.
- Dhillon, A. and Mertens, J.-F. (1999). Relative utilitarianism. *Econometrica* 67(3), 471-498.
- Eggers, A. C. and Nowacki, T. (2024). Susceptibility to strategic voting: a comparison of plurality and instant-runoff elections. *Journal of Politics*.
- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41(4), 587-601.
- Laslier, J.-F. (2009). The leader rule: a model of strategic approval voting in a large electorate. *Journal of Theoretical Politics* 21(1), 113-136. (Read in the working-paper version of 2006.)
- Lehtinen, A. (2007). The Borda rule is also intended for dishonest men. *Public Choice* 133, 73-90. †
- Lehtinen, A. (2008). The welfare consequences of strategic behaviour under approval and plurality voting. *European Journal of Political Economy* 24(3), 688-704.
- Merrill, S. (1979). Approval voting: a "best buy" method for multi-candidate elections? *Mathematics Magazine* 52, 98-102. †
- Myerson, R. B. and Weber, R. J. (1993). A theory of voting equilibria. *American Political Science Review* 87, 102-114.
- Núñez, M. and Laslier, J.-F. (2014). Preference intensity representation: strategic overstating in large elections. *Social Choice and Welfare* 42(2), 313-340.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10, 187-217. †
- Weber, R. J. (1978). Comparison of voting systems. Cowles Foundation Discussion Paper 498. †
- Xia, L. and Conitzer, V. (2010). Compilation complexity of common voting rules. *Proceedings of AAAI 2010*, 915-920.
