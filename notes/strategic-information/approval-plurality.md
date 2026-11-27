# Plurality and Approval under a Common Rationale

*Working note, part of [Strategic Information](README.md). It compares plurality and approval voting under the common rationale of [The Common Rationale](rationale.md). Conventions as in the README. The checks are in `scripts/information/strategic_information.py`, `ties.py`, `ballot_mistakes.py` and `lost_marks_walk.py`; Propositions 1 to 3, the statement on the Smith set and the steps of Proposition 4 are checked in Lean in `lean/LeaderRule.lean`, with the best replies as definitions; Propositions 5 and 6 and the counting of Proposition 4 in `lean/StrategicInformation.lean`, and Proposition 4 as one statement with the passage from positions to utilities in `lean/MemoryWalk.lean`.*

## 1. Best replies

Preferences are strict. With this rationale the best replies are as follows (proved here; checked by brute force over all ballots in the script):

- **Plurality.** Vote for whichever of a₁ and a₂ you prefer. The tie between them decides alone, since a vote for anyone else has no effect on it.
- **Approval.** Approve a₁ exactly when you prefer a₁ to a₂, and approve every other candidate exactly when you prefer that candidate to a₁. The first tie fixes the ballot on a₁ and a₂ (one of the two approved, not both, since approving both abstains from their comparison). The ties with a₁ then fix every other candidate. This is the leader rule (related to the k-pragmatists of Reijngoud and Endriss 2012, voters who use only the top k of a poll), Laslier's "lexicographic response" (2006, Theorem 1, cited; there derived from his Lemma 2, so in his model it holds for the front-runners but not for candidates ranked third or lower, Section 9). In particular a₂ is approved exactly when it is preferred to a₁. Leader-rule ballots are sincere, and admissible in the sense of Brams and Fishburn (1983): the favourite is always approved and the least preferred candidate never (Laslier 2006, Corollary 1 and Section 1, cited; checked).

## 2. When the poll is tied

(T) needs a poll without ties, as does Laslier's lemma. When two contenders are tied in the poll, a voter cannot know which of two races is pivotal. Suppose the two races are of the same order of likelihood, with some ratio of their probabilities, and every other race involving the candidates concerned is less likely; this is not covered by Laslier's lemma and is assumed here.

- **A tie for second** between x₂ and x₃. The races of a₁ against x₂ and against x₃ weigh together. A voter who prefers a₁ to both approves it, one who prefers both to a₁ does not, and a voter who ranks a₁ between them approves it exactly when the utility of a₁ exceeds the weighted mean of the utilities of x₂ and x₃. Every other candidate is decided against a₁ as before.
- **A tie for first** between a₁ and a₂. The voter approves the preferred of the two and not the other. Every other candidate x is weighed against both: approved if preferred to both, not if both are preferred to it, and otherwise approved exactly when its utility exceeds the weighted mean of those of a₁ and a₂.

In both cases the ballot stays sincere, and intensities of preference enter only for candidates ranked between the tied contenders. *(Proved here under the stated assumption.)* Laslier observes that without a Condorcet winner every equilibrium score vector has a tie between the two first candidates or among the second-ranked ones (2006, after Corollary 2, cited). Intensities therefore enter exactly where the majority relation cycles: where ordinal information runs out, the rational ballot draws on cardinal information. *(Interpretation.)*

## 3. What the ballots carry

Write N(x > y) for the number of voters who prefer x to y.

**Proposition 1.** Under the common rationale, for a poll with leader a₁ and runner-up a₂:

1. a₁ has the tally N(a₁ > a₂) and a₂ the tally N(a₂ > a₁), under plurality and under approval alike;
2. every plurality ballot lies inside the approval ballot of the same voter, and the plurality ballot is a function of the approval ballot: a₁ if a₁ is approved, a₂ otherwise;
3. every other candidate x has the tally N(x > a₁) under approval, and none under plurality.

*Proof.* A voter votes for a₁ under plurality exactly when they prefer a₁ to a₂, which is exactly when they approve a₁; the same holds for a₂. This gives 1 and 2. Under approval, x outside the pair is approved exactly by the voters who prefer x to a₁, which gives 3. ∎

The approval tallies in 1 and 3 are Laslier's Theorem 2 (2006, cited), stated there for equilibrium score vectors and proved from the best replies alone, so that it holds for any poll. The comparison with plurality is the addition here. Parts 1 and 2 use (T) only for the front-runners, so they also hold in Laslier's model of ballot mistakes; part 3 uses the rest of (T) (Section 9).

*Reading.* In the matrix of pairwise counts, strategic plurality reveals one entry, the comparison of the two front-runners. Strategic approval reveals that entry and the whole row of the leader: how every candidate fares against a₁. In the terms of Blackwell (1953), the strategic approval ballot is sufficient for the strategic plurality ballot (the plurality ballot is a garbling of the approval ballot, see the [README](README.md), Section 2), so any use that can be made of the strategic plurality ballots can also be made of the strategic approval ballots, and not conversely. This is the first step of the [README](README.md), Section 1, for this pair, for a fixed poll. *(Proved; the interpretation as a Blackwell comparison is ours.)*

## 4. Which polls confirm themselves

The poll is not given from outside. A poll is *self-confirming* if the tally it produces ranks a₁ first and a₂ second, strictly (a voting equilibrium in the sense of Myerson and Weber, an outcome that justifies the perceptions it came from; Laslier's equilibrium score vector).

**Proposition 2.** Under the common rationale:

1. Under plurality, a poll (a₁, a₂) is self-confirming exactly when a₁ beats a₂ by majority and some voter prefers a₂ to a₁.
2. Under approval, a poll (a₁, a₂) is self-confirming exactly when a₁ is the Condorcet winner and a₂ is its strongest challenger, the unique candidate x maximising N(x > a₁) (Laslier's *best contender*).
3. Every self-confirming approval poll is a self-confirming plurality poll.

Statement 2 is Laslier's Corollary 2 (2006, cited): an equilibrium without ties elects a Condorcet winner, and a Condorcet winner with a unique best contender gives a unique equilibrium. Statements 1 and 3 are the addition here. Statement 2 needs all of (T); in Laslier's model of ballot mistakes it fails (Section 9). Statement 3 uses only the tallies of the front-runners and holds there too.

*Proof.* Under plurality the tally is N(a₁ > a₂) for a₁, N(a₂ > a₁) for a₂ and zero for the rest, which gives 1. Under approval the poll confirms itself exactly when N(a₁ > a₂) > N(a₂ > a₁) > N(x > a₁) for every other x. The first inequality says a₁ beats a₂. With it, N(a₂ > a₁) < n/2, so the second says that every other x also loses to a₁, and that a₂ is the unique strongest challenger. Conversely, if a₁ is the Condorcet winner and a₂ its unique strongest challenger, then N(a₁ > a₂) > n/2 > N(a₂ > a₁) > N(x > a₁). Statement 3 follows, since N(a₂ > a₁) > N(x > a₁) ≥ 0. ∎

The proposition is checked on random profiles (impartial culture and a two-dimensional spatial model, 101 voters, three to six candidates), with profiles skipped where a tie in the tally decides.

*Consequences.*

- When there is a Condorcet winner, approval has exactly one self-confirming poll and elects the Condorcet winner. Plurality has one self-confirming poll for every pair of candidates (with the majority winner of the pair as leader), so it can elect any candidate that beats at least one other. This is Laslier's result on the approval side, under (T); it agrees with Myerson and Weber's observation that plurality restricts the winner's position little while approval leads to the median (cited). In a setting with common values, Goertz and Maniquet (2011) find approval the only simple scoring rule with at least one equilibrium that aggregates information efficiently (cited).
- When there is no Condorcet winner, approval has no self-confirming poll at all, and plurality still has many. In approval the absence of a fixed point is located exactly on the far side of the walls of *Walls and Strategy*, Section 2: the strategic regress becomes visible as a poll that cannot settle. Plurality settles in any case, because it reads only one comparison and cannot see the cycle. *(Interpretation.)*
- Under plurality, which self-confirming poll occurs is not determined by the electorate: the ballots carry no information that selects among them. The selection comes from outside the profile (history, media, the order in which candidates entered), the placement "in the rule" of *Where the Symmetry Goes* in a strategic form. Under approval, when a Condorcet winner exists, the profile determines the poll. *(Interpretation.)*

## 5. The majority switch

Proposition 2 concerns polls that confirm themselves, and it says something only when a Condorcet winner exists. A weaker property holds for every profile: approval can leave a leader whom a majority rejects, where plurality stays. Laslier remarks that without a Condorcet winner any announced winner is defeated under approval by a candidate preferred to it by more than half the population (2006, after Corollary 2, cited). Proposition 3 makes this precise: the defeat can take two rounds, since a leader who beats its runner-up keeps the lead for one round, with a new runner-up. Let the poll be replaced each round by the two highest tallies of the round before (the *walk*; a political tâtonnement in the sense of Durand, Macé and Núñez 2019, or iterative voting with poll information as in Meir et al. 2010 and Reijngoud and Endriss 2012).

**Proposition 3.** Under the common rationale, with approval:

1. whenever the leader changes from one round to the next, the new leader beats the old one by majority;
2. a leader beaten by majority by some candidate does not lead two rounds in a row;
3. a Condorcet winner, once it leads, keeps the lead.

*Proof.* Let the poll be (a₁, a₂). For 1, the new leader L has a higher tally than a₁ and a₂. If L = a₂, then N(a₂ > a₁) > N(a₁ > a₂). Otherwise N(L > a₁) exceeds both N(a₁ > a₂) and N(a₂ > a₁), one of which is at least n/2. For 2, suppose a₁ is beaten and still leads the next tally. Let c be its strongest challenger, the x maximising N(x > a₁); then N(c > a₁) > n/2 and c has the highest tally after a₁, so the next poll is (a₁, c). Its tally gives a₁ the count N(a₁ > c) < n/2 and c the count N(c > a₁) > n/2, so a₁ loses the lead. Statement 3 is the converse half of Proposition 2: as leader, a Condorcet winner gets N(a₁ > a₂) > n/2 and every other candidate a count below n/2. ∎

Starting from the sincere plurality count, the plurality winner p is therefore replaced within two rounds whenever some candidate beats it by majority, and the first new leader is such a candidate. Under plurality, by Proposition 2, every poll whose leader beats its runner-up stays where it is. This is the ability to make the switch by majority, and it needs no Condorcet winner. *(Proved; ties in tallies excluded; checked on random profiles.)*

The sequence of leaders is a walk along majority defeats: by the proof of parts 1 and 2, each new leader is the strongest challenger of the one before. It stops exactly at a Condorcet winner. Without one it cannot stop.

**The Smith set.** The Smith set (also called GETCHA, or the top cycle) is the smallest set of candidates each of whom beats every candidate outside it; a Condorcet winner is the case of one candidate. By part 1, once the leader is in the Smith set it stays there, since no candidate outside the set beats a member. Without a Condorcet winner the walk therefore cycles inside the Smith set once it has entered it, and the cycle takes the place of the self-confirming poll. *(Proved.)*

Entering is not guaranteed. The walk follows the strongest defeat of the current leader, and a cycle outside the Smith set can have stronger defeats than those inflicted by the Smith set. An example with 102 voters and candidates a, b, c, d: three groups of 35, 34 and 33 voters hold the cyclic rankings a > b > d, b > d > a and d > a > b, and in each group all but four voters put c second, the four others last. Then c beats every other candidate by 59 to 61 votes and is the Condorcet winner, with no first preferences, while the cycle a, b, d has margins of 67 to 69. From the plurality count the leader runs a, d, b, a, … forever, with c as runner-up from the second round on, and every tally on the way is strict. *(Computed; the profile is checked in the script.)* Among random profiles such walks are rare: of 24,800 walks from every starting poll (four to six candidates, both models), 43 ended in a cycle outside the Smith set, some of them through ties between challengers; from the plurality count, 1,197 of 1,200 profiles reached the Smith set. Brams and Fishburn (1983, example 7, p. 120) already give an example in which adjustment to polls cycles although a Condorcet winner exists (cited via Laslier 2006). *(Computed, no claim:* from every starting poll, the walk ends at the Condorcet winner in all spatial profiles and in 98 to 100 percent of the starting polls under impartial culture; among the profiles where the plurality winner is beaten, the leader after two rounds beats it in 177 of 178 spatial profiles and in 86 percent under impartial culture, after twenty rounds in 177 of 178 and in 67 percent; the difference is the walk moving on within a cycle.)

The same walk can be read in two ways. As a model of strategic voters under approval, its rounds are successive polls. As a counting method on ranked ballots, its rounds are computed from the ballots themselves, starting from the plurality count, and Proposition 3 then describes the count. Such a method obtains the outcome that the poll dynamics would reach without depending on voters to carry the dynamics out. It is implemented as Leader-AV-r (r counting rounds) in the Ballot Front Finder Lab. *(Interpretation.)*

## 6. Memory: reaching the Smith set

The walk of Section 5 fails to enter the Smith set because it always moves to the strongest defeat of the current leader, and a cycle outside the Smith set can hold all the strongest defeats. One change of the poll rule removes this: a candidate who has led once does not lead again.

The memory is not an assumption about voters. Voters still cast leader-rule ballots against whatever poll they are shown, and nothing in their rationale would make them exclude a former leader. The rule belongs to whoever produces the poll, or, read as a counting method, to the method itself. Its role here is to separate the two walks under the criterion of reaching the Smith set: the walk of Section 5 fails it, the walk with memory meets it.

**The walk with memory.** At each round the poll is (L, R). A candidate is *eligible* if it has never led, or is the current leader L; R is always eligible. Voters cast leader-rule ballots against (L, R). The next leader is the eligible candidate with the highest tally, and the next runner-up the eligible candidate with the highest tally after it. The walk stops when no eligible candidate other than the leader is left.

**Proposition 4.** Let the walk with memory start from any poll with an eligible runner-up, and suppose that no two eligible candidates tie in a tally. Then, with m candidates:

1. whenever the leader changes, the new leader has never led before and beats the old leader by majority;
2. a leader beaten by an eligible candidate loses the lead within two rounds;
3. a leader who beats every eligible candidate keeps the lead for good;
4. the leader changes at most m − 1 times, and not after round 2(m − 1);
5. the final leader is in the Smith set and beats every candidate that never led.

*Proof.* Parts 1 to 3 are the arguments of Proposition 3 with all candidates replaced by the eligible ones: the old leader's tally is N(L > R) and the runner-up's is N(R > L), both computed against an eligible runner-up, so a candidate who overtakes both beats L, and if L keeps the lead while beaten by an eligible candidate, its strongest eligible challenger becomes runner-up and wins the next tally. For 3, the eligible set does not change while the leader stays, so N(L > R) > n/2 > N(x > L) for every eligible x holds in every later round. For 4, every new leader is new, so there are at most m − 1 changes; after each change the next one comes within two rounds by 2 or never by 3, and the same holds for the first. For 5, once the leader is in the Smith set it stays there by 1. If the final leader were outside, no member of the Smith set would ever have led, so all of them would be eligible and would beat it, and by 2 it would not be final. If the walk stops because every candidate has led, members of the Smith set have led, so the final leader is in it. It beats every candidate that never led, since by 2 an eligible candidate beating it would take the lead. ∎

*(Proved; steps 1 to 3 and the step from a dominant set to an eligible challenger are checked in Lean, and so are parts 4 and 5 for the walk given by its properties, with no pairwise ties between candidates; checked on random profiles, where the bound 2(m − 1) is attained.)* On the profile of Section 5 the walk with memory runs a, d, b, c and stays at c, the Condorcet winner.

The walk with memory satisfies the criterion asked for in the [README](README.md), Section 7, question 7, with N = 2(m − 1). It does so by using information that a single tally does not hold, the record of who has led. Without that record the information of Proposition 1, the whole row of the leader, is exactly what leads the walk to the strongest defeat. With it, the row is used to choose among candidates not yet tried. *(Interpretation.)*

As an explicit counting method on ranked ballots, started from the plurality count, the walk with memory is a Smith-efficient method of the agenda type: it follows defeats through the candidates, each tried at most once as leader, and stops at the last leader, who beats every candidate not yet tried. For sequential pairwise procedures with an agenda, ending in the top cycle is classical (Miller 1977†). The winner within the Smith set depends on the start and on the order of the walk, as with an agenda chosen by the tallies. The method is a consequence of the analysis, not a model of how voters or polls behave.

## 7. Away from the corner

With the weights p(x, y), the coefficients c(x) and the virtual opponents π_x of [The Common Rationale](rationale.md), Section 2:

**Proposition 5 (any weights).** For every system of weights:

1. the best approval ballot approves x exactly when the voter prefers x to its virtual opponent, u_x > E_{π_x} u, so the approval tally of x is the number of voters who prefer x to π_x;
2. the best plurality vote goes to a candidate maximising c(x), and that candidate is approved in the best approval ballot;
3. a voter and the opposite voter (utility −u, the same poll) cast complementary best approval ballots, so together they add one approval to every candidate.

*Proof.* 1 is the sign of the coefficient c(x). For 2, the coefficients sum to zero, since each pair contributes p(x, y)(u_x − u_y) + p(y, x)(u_y − u_x) = 0, so the largest is positive (generically) and the candidate is approved. For 3, replacing u by −u replaces every c(x) by −c(x). ∎

In the corner (T), π_x is the leader for every x ≠ a₁ and the runner-up for a₁, and part 1 is Proposition 1: the tally N(x > a₁) is the special case of a count against a lottery. For any weights the favourite is approved and the least preferred candidate is not, since their coefficients are positive and negative; with three candidates the ballot is therefore sincere. Beyond that, away from the corner the approval ballot need not be sincere: with random weights on three to five candidates, about 4 percent of best ballots approve a candidate while leaving out one the voter prefers (*computed*). The inclusion in part 2 holds everywhere. That the plurality ballot is a function of the approval ballot holds only in the corner; in general the plurality vote is the approved candidate with the largest coefficient, which the approval ballot does not show.

**Proposition 6 (a finite corner, that is, weights close enough to (T) that the best replies do not change).** Let g be the smallest difference between the utilities of two candidates for any voter, and D the largest range of a voter's utilities. Suppose that for some δ with 2δD < g:

- Σ_{y ≠ a₁, a₂} p(a₁, y) ≤ δ p(a₁, a₂), and the same for a₂;
- for every other candidate x: Σ_{y ≠ a₁} p(x, y) ≤ δ p(x, a₁);
- for every other candidate x: Σ_y p(x, y) ≤ δ p(a₁, a₂).

Then the best approval ballot is the leader-rule ballot and the best plurality vote goes to the preferred of a₁ and a₂, for every voter. The last condition is needed only for plurality.

*Proof.* For x ≠ a₁, c(x) = p(x, a₁)(u_x − u_{a₁}) plus terms whose total size is at most δ p(x, a₁) D < p(x, a₁) g, so its sign is that of u_x − u_{a₁}; the same argument with a₂ in place of a₁ decides a₁. For plurality, the preferred front-runner has a coefficient of at least p(a₁, a₂)(g − δD), the other front-runner a negative one, and every other candidate at most δ p(a₁, a₂) D, which is smaller since 2δD < g. ∎

*(Proved; checked in Lean, and on 3000 random systems of weights within the bound.)* So Propositions 1 to 4 do not need the limit, only that at every poll involved each candidate's main tie outweighs its others by a factor above 2D/g. The factor is set by the finest distinction of preference in the electorate. Applied voter by voter, the same proof bounds the damage when the condition fails for some voters: the ballots differ from the leader rule only for voters whose smallest utility difference is at most 2δ times their range, so each tally moves by at most their number, and every strict inequality between tallies in Propositions 1 to 4 with a margin above twice that number survives. The conclusions degrade continuously as the weights leave the corner. *(Proved.)*

What is not yet available away from the corner is the walk: Propositions 2 to 4 also use how the poll, and with it the weights, follows from the tally of the previous round. In the corner this is the ranking of the tallies; in general it needs a model of how tie probabilities depend on the tallies (binomial errors as in Laslier, or Poisson populations).

## 8. Ties

The propositions exclude ties. Three kinds can occur: ties between pairwise counts, N(x > y) = N(y > x), possible only with an even number of voters; ties between tallies in a poll, for instance two challengers with the same count against the leader; and indifferences in a voter's preferences, which Section 2 touches. The first two are settled here.

**Proposition 7.** Under the common rationale, with approval and the walks of Sections 5 and 6:

1. If no two candidates tie pairwise, ties between tallies do no harm: with any rule for breaking them, Propositions 2 to 4 hold as stated.
2. With pairwise ties, every change of leader goes to a candidate that beats or ties the old leader. A leader in the Smith set (each member beats every non-member) keeps the walk in it.
3. With pairwise ties and the walk with memory, if ties between tallies are broken by a rule that depends only on the tallies and on who is eligible, the walk settles by round 2(m − 1) in the Smith set. With any other rule, random tie-breaking included, it still settles in the Smith set, since there are at most m − 1 changes, but not necessarily by that round; with random tie-breaking the final leader beats or ties every candidate that never led, with probability one.

*Proof.* Every tally is a pairwise count: N(L > R) for the leader and N(x > L) for every other candidate. For 1: a candidate x reaching the top beside or above the leader has N(x > L) at least max(N(L > R), N(R > L)), which is at least n/2, and with no pairwise ties more than n/2, so x beats L; a beaten leader that keeps the lead hands the runner-up position to a strongest challenger, any of which beats it, and loses the next tally strictly; a Condorcet winner as leader has a tally above n/2 and every other candidate one below, so no tie arises. The arguments of Propositions 2 to 4 go through with these inequalities. For 2, the same computation gives N(x > L) ≥ n/2, so x beats or ties L, and a member of the Smith set is not beaten or tied by a non-member. For 3: changes bring new leaders, so there are at most m − 1. When the leader is kept, the challengers' tallies against it do not change and neither does the set of eligible candidates, so a rule depending only on these chooses the same runner-up again and the poll repeats; a leader kept for two rounds is kept for good, and the counting of Proposition 4 applies. A final leader outside the Smith set would face eligible members who beat it strictly, so it would lose the next tally; this uses only that the runner-up has a largest eligible tally, whatever the rule for ties. With random tie-breaking a tie repeated every round is eventually lost, so with probability one the walk stops only at a leader that no eligible candidate beats or ties, or when every candidate has led. ∎

*(Proved; checked on random profiles with odd and even electorates and both tie-breaking rules, `scripts/information/ties.py`. In even electorates a fifth to over a third of the changes go along ties.)* The assumption of no ties in Sections 5 and 6 can therefore be dropped: it fixes only the strictness of the defeats along the walk and, with random tie-breaking, the bound on the number of rounds. Part 3 is checked in Lean without any assumption on pairwise ties: with deterministic tie-breaking and the bound (`memory_walk_ties` in `MemoryWalk.lean`), and with any tie-breaking without the bound (`memory_walk_settles`); the statement with probability one is not.

**The Schwartz set.** The Schwartz set (also called GOCHA; Schwartz 1986†) is the union of the smallest sets that no outside candidate beats; it lies inside the Smith set and is smaller when pairwise ties occur. The walks do not end in it in general, because they move along ties, and a member of a Schwartz component can be tied with an outsider. Among random profiles with even electorates in which the two sets differ, the walk with memory ended in the Smith set every time and outside the Schwartz set in 18 per cent of the profiles with a fixed tie-break and 53 per cent with a random one (*computed*, `scripts/information/ties.py`). The Schwartz set appears with a different rule for ties: if a tie for the lead never dethrones the current leader, every change is a strict defeat (the new leader's tally exceeds both N(L > R) and, weakly, N(R > L)), so no set that no outsider beats is ever left once the leader is in it. *(Proved; checked in Lean, `incumbent_change_strict`, `incumbent_stays`.)* It never left the Schwartz set once inside, and ended in it in 1414 of 1415 profiles where the two sets differ without memory and in 1404 of 1407 with memory; with memory the exceptions are walks stopped at a leader that the remaining candidates only tie (*computed*). Entering the Schwartz set is not guaranteed in general, for the same reason as for the Smith set in Section 5.

## 9. Ballot mistakes

In Laslier's model of ballot mistakes ([The Common Rationale](rationale.md), Section 3) the ties of the front-runners separate exponentially, while the ties of a candidate ranked third or lower with the candidates above it stay of the same order.

The best approval ballot decides such a candidate against a lottery over the candidates above it, as in Proposition 5, not against the leader alone; exact best replies differ from the leader rule for a fifth to two fifths of random voters at every size tried (40 to 640 voters). A threshold against the lottery with the limiting weights agrees with the exact best reply more often (for 31 to 35 of 40 voters, against 23 to 32 for the leader rule) but not always: the exact weights also depend on which candidate is one vote ahead in a near tie.

**The Condorcet winner can lose.** Take candidates a₁, a₂ and c, and per 100 voters: 10 with c > a₁ > a₂; 42 with a₂ > c > a₁ and c rated at a quarter of the way from a₁ to a₂; 42 with a₁ > c > a₂ and c rated at two fifths of the way from a₂ to a₁; 4 with a₁ > a₂ > c; 2 with a₂ > a₁ > c. Then c beats a₁ and a₂ by 52 to 48, and a₁ beats a₂ by 56 to 44. Against the poll with a₁ leading, a₂ second and c at 10 per cent, the exact best replies reproduce the poll exactly for 100, 200, 400 and 800 voters. This is an equilibrium in Laslier's sense in which the Condorcet winner gets 10 per cent and a₁ is elected; under the leader rule c would get 52 per cent and overtake a₂. The camps that see c as a lukewarm compromise weigh it against both front-runners, and against both it loses. Laslier's Corollary 2 therefore does not hold in the model of the working paper as stated, where the order of ties is derived from uncounted marks. It is consistent with the published abstract if the order of ties there is assumed rather than derived: the example is an equilibrium of voters who compute the likelihood of ties from the model of mistakes, not of voters who hold (T).

**Sincerity.** With four or more candidates the exact best ballots are occasionally insincere: for random voters, 0 to 2 of 60 with four candidates and 2 of 60 with five, at 80 and 320 voters. One example, with five candidates ranked by score as listed and utilities (410, 601, 43, 404, 24), approves the runner-up and the fourth candidate and not the leader, whom the voter prefers to the fourth. The leader rule excludes exactly this. With three candidates the ballot is sincere, since the favourite is approved and the least preferred is not. Laslier's Corollary 1 (sincerity) therefore also rests on the half of his Lemma 2 that fails with uncounted marks.

**The walks with uncounted marks.** With the limiting weights for the candidates below the runner-up and voters responding to the previous tally, the walks of Sections 5 and 6 lose their guarantees (`scripts/information/lost_marks_walk.py`, 101 voters, starting from the plurality count). Under impartial culture, 10 to 21 per cent of the changes of leader go to a candidate that does not beat the old leader by majority, so Proposition 3, part 1, fails; the walk reaches the Condorcet winner in 88, 66 and 45 per cent of the profiles that have one, with three, four and five candidates, against all of them under the leader rule; and the walk with memory ends in the Smith set in 96, 89 and 85 per cent. In the spatial model the losses are small (Condorcet winner reached in 88 to 97 per cent, Smith set with memory in 98 to 99 per cent). Almost all failures are cycles, not polls that settle at another candidate: a self-confirming poll led by a candidate other than the Condorcet winner is rare from the plurality count (at most 3 in 400 profiles), though the example above shows it exists.

With symmetric mistakes, the example above is still an equilibrium at 100 and 200 voters and not at 400, where c's approvals jump to 208 per 400.

*Consequences.* The published framing separates two claims: an assumption about how voters weigh ties, and what follows from it. What follows is confirmed here (Propositions 1 and 2 under (T)). What is questioned is the assumption: independent recording errors that only lose marks do not support it for candidates ranked third or lower, and errors in both directions support it only in the limit, slowly. Whether a model of uncertainty that voters could plausibly hold yields (T) at realistic sizes is open ([The Common Rationale](rationale.md), Section 5, question 3). What holds in both models of mistakes is everything that rests on the front-runners: parts 1 and 2 of Proposition 1 (equal tallies of the front-runners, the plurality ballot as a function of the approval ballot) and part 3 of Proposition 2 (every self-confirming approval poll confirms itself under plurality). The comparison of approval with plurality survives: approval's self-confirming polls are among plurality's. What depends on the kind of mistake, and on the size of the electorate, is that approval finds the Condorcet winner: with marks only uncounted it can fail in every electorate, with symmetric mistakes only in small ones. So the order of ties is not a technicality. It decides whether approval's extra information, the comparisons of the other candidates, is read against the leader or against a mixture of the front-runners, and only the first guarantees the Condorcet winner. *(Interpretation.)* The published version of Laslier's paper (2009) has not been compared with the working paper read here beyond its abstract.

## 10. Best and worst case

With Propositions 1 and 2 the two steps of the [README](README.md), Section 1, can be carried out, but the result depends on the target by which outcomes are judged.

**Majority as target.** If outcomes are judged by the majority relation (the Condorcet winner when there is one), approval's only self-confirming outcome is the best one, and it is also among plurality's. The best cases agree; in the worst case approval is strictly better whenever plurality has a self-confirming poll led by a candidate other than the Condorcet winner. With an odd number of voters that is the case in every profile with a Condorcet winner, since among the other candidates one beats another. Plurality lies below approval. *(Proved, from Proposition 2.)*

**Total utility as target.** If outcomes are judged by the sum of utilities, the best case is no longer ordered. A plurality poll led by a candidate who is not the Condorcet winner but has a higher total utility can confirm itself, and approval cannot reach that candidate. In the computations this happens for about a quarter to a third of the profiles with a Condorcet winner under impartial culture, where utilities are unrelated across voters, and for under a tenth in the spatial model (*computed*). The worst case still favours approval: plurality's worst self-confirming winner by total utility is not the Condorcet winner in 71 percent of the profiles with a Condorcet winner for three candidates under impartial culture, and in nearly all of them otherwise (*computed*; an earlier version gave this figure under the majority target).

*Reading.* Plurality's advantage in that case does not come from the electorate: the ballots carry the same single comparison whichever poll occurs, and the good outcome needs a fortunate poll. Under the common rationale neither method's ballots carry any information about intensities. Both reveal only who is preferred to whom, so a utilitarian target asks of them something neither delivers through the ballots. Two ways of stating the best case are possible, and the choice between them is open:

- the best over all self-confirming polls, which credits a method with information that arrives through the poll;
- the best use of the information carried by the ballots, which credits plurality with one comparison and approval with a row, and under which approval dominates for any target that depends only on the majority relation.

The second is the one adopted, through Blackwell's order on experiments ([README](README.md), Section 3).

## 11. Stage 2 in bits

By the Lemma of the [README](README.md), Section 2, Blackwell's order fails at a poll whenever the plurality ballot is not a function of the approval ballot, and H(β_plur | β_appr) measures by how much. In the corner the order holds for the counts themselves (Proposition 1): the strategic plurality count keeps one number about the electorate and the strategic approval count m − 1, the first among them (README, Section 2, Proposition; `scripts/information/strategic_count.py`). The polls of the two methods are matched by the same leader and runner-up. *(Checks in `scripts/information/stage2_bits.py`.)*

**In the corner.** The plurality ballot is the preferred front-runner, a function of the approval ballot (Proposition 1), so H(β_plur | β_appr) = 0 for every culture. Under impartial culture, H(β_plur) = 1 bit and

  H(β_appr) = log₂ m + (1/m) Σ_{j=0}^{m−1} log₂ C(m − 1, j),

which is 1.92, 2.79, 3.64 and 4.47 bits for three to six candidates, against capacities of log₂ m and m bits. *(Proved: the approval ballot of the leader rule determines, and is determined by, the set T of candidates the voter ranks above a₁, since a₁ is approved exactly when a₂ is not in T; under impartial culture the size of T is uniform on 0, …, m − 1 and T is uniform given its size.)* With three candidates the strategic approval ballot already carries more than plurality's capacity of 1.58 bits. In the spatial model the values are lower (0.78 to 0.87 bits for plurality, 1.43 to 2.60 for approval, three to six candidates), and H(β_plur | β_appr) is zero at every poll (*computed*).

**Away from the corner.** With weights moved from the corner by a random system, P = P₀ + λR, where P₀ puts 1 on the tie of the front-runners and 0.001 on the ties of the others with the leader, H(β_plur | β_appr) grows smoothly with λ: from 0.003 to 0.005 bits at λ = 0 (the residue of the finite 0.001) through 0.04 to 0.13 at λ = 0.03 to 0.34, 0.66 and 0.94 bits at λ = 1 for three, four and five candidates, while H(β_appr | β_plur) stays between 0.9 and 3.3 bits (*computed*, 40 weight systems each). The plurality vote is always approved (Proposition 5); what plurality adds is which of the approved candidates gets the single vote, which depends on intensities.

**Ballot mistakes.** In Laslier's model of uncounted marks (exact best replies, 100 other voters), H(β_plur | β_appr) = 0 at polls with the third candidate well behind ([55, 45, 35], [52, 48, 30], [55, 45, 35, 20]). At [52, 48, 45] four voters in 400 approve both front-runners or neither, and it is 0.008 bits. At polls taken from impartial-culture profiles, where the third approval tally is often close to the runner-up's, it is 0.016 bits on average for three candidates and 0.049 for four (zero at 17 and 8 of 30 polls). *(Computed.)* So the front-runner part of Proposition 1 holds in that model once the front-runners' ties have separated from the third candidate's, as Section 9 says for large electorates, and not yet at a hundred voters when the race for second place is close. The comparison here is voter by voter; the noise the mistakes add to the count is left aside.

## References

- Blackwell, D. (1953). Equivalent comparisons of experiments. *Annals of Mathematical Statistics* 24(2), 265–272. doi:10.1214/aoms/1177729032.
- Brams, S. J. and Fishburn, P. C. (1983). *Approval Voting.* Birkhäuser, Boston. (Cited via Laslier 2006.)
- Durand, F., Macé, A. and Núñez, M. (2019). Analysis of approval voting in Poisson games. Working paper, Paris School of Economics.
- Goertz, J. M. M. and Maniquet, F. (2011). On the informational efficiency of simple scoring rules. *Journal of Economic Theory* 146, 1464–1480. doi:10.1016/j.jet.2011.03.001.
- Laslier, J.-F. (2006). Strategic approval voting in a large electorate. Working paper, halshs-00121751, version of 16 June 2006. Lemma, theorem and corollary numbers refer to this version.
- Laslier, J.-F. (2009). The leader rule: a model of strategic approval voting in a large electorate. *Journal of Theoretical Politics* 21, 113–136. doi:10.1177/0951629808097286. The published version; not compared with the working paper.
- Meir, R., Polukarov, M., Rosenschein, J. S. and Jennings, N. R. (2010). Convergence to equilibria in plurality voting. *Proceedings of AAAI 2010*. †
- Miller, N. R. (1977). Graph-theoretical approaches to the theory of voting. *American Journal of Political Science* 21, 769–803. † (sequential pairwise voting and the top cycle)
- Myerson, R. B. and Weber, R. J. (1993). A theory of voting equilibria. *American Political Science Review* 87, 102–114.
- Reijngoud, A. and Endriss, U. (2012). Voter response to iterated poll information. *Proceedings of AAMAS 2012*. †
- Schwartz, T. (1986). *The Logic of Collective Choice.* Columbia University Press. †
- *Where the Symmetry Goes*, *Walls and Strategy* (working notes and drafts in this repository).
