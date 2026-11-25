# Strategic Information: Plurality and Approval under a Common Rationale

*Working note, first draft. It proposes a way to compare voting methods by how much of the electorate's information they can use when every voter follows the same strategic rationale, and carries the comparison out for plurality and approval voting, with score voting as a first extension. Statements are marked as cited, proved here, computed on random profiles, or interpretation. References marked † are cited from memory and have not been checked against the original. The checks are in `scripts/information/strategic_information.py`; Propositions 1 to 3 and the statement on the Smith set are checked in Lean in `lean/LeaderRule.lean`, with the best replies as definitions.*

## 1. The question

The impossibility theorems of Arrow and Gibbard describe the upper end of the space of voting methods: once a method is good enough, its remaining defects are trade-offs, and no method has all the properties at once. They say nothing about methods that lie below that frontier. A method can be worse than another without any trade-off, if the other does at least as well in every respect that both are judged by. The aim of this note is to make such comparisons precise for methods that are similar enough to be compared pair by pair.

The comparison has two steps. The first asks for the best use a method can make of the information in the electorate under ideal assumptions about the voters. The second asks for the worst outcome under the same assumptions. If one method is at least as good as another in both, and better in one, the other lies below the frontier. Neither step compares sincere ballots: voters who leave gains on the table are not the point. Both methods are played by voters who follow the same rationale, and the rationale must be stated without reference to the method.

## 2. The common rationale

A *poll* is a shared belief about the race, given by a leader a₁ and a runner-up a₂. A voter values a ballot by its effect on pivotal events, in the manner of Myerson and Weber (1993): if s(x) is what the ballot adds to the tally of candidate x and u the voter's utility, a tie between x and y gives the ballot the value (s(x) − s(y))(u_x − u_y). One assumption on the likelihood of ties is used, in the sense that one tie is so much more likely than another that the second matters only when the first leaves the choice open (a voter then maximises lexicographically, event by event):

- **(T)** for every candidate x other than a₁, the most likely tie involving x is the tie with a₁; the most likely tie involving a₁ is the tie with a₂; ties of three or more candidates are less likely than the ties of two among them.

No comparison is made between ties that share no candidate, for instance between a₁ against a₄ and a₂ against a₃. This is what Laslier (2006, Lemma 2) proves for large electorates and uses for the leader rule (his Theorem 1): types of voters replicated n times, scores without ties, and each approval left unrecorded with a small probability ε < 1/v, independently across voters and candidates, where v is the size of the unreplicated electorate; the lemma then orders all ties involving a given candidate by the ranks of the others, and (T) is the part of that order the proofs use (cited). The lemma concerns only the distribution of the tallies, so it applies to plurality tallies in the same way (our reading). Here (T) is taken as the primitive, and the ballot mistakes from which Laslier derives it play no further part. The assumption is the same for every method, and it is the rationale used throughout.

Preferences are strict. With this rationale the best replies are as follows (proved here; checked by brute force over all ballots in the script):

- **Plurality.** Vote for whichever of a₁ and a₂ you prefer. The tie between them decides alone, since a vote for anyone else has no effect on it.
- **Approval.** Approve a₁ exactly when you prefer a₁ to a₂, and approve every other candidate exactly when you prefer that candidate to a₁. The first tie fixes the ballot on a₁ and a₂ (one of the two approved, not both, since approving both abstains from their comparison). The ties with a₁ then fix every other candidate. This is the leader rule, Laslier's "lexicographic response" (2006, Theorem 1, cited; there proved as the unique best reply for large n). In particular a₂ is approved exactly when it is preferred to a₁. Leader-rule ballots are sincere, and admissible in the sense of Brams and Fishburn (1983): the favourite is always approved and the least preferred candidate never (Laslier 2006, Corollary 1 and Section 1, cited; checked).

## 2a. When the poll is tied

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

The approval tallies in 1 and 3 are Laslier's Theorem 2 (2006, cited), stated there for equilibrium score vectors and proved from the best replies alone, so that it holds for any poll. The comparison with plurality is the addition here.

*Reading.* In the matrix of pairwise counts, strategic plurality reveals one entry, the comparison of the two front-runners. Strategic approval reveals that entry and the whole row of the leader: how every candidate fares against a₁. In the language of Blackwell (1953)†, the plurality ballot is a garbling of the approval ballot, so any use that can be made of the strategic plurality ballots can also be made of the strategic approval ballots, and not conversely. This is the first step of Section 1 for this pair, for a fixed poll. *(Proved; the interpretation as a Blackwell comparison is ours.)*

## 4. Which polls confirm themselves

The poll is not given from outside. A poll is *self-confirming* if the tally it produces ranks a₁ first and a₂ second, strictly.

**Proposition 2.** Under the common rationale:

1. Under plurality, a poll (a₁, a₂) is self-confirming exactly when a₁ beats a₂ by majority and some voter prefers a₂ to a₁.
2. Under approval, a poll (a₁, a₂) is self-confirming exactly when a₁ is the Condorcet winner and a₂ is its strongest challenger, the unique candidate x maximising N(x > a₁).
3. Every self-confirming approval poll is a self-confirming plurality poll.

Statement 2 is Laslier's Corollary 2 (2006, cited): an equilibrium without ties elects a Condorcet winner, and a Condorcet winner with a unique best contender gives a unique equilibrium. Statements 1 and 3 are the addition here.

*Proof.* Under plurality the tally is N(a₁ > a₂) for a₁, N(a₂ > a₁) for a₂ and zero for the rest, which gives 1. Under approval the poll confirms itself exactly when N(a₁ > a₂) > N(a₂ > a₁) > N(x > a₁) for every other x. The first inequality says a₁ beats a₂. With it, N(a₂ > a₁) < n/2, so the second says that every other x also loses to a₁, and that a₂ is the unique strongest challenger. Conversely, if a₁ is the Condorcet winner and a₂ its unique strongest challenger, then N(a₁ > a₂) > n/2 > N(a₂ > a₁) > N(x > a₁). Statement 3 follows, since N(a₂ > a₁) > N(x > a₁) ≥ 0. ∎

The proposition is checked on random profiles (impartial culture and a two-dimensional spatial model, 101 voters, three to six candidates), with profiles skipped where a tie in the tally decides.

*Consequences.*

- When there is a Condorcet winner, approval has exactly one self-confirming poll and elects the Condorcet winner. Plurality has one self-confirming poll for every pair of candidates (with the majority winner of the pair as leader), so it can elect any candidate that beats at least one other. This is Laslier's result on the approval side; it agrees with Myerson and Weber's observation that plurality restricts the winner's position little while approval leads to the median (cited). In a setting with common values, Goertz and Maniquet (2011) find approval the only simple scoring rule with at least one equilibrium that aggregates information efficiently (cited).
- When there is no Condorcet winner, approval has no self-confirming poll at all, and plurality still has many. In approval the absence of a fixed point is located exactly on the far side of the walls of *Walls and Strategy*, Section 2: the strategic regress becomes visible as a poll that cannot settle. Plurality settles in any case, because it reads only one comparison and cannot see the cycle. *(Interpretation.)*
- Under plurality, which self-confirming poll occurs is not determined by the electorate: the ballots carry no information that selects among them. The selection comes from outside the profile (history, media, the order in which candidates entered), the placement "in the rule" of *Where the Symmetry Goes* in a strategic form. Under approval, when a Condorcet winner exists, the profile determines the poll. *(Interpretation.)*

## 4a. The majority switch

Proposition 2 concerns polls that confirm themselves, and it says something only when a Condorcet winner exists. A weaker property holds for every profile: approval can leave a leader whom a majority rejects, where plurality stays. Laslier remarks that without a Condorcet winner any announced winner is defeated under approval by a candidate preferred to it by more than half the population (2006, after Corollary 2, cited). Proposition 3 makes this precise: the defeat can take two rounds, since a leader who beats its runner-up keeps the lead for one round, with a new runner-up. Let the poll be replaced each round by the two highest tallies of the round before.

**Proposition 3.** Under the common rationale, with approval:

1. whenever the leader changes from one round to the next, the new leader beats the old one by majority;
2. a leader beaten by majority by some candidate does not lead two rounds in a row;
3. a Condorcet winner, once it leads, keeps the lead.

*Proof.* Let the poll be (a₁, a₂). For 1, the new leader L has a higher tally than a₁ and a₂. If L = a₂, then N(a₂ > a₁) > N(a₁ > a₂). Otherwise N(L > a₁) exceeds both N(a₁ > a₂) and N(a₂ > a₁), one of which is at least n/2. For 2, suppose a₁ is beaten and still leads the next tally. Let c be its strongest challenger, the x maximising N(x > a₁); then N(c > a₁) > n/2 and c has the highest tally after a₁, so the next poll is (a₁, c). Its tally gives a₁ the count N(a₁ > c) < n/2 and c the count N(c > a₁) > n/2, so a₁ loses the lead. Statement 3 is the converse half of Proposition 2: as leader, a Condorcet winner gets N(a₁ > a₂) > n/2 and every other candidate a count below n/2. ∎

Starting from the sincere plurality count, the plurality winner p is therefore replaced within two rounds whenever some candidate beats it by majority, and the first new leader is such a candidate. Under plurality, by Proposition 2, every poll whose leader beats its runner-up stays where it is. This is the ability to make the switch by majority, and it needs no Condorcet winner. *(Proved; ties in tallies excluded; checked on random profiles.)*

The sequence of leaders is a walk along majority defeats: by the proof of parts 1 and 2, each new leader is the strongest challenger of the one before. It stops exactly at a Condorcet winner. Without one it cannot stop.

**The Smith set.** The Smith set is the smallest set of candidates each of whom beats every candidate outside it; a Condorcet winner is the case of one candidate. By part 1, once the leader is in the Smith set it stays there, since no candidate outside the set beats a member. Without a Condorcet winner the walk therefore cycles inside the Smith set once it has entered it, and the cycle takes the place of the self-confirming poll. *(Proved.)*

Entering is not guaranteed. The walk follows the strongest defeat of the current leader, and a cycle outside the Smith set can have stronger defeats than those inflicted by the Smith set. An example with 102 voters and candidates a, b, c, d: three groups of 35, 34 and 33 voters hold the cyclic rankings a > b > d, b > d > a and d > a > b, and in each group all but four voters put c second, the four others last. Then c beats every other candidate by 59 to 61 votes and is the Condorcet winner, with no first preferences, while the cycle a, b, d has margins of 67 to 69. From the plurality count the leader runs a, d, b, a, … forever, with c as runner-up from the second round on, and every tally on the way is strict. *(Computed; the profile is checked in the script.)* Among random profiles such walks are rare: of 24,800 walks from every starting poll (four to six candidates, both models), 43 ended in a cycle outside the Smith set, some of them through ties between challengers; from the plurality count, 1,197 of 1,200 profiles reached the Smith set. Brams and Fishburn (1983, example 7, p. 120) already give an example in which adjustment to polls cycles although a Condorcet winner exists (cited via Laslier 2006). *(Computed, no claim:* from every starting poll, the walk ends at the Condorcet winner in all spatial profiles and in 98 to 100 percent of the starting polls under impartial culture; among the profiles where the plurality winner is beaten, the leader after two rounds beats it in 177 of 178 spatial profiles and in 86 percent under impartial culture, after twenty rounds in 177 of 178 and in 67 percent; the difference is the walk moving on within a cycle.)

The same walk can be read in two ways. As a model of strategic voters under approval, its rounds are successive polls. As a counting method on ranked ballots, its rounds are computed from the ballots themselves, starting from the plurality count, and Proposition 3 then describes the count. Such a method obtains the outcome that the poll dynamics would reach without depending on voters to carry the dynamics out. It is implemented as Leader-AV-r (r counting rounds) in the Ballot Front Finder Lab. *(Interpretation.)*

## 5. Best and worst case

With Propositions 1 and 2 the two steps of Section 1 can be carried out, but the result depends on the target by which outcomes are judged.

**Majority as target.** If outcomes are judged by the majority relation (the Condorcet winner when there is one), approval's only self-confirming outcome is the best one, and it is also among plurality's. The best cases agree; in the worst case approval is strictly better whenever plurality has a self-confirming poll led by a candidate other than the Condorcet winner. In the computations that is the case in 71 percent of the profiles with a Condorcet winner for three candidates under impartial culture, and in nearly all of them otherwise. Plurality lies below approval. *(Proved, from Proposition 2.)*

**Total utility as target.** If outcomes are judged by the sum of utilities, the best case is no longer ordered. A plurality poll led by a candidate who is not the Condorcet winner but has a higher total utility can confirm itself, and approval cannot reach that candidate. In the computations this happens for about a quarter to a third of the profiles with a Condorcet winner under impartial culture, where utilities are unrelated across voters, and for under a tenth in the spatial model (*computed*). The worst case still favours approval as above.

*Reading.* Plurality's advantage in that case does not come from the electorate: the ballots carry the same single comparison whichever poll occurs, and the good outcome needs a fortunate poll. Under the common rationale neither method's ballots carry any information about intensities. Both reveal only who is preferred to whom, so a utilitarian target asks of them something neither delivers through the ballots. Two ways of stating the best case are possible, and the choice between them is open:

- the best over all self-confirming polls, which credits a method with information that arrives through the poll;
- the best use of the information carried by the ballots, which credits plurality with one comparison and approval with a row, and under which approval dominates for any target that depends only on the majority relation.

## 6. Score voting

Under the same rationale, score voting with scores 0 to k reduces to approval with every ballot multiplied by k (proved here: the tie between a₁ and a₂ forces the scores of the two to k and 0, and each tie with a₁ forces every other score to k or 0, according to the sign of u_x − u_{a₁}). Tallies are scaled by k, so outcomes and self-confirming polls coincide with those of approval. This is the case of (T) in the equivalence of Núñez and Laslier (2014): additive rules with the same extremal ballots are strategically equivalent in large elections, and the equivalence fails for small electorates (cited). Under this rationale score voting is exactly as good as approval and never worse, which is the first half of the claim that score voting dominates approval. A strict advantage would have to come from a rationale in which (T) fails, as in small electorates, and it would have to be shown that intermediate scores then carry information that the method uses.

## 7. What is assumed, and where it may break

- **The order of ties.** The whole comparison rests on (T), a large-electorate idealisation with distinct poll scores. Without any order of ties, the best approval ballot in the approximation of Myerson and Weber is a threshold at the mean utility of the candidates, weighted by the probabilities of the ties with each (†, not yet checked against the paper); (T) is the corner in which all weight lies on one tie per candidate. Section 2a is a first step away from that corner. In large Poisson games, a counterexample to the Condorcet consistency of approval voting is known (Núñez 2010†), so the conclusion of Section 4 depends on the strength of this assumption, not only on large numbers. Durand, Macé and Núñez (2019) study which equilibria of approval in Poisson games are stable and how often they elect the Condorcet winner.
- **A shared poll.** All voters respond to the same leader and runner-up. Polls that differ between groups of voters are not covered.
- **Strict preferences, a single winner, no abstention.** Indifferences change the leader rule at the margin; abstention is absent from both methods here.
- **Information in the poll.** Section 5 shows that the comparison depends on whether information arriving through the poll is counted. This is a question of definition, not of mathematics, and it should be settled before the framework is extended.
- **Other methods.** The rationale is stated for any method, but best replies under ranked methods (instant runoff, Condorcet methods) are not "one comparison per candidate", and Proposition 1 has no analogue yet. A ladder in which a well-played Condorcet method reveals the full matrix is plausible and unproved.

## 8. Connection with the Equality Criterion

Approval passes the Equality Criterion (an approval ballot and its complement add one approval to every candidate) and plurality fails it (*The Equality Criterion and Reversal*, Section 2). In Proposition 1 the extra information of approval is the row of the leader, and each of its entries is a pairwise count, a quantity on which a ballot and its opposite cancel. Whether the criterion is the structural reason why the additional information is unbiased, and whether failing it always shows up as a choice of self-confirming poll made from outside the profile, is open. *(Interpretation and question.)*

## 9. Open questions

1. Settle the definition of the best case (Section 5), and with it state the dominance order on methods in general.
2. Instant runoff and plurality under the same rationale; then a Condorcet method against approval.
3. Score against approval when (T) fails: does any intermediate score become a best reply, and does it carry information the tally uses?
4. Weaken (T): which conclusions survive if a challenger's tie with the runner-up can be as likely as its tie with the leader, as with correlated uncertainty (Poisson populations, where Núñez 2010 finds a counterexample)? Section 2a treats the case of exact ties in the poll.
5. Measure the gap in the Ballot Front Finder Lab: the share of profiles in which the strategic outcome depends on the starting poll, per method.
6. The link with the Equality Criterion of Section 8.
7. A criterion in the spirit of the Smith set: a method reaches the Smith set under the common rationale within N rounds from every poll, with N the number of candidates or a bound still to be found. Approval with the leader rule fails it (Section 4a), rarely. Which methods, or which rules for updating the poll, satisfy it?
8. The general rationale without (T): pivot-weighted thresholds for approval and the corresponding plurality best reply, and whether Propositions 1 to 3 hold in a neighbourhood of the corner (T).

## References

- Blackwell, D. (1953). Equivalent comparisons of experiments. *Annals of Mathematical Statistics* 24, 265–272. †
- Brams, S. J. and Fishburn, P. C. (1983). *Approval Voting.* Birkhäuser, Boston. (Cited via Laslier 2006.)
- Durand, F., Macé, A. and Núñez, M. (2019). Analysis of approval voting in Poisson games. Working paper, Paris School of Economics.
- Goertz, J. M. M. and Maniquet, F. (2011). On the informational efficiency of simple scoring rules. *Journal of Economic Theory* 146, 1464–1480. doi:10.1016/j.jet.2011.03.001.
- Laslier, J.-F. (2006). Strategic approval voting in a large electorate. Working paper, halshs-00121751, version of 16 June 2006. Lemma, theorem and corollary numbers refer to this version.
- Laslier, J.-F. (2009). The leader rule: a model of strategic approval voting in a large electorate. *Journal of Theoretical Politics* 21, 113–136. doi:10.1177/0951629808097286. The published version; not compared with the working paper.
- Myerson, R. B. and Weber, R. J. (1993). A theory of voting equilibria. *American Political Science Review* 87, 102–114.
- Núñez, M. (2010). Condorcet consistency of approval voting: a counter example in large Poisson games. *Journal of Theoretical Politics* 22, 64–84. doi:10.1177/0951629809348268. † (author from memory)
- Núñez, M. and Laslier, J.-F. (2014). Preference intensity representation: strategic overstating in large elections. *Social Choice and Welfare* 42, 313–340. doi:10.1007/s00355-013-0728-0.
- *The Equality Criterion and Reversal*, *Where the Symmetry Goes* (working notes), *Walls and Strategy* (draft), all in this repository.
