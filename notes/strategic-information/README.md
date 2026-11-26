# Strategic Information

*Working notes. They propose a way to compare voting methods by how much of the electorate's information they can use when every voter follows the same strategic rationale. This README holds the main idea (the two stages of information and the order they define), the pairs compared so far and the questions that concern all of them. The strategic model shared by all pairs is in [The Common Rationale](rationale.md); each pair has its own note. Statements are marked as cited, proved here, computed on random profiles, or interpretation. References marked † are cited from memory and have not been checked against the original.*

## 1. The question

The impossibility theorems of Arrow and Gibbard describe the upper end of the space of voting methods: once a method is good enough, its remaining defects are trade-offs, and no method has all the properties at once. They say nothing about methods that lie below that frontier. A method can be worse than another without any trade-off, if the other does at least as well in every respect that both are judged by. The aim of these notes is to make such comparisons precise for methods that are similar enough to be compared pair by pair.

The comparison has two steps. The first asks for the best use a method can make of the information in the electorate under ideal assumptions about the voters. The second asks for the worst outcome under the same assumptions. If one method is at least as good as another in both, and better in one, the other lies below the frontier. Neither step compares sincere ballots: voters who leave gains on the table are not the point. Both methods are played by voters who follow the same rationale, and the rationale must be stated without reference to the method.

## 2. Information in two stages

The information a method can use is described in two stages: what its ballots can carry, which depends on the method alone, and what it can use when voters fill the ballots strategically.

**Stage 1: what the ballot can carry.** This has two parts.

- *The ballot space* B, the set of ballots a voter may cast. With m candidates, plurality has m ballots (one name), approval 2^m (any set of names), score with scores 0 to k has (k + 1)^m, strict rankings m!, and rankings that allow equal ranks (weak orders) have the ordered Bell numbers, 13 for three candidates and 75 for four. A single ballot can tell at most log₂|B| bits.
- *The count* τ, what the method keeps of the profile of ballots before deciding. An anonymous method keeps at most how many voters cast each ballot (the histogram over B). Additive methods (plurality, approval, score, Borda) keep only the m totals of the candidates. Instant runoff needs more of the histogram; the bottom-two-runoff methods need the first preferences and the pairwise counts. Information can be lost here, before any strategy: the approval profiles {a, b}, {c} and {a, c}, {b} have the same count.

A method A *embeds in* a method B at stage 1 if every ballot of A can be rewritten as a ballot of B, one rewriting for all voters, so that the count of A is a function of the count of B on the rewritten ballots. A voter under B can then say anything a voter under A can, and B still sees what A sees. Plurality embeds in approval (a vote for x as the approval of x alone), approval in score (approval as k, no approval as 0), plurality in instant runoff (a vote for x as any ranking with x first; the plurality count is the count of first preferences), and strict rankings in rankings with equal ranks allowed. Borda embeds in score with k = m − 1: a Borda ballot is a score ballot that uses each score from 0 to m − 1 once. *(Definition; the examples are immediate.)* Stage 1 says what a method could use if voters put into its ballots everything they know. It says nothing about what they will put in.

**Stage 2: what the method can use strategically.** Under the common rationale (Section 4) every voter casts a best reply to a shared poll π. For a fixed poll this maps the profile P of the voters' preferences, unknown to the method, to the count of the strategic ballots,

  E_M^π(P) = τ_M(best replies under M to π, for every voter of P).

This is an *experiment* in the sense of Blackwell (1953): an observation whose distribution depends on an unknown state, here the profile. Under (T) with strict preferences the best replies found so far depend only on the voters' rankings, so the states can be taken as profiles of rankings, a finite set.

Blackwell compares two experiments α and β on the same states in two ways and shows that they agree (cited; his Theorems 3 and 6 for finitely many outcomes, where the converse is due to Sherman and Stein, and Theorem 8 for bounded outcomes):

- α is *more informative* than β if in every decision problem every expected loss that can be attained from observing β can also be attained from observing α;
- α is *sufficient for* β if the observation of β can be produced from that of α by a stochastic transformation that does not depend on the state. β is then also called a *garbling* of α, a later term.

Method A *uses no more strategic information* than method B if for every poll π the experiment E_A^π is a garbling of E_B^π. When the experiments are deterministic, as under (T) without ballot mistakes, a garbling is a function: E_A^π = g ∘ E_B^π for some g, or equivalently, every two profiles that B's strategic count does not tell apart, A's does not either. With ballot mistakes (uncounted marks, *The Common Rationale*, Section 3), random tie-breaking or random electorates the experiments are random, and Blackwell's general form is the one needed. *(Definition; the application of Blackwell's order is ours.)*

Stage 2 does not follow from stage 1. Approval embeds in score, strictly, yet under the common rationale in large electorates the two strategic experiments coincide up to the factor k (*Score and Approval*, Section 1): voters do not use the extra capacity. Whether a method can lie below another at stage 1 and above it at stage 2 is open (Section 7).

Blackwell's order is partial. A quantity that orders every pair, at the price of choosing a distribution of profiles (a culture, for instance impartial culture), is the mutual information between the profile and the strategic count. A garbling never increases it (the data-processing inequality), so it agrees with the order where the order applies. *(Standard; not yet computed for any pair.)*

## 3. The order

**Best case.** Blackwell's first form says exactly that the better experiment is at least as good for every target at once. If A uses no more strategic information than B, then any rule for choosing the winner from A's strategic count, judged by any target, can be matched by a rule reading B's strategic count. The best case of Section 1 is taken in this sense: the best use of the information carried by the strategic ballots, not the best outcome over all polls. An outcome that needs a fortunate poll uses information from outside the electorate, the selection among polls described in *Plurality and Approval*, Section 4. This settles the choice left open in *Plurality and Approval*, Section 10.

**Worst case.** The method's own rule for choosing the winner, at its self-confirming polls (polls that the strategic count reproduces; voting equilibria in the sense of Myerson and Weber 1993): for a given target, the worst winner over them.

**The order.** A *lies below* B, for a given target, if A uses no more strategic information than B and B's worst case is at least as good as A's, with one of the two strict. A and B are *strategically equivalent* if each uses no more strategic information than the other and their worst cases agree.

For plurality and approval under (T): by *Plurality and Approval*, Proposition 1, the strategic plurality count is a function of the strategic approval count at every poll (both front-runners have the same tally under both, and plurality gives the others nothing), and by Proposition 2 every self-confirming approval poll is self-confirming under plurality, with the Condorcet winner as leader. So plurality lies below approval for the majority target, and for the utilitarian target as well whenever there is a Condorcet winner. Without one approval has no self-confirming poll and the worst case has to be read from the walks (*Plurality and Approval*, Sections 5 and 6). Score and approval with large electorates are strategically equivalent. *(From the propositions cited.)*

## 4. The common rationale

Every voter best-responds to the same poll (a leader and a runner-up) under the same assumption on the likelihood of ties, whatever the method. The rationale, its assumptions and their sources are in [The Common Rationale](rationale.md).

## 5. The pairs

| Pair | Note | Result so far |
|---|---|---|
| Plurality and approval | [approval-plurality.md](approval-plurality.md) | Approval's strategic ballot refines plurality's, and its self-confirming polls are among plurality's; plurality lies below approval for targets that depend on the majority relation (under the order of ties). |
| Score and approval | [score-approval.md](score-approval.md) | Score reduces to approval in large electorates for any weights of ties; intermediate scores help only through windows in small electorates. |

Planned: instant runoff and plurality; a Condorcet method and instant runoff, with the Condorcet side from the bottom-two-runoff family (ranked ballots, candidates ordered by an initial count such as plurality, repeated runoffs between the lowest two still in the race; Smith-efficient for any initial order, which can be swapped out); Borda and score; strict and weak rankings.

## 6. Connection with the Equality Criterion

Approval passes the Equality Criterion (an approval ballot and its complement add one approval to every candidate) and plurality fails it (*The Equality Criterion and Reversal*, Section 2). The criterion concerns sincere ballots. *Plurality and Approval*, Proposition 5, part 3, carries it over to strategic ballots for approval: under the common rationale, with any weights of ties, a voter and the opposite voter cast complementary best ballots, so the pair changes no comparison between candidates. *(Proved.)* Under plurality the two best votes go to the candidates with the largest and the smallest coefficient. In the corner these are the two front-runners, and the pair cancels in their race. Away from it they need not belong to one race: with ties between a and b and between c and d both likely, a voter with a > b > c > d votes for a and the opposite voter for d, and the pair tilts both races (*computed example*).

So under the common rationale approval keeps equal and opposite votes for every poll, and plurality keeps them only when a single race dominates. In Proposition 1 of that note the extra information of approval is the row of the leader, each entry a pairwise count on which a ballot and its opposite cancel. Whether failing the criterion always shows up as a choice of self-confirming poll made from outside the profile is open. *(Interpretation and question.)*

## 7. Open questions

1. The worst case without self-confirming polls: when a method has none for a profile (approval without a Condorcet winner), what takes their place in the order, the cycles of the walk or the endpoints of the walk with memory?
2. The further pairs of Section 5: instant runoff and plurality, a bottom-two-runoff method and instant runoff, Borda and score, strict and weak rankings; and whether a method can lie below another at stage 1 and above it at stage 2.
3. Measure the gap in the Ballot Front Finder Lab: the share of profiles in which the strategic outcome depends on the starting poll, per method.
4. The link with the Equality Criterion of Section 6, beyond Proposition 5, part 3.
5. A criterion in the spirit of the Smith set: a method reaches the Smith set under the common rationale within N rounds from every poll. Approval with the leader rule fails it (*Plurality and Approval*, Section 5), rarely; with memory of who has led it holds with N = 2(m − 1) (Section 6 there). Which other methods satisfy it, and is 2(m − 1) the right bound for a rule that does not stop?

## References

- Blackwell, D. (1953). Equivalent comparisons of experiments. *Annals of Mathematical Statistics* 24, 265–272. Pages checked against the original; the volume number from memory.
- *The Equality Criterion and Reversal* (working notes and drafts in this repository).
