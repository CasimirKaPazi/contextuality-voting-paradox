# Strategic Information

*Working notes. They propose a way to compare voting methods by how much of the electorate's information they can use when every voter follows the same strategic rationale. This README holds the main idea, the pairs compared so far and the questions that concern all of them. The strategic model shared by all pairs is in [The Common Rationale](rationale.md); each pair has its own note. Statements are marked as cited, proved here, computed on random profiles, or interpretation. References marked † are cited from memory and have not been checked against the original.*

## 1. The question

The impossibility theorems of Arrow and Gibbard describe the upper end of the space of voting methods: once a method is good enough, its remaining defects are trade-offs, and no method has all the properties at once. They say nothing about methods that lie below that frontier. A method can be worse than another without any trade-off, if the other does at least as well in every respect that both are judged by. The aim of these notes is to make such comparisons precise for methods that are similar enough to be compared pair by pair.

The comparison has two steps. The first asks for the best use a method can make of the information in the electorate under ideal assumptions about the voters. The second asks for the worst outcome under the same assumptions. If one method is at least as good as another in both, and better in one, the other lies below the frontier. Neither step compares sincere ballots: voters who leave gains on the table are not the point. Both methods are played by voters who follow the same rationale, and the rationale must be stated without reference to the method.

## 2. The common rationale

Every voter best-responds to the same poll (a leader and a runner-up) under the same assumption on the likelihood of ties, whatever the method. The rationale, its assumptions and their sources are in [The Common Rationale](rationale.md).

## 3. The pairs

| Pair | Note | Result so far |
|---|---|---|
| Plurality and approval | [approval-plurality.md](approval-plurality.md) | Approval's strategic ballot refines plurality's, and its self-confirming polls are among plurality's; plurality lies below approval for targets that depend on the majority relation (under the order of ties). |
| Score and approval | [score-approval.md](score-approval.md) | Score reduces to approval in large electorates for any weights of ties; intermediate scores help only through windows in small electorates. |

Planned: instant runoff and plurality; a Condorcet method and instant runoff, with the Condorcet side from the bottom-two-runoff family (ranked ballots, candidates ordered by an initial count such as plurality, repeated runoffs between the lowest two still in the race; Smith-efficient for any initial order, which can be swapped out); Borda and score; strict and weak rankings.

## 4. Connection with the Equality Criterion

Approval passes the Equality Criterion (an approval ballot and its complement add one approval to every candidate) and plurality fails it (*The Equality Criterion and Reversal*, Section 2). The criterion concerns sincere ballots. *Plurality and Approval*, Proposition 5, part 3, carries it over to strategic ballots for approval: under the common rationale, with any weights of ties, a voter and the opposite voter cast complementary best ballots, so the pair changes no comparison between candidates. *(Proved.)* Under plurality the two best votes go to the candidates with the largest and the smallest coefficient. In the corner these are the two front-runners, and the pair cancels in their race. Away from it they need not belong to one race: with ties between a and b and between c and d both likely, a voter with a > b > c > d votes for a and the opposite voter for d, and the pair tilts both races (*computed example*).

So under the common rationale approval keeps equal and opposite votes for every poll, and plurality keeps them only when a single race dominates. In Proposition 1 of that note the extra information of approval is the row of the leader, each entry a pairwise count on which a ballot and its opposite cancel. Whether failing the criterion always shows up as a choice of self-confirming poll made from outside the profile is open. *(Interpretation and question.)*

## 5. Open questions

1. Settle the definition of the best case (*Plurality and Approval*, Section 10), and with it state the dominance order on methods in general.
2. Instant runoff and plurality under the same rationale; then a Condorcet method against approval.
3. Measure the gap in the Ballot Front Finder Lab: the share of profiles in which the strategic outcome depends on the starting poll, per method.
4. The link with the Equality Criterion of Section 4, beyond Proposition 5, part 3.
5. A criterion in the spirit of the Smith set: a method reaches the Smith set under the common rationale within N rounds from every poll. Approval with the leader rule fails it (*Plurality and Approval*, Section 5), rarely; with memory of who has led it holds with N = 2(m − 1) (Section 6 there). Which other methods satisfy it, and is 2(m − 1) the right bound for a rule that does not stop?

## References

- *The Equality Criterion and Reversal* (working notes and drafts in this repository).
