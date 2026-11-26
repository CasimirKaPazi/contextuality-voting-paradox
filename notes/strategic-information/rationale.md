# The Common Rationale

*Working note, part of [Strategic Information](README.md). It states the strategic model that every pair of methods in this folder is compared under: the poll, the value of a ballot, the order of ties, and where that order comes from. Conventions as in the [README](README.md).*

## 1. Polls and the value of a ballot

A *poll* is a shared belief about the race, given by a leader a₁ and a runner-up a₂ (in Myerson and Weber 1993, the voters' perceptions of which pairs of candidates are in contention). A voter values a ballot by its effect on pivotal events, in the manner of Myerson and Weber (1993): if s(x) is what the ballot adds to the tally of candidate x and u the voter's utility, a tie between x and y gives the ballot the value (s(x) − s(y))(u_x − u_y). The setting is that of Myerson and Weber's voting equilibria, applied here to the comparison of methods (the *common rationale*: every voter best-responds to the same poll under the same assumption on ties, whatever the method). One assumption on the likelihood of ties is used, in the sense that one tie is so much more likely than another that the second matters only when the first leaves the choice open (a voter then maximises lexicographically, event by event):

- **(T)** for every candidate x other than a₁, the most likely tie involving x is the tie with a₁; the most likely tie involving a₁ is the tie with a₂; ties of three or more candidates are less likely than the ties of two among them.

This is in substance the ordering condition on pivot probabilities under which Myerson and Weber (1993) derive their predictions, as described by Durand, Macé and Núñez (2019). No comparison is made between ties that share no candidate, for instance between a₁ against a₄ and a₂ against a₃. Laslier (2006, Lemma 2) states an order of this kind for large electorates and uses it for the leader rule (his Theorem 1): types of voters replicated n times, scores without ties, and each approval left unrecorded with a small probability ε < 1/v, independently across voters and candidates, where v is the size of the unreplicated electorate. The lemma orders all ties involving a given candidate by the ranks of the others. Its proof covers the ties of a candidate with those ranked below it, which gives the part of (T) concerning the two front-runners. It does not cover the ties of a candidate ranked third or lower with the candidates above it, and in his model that part fails: those ties stay of the same order however large the electorate (Section 3). Here (T) is therefore an assumption, not a consequence of the model of ballot mistakes, and Section 3 describes what replaces it there. The abstract of the published version (Laslier 2009) states the order of ties as a supposition: "It is supposed that voters evaluate the relative likelihood of pairwise ties" from statistical information about the scores, and the Condorcet winner is elected "at equilibrium". Read this way, the published result is Proposition 2 of *Plurality and Approval* with (T) as an assumption about voters' beliefs; the paper itself has not been checked. The assumption is the same for every method, and it is the rationale used throughout.

## 2. Weights away from the corner

Assumption (T) is a limit: each candidate's most likely tie is infinitely more likely than its others. The valuation of Section 1 is defined for any weights. Let p(x, y) = p(y, x) ≥ 0 be the weights of the ties, shared by all voters as part of the poll. A ballot that adds s(x) to the tally of x has the value Σ p(x, y)(s(x) − s(y))(u_x − u_y) over pairs, and this value is linear in s, with the coefficient

  c(x) = Σ_y p(x, y)(u_x − u_y) = w(x)(u_x − E_{π_x} u)

for candidate x, where w(x) = Σ_y p(x, y) and π_x is the lottery that gives each other candidate y the probability p(x, y)/w(x). Call π_x the *virtual opponent* of x.

## 3. Ballot mistakes: Laslier's model at finite electorates

Assumption (T) is meant to come from ballot mistakes: a voter's ballot matters only if the race is close, and mistakes in recording make some close races much more likely than others. Laslier's model makes this concrete: voter types replicated n times, each mark recorded with probability 1 − ε independently, the winner drawn among the highest totals. A mark that fails to be recorded is simply not counted (an *uncounted mark*; Laslier's "trembling ballots"); no mark is ever added that the voter did not make, so a counted tally can fall below the intended one but never rise above it. In this model the best replies can be computed exactly for finite electorates, without the limit and without the linear valuation of Section 1 (`scripts/information/ballot_mistakes.py`, with ε = 1/20 and exact integer arithmetic). *(Computed throughout.)*

**The front-runners.** The ties of the leader and of the runner-up with the other candidates become negligible exponentially fast against the tie between the two: for vote shares 0.55, 0.45, 0.35 and 0.20 the ratio of the leader's tie with the third candidate to its tie with the runner-up is about 10⁻¹¹ at 80 voters and 10⁻⁴⁰ at 320. Accordingly the best plurality vote is the preferred front-runner already in moderate electorates, even in a close race of three, and so is the part of the approval ballot that concerns the two front-runners.

**The other candidates.** A candidate x ranked third or lower can only be pivotal if every candidate above it falls to its level, since a mark can go uncounted but none is ever added. Its ties with the different candidates above it then require the same losses and are of the same order. Their ratios converge to positive constants close to ((s_y − s_x)/(s_{a₁} − s_x))², with s the vote shares: for the shares above, the third candidate's tie with the runner-up weighs about 0.23 of its tie with the leader, and the fourth candidate's ties with the runner-up and with the third weigh about 0.50 and 0.18. The second half of Laslier's Lemma 2, which makes the tie with the leader infinitely more likely, does not hold, and his proof does not cover it.

**Symmetric mistakes.** If a mark can also be added by mistake (with the same probability 1/20), a third candidate can rise as well as the others fall, and the ratios of its ties tend to zero, but slowly: the third candidate's tie with the runner-up weighs 0.047, 0.025 and 0.011 of its tie with the leader at 20, 80 and 320 voters.

What this means for approval and plurality is in [Plurality and Approval](approval-plurality.md), Section 9.

## 4. What is assumed, and where it may break

- **The order of ties.** The whole comparison rests on (T), a large-electorate idealisation with distinct poll scores. In Laslier's model of mistakes (uncounted marks only) (T) holds for the front-runners and fails for the other candidates; with symmetric mistakes it holds in the limit, slowly (Section 3). Without any order of ties, the best approval ballot is a threshold against a virtual opponent, a lottery over the other candidates weighted by the ties (Section 2; *Plurality and Approval*, Proposition 5); (T) is the corner in which all weight lies on one tie per candidate. Proposition 6 there replaces the limit by a finite ratio, and Section 2 there treats exact ties in the poll. The dependence of the weights on the tallies, which the walk needs, is not modelled away from the corner. In large Poisson games, a counterexample to the Condorcet consistency of approval voting is known (Núñez 2010†), so the conclusion of *Plurality and Approval*, Section 4, depends on the strength of this assumption, not only on large numbers. Durand, Macé and Núñez (2019) study which equilibria of approval in Poisson games are stable and how often they elect the Condorcet winner.
- **A shared poll.** All voters respond to the same leader and runner-up. Polls that differ between groups of voters are not covered.
- **Ties.** Pairwise ties and ties between tallies are treated in *Plurality and Approval*, Section 8; only the strictness of defeats along the walk and, with random tie-breaking, the bound on rounds depend on them.
- **Strict preferences, a single winner, no abstention.** Indifferences change the leader rule at the margin; abstention is absent from both methods here.
- **Information in the poll.** *Plurality and Approval*, Section 10, shows that the comparison depends on whether information arriving through the poll is counted. This is a question of definition, not of mathematics; it is settled in the [README](README.md), Section 3, by counting only the information carried by the strategic ballots.
- **Other methods.** The rationale is stated for any method, but best replies under ranked methods (instant runoff, Condorcet methods) are not "one comparison per candidate", and Proposition 1 of *Plurality and Approval* has no analogue yet. A ladder in which a well-played Condorcet method reveals the full matrix is plausible and unproved.

## 5. Open questions

1. Correlated uncertainty: Poisson populations, where Núñez (2010) finds a counterexample to the Condorcet consistency of approval; which condition of *Plurality and Approval*, Proposition 6, fails there?
2. The walk away from the corner: a model of how the weights of ties follow from the tallies, and with it the self-confirming polls and the walk for arbitrary weights. With a continuum of voters and weights that depend continuously on the tallies, Brouwer's theorem would give a self-confirming poll for every profile; where it sits when there is no Condorcet winner is the question.
3. The kind of ballot mistake (Section 3): which models of mistakes or of uncertainty about the tallies give (T), and how fast? With marks only uncounted, the walks lose their guarantees (computed); what are all the equilibria of approval there, and is there a rule for publishing polls that restores the Smith set?

## References

- Durand, F., Macé, A. and Núñez, M. (2019). Analysis of approval voting in Poisson games. Working paper, Paris School of Economics.
- Laslier, J.-F. (2006). Strategic approval voting in a large electorate. Working paper, halshs-00121751, version of 16 June 2006. Lemma, theorem and corollary numbers refer to this version.
- Laslier, J.-F. (2009). The leader rule: a model of strategic approval voting in a large electorate. *Journal of Theoretical Politics* 21, 113–136. doi:10.1177/0951629808097286. The published version; not compared with the working paper.
- Myerson, R. B. and Weber, R. J. (1993). A theory of voting equilibria. *American Political Science Review* 87, 102–114.
- Núñez, M. (2010). Condorcet consistency of approval voting: a counter example in large Poisson games. *Journal of Theoretical Politics* 22, 64–84. doi:10.1177/0951629809348268. † (author from memory)
