# Borda and Score under a Common Rationale

*Working note, part of [Strategic Information](README.md), first draft. It compares the Borda count with score voting under the rationale of [The Common Rationale](rationale.md). The two differ by one design choice: a Borda ballot is a score ballot with scores 0 to m − 1 that uses each score exactly once. Conventions as in the README. The checks are in `scripts/information/borda_score.py`.*

## 1. Stage 1

Borda embeds in score with k = m − 1: a Borda ballot is a score ballot, and both methods count totals ([README](README.md), Section 2). The capacities are m! ballots against m^m, for instance 2.58 against 4.75 bits for three candidates and 4.58 against 8 bits for four. The converse embedding fails, since a Borda voter cannot give two candidates the same score.

## 2. Best replies

Both methods are additive, so the value of a ballot s at a poll is Σ_x s(x) c(x), with c(x) = Σ_y p(x, y)(u_x − u_y) the coefficient of [The Common Rationale](rationale.md), Section 2.

**Proposition 1 (any weights).** The best Borda ballot ranks the candidates in decreasing order of c(x), giving m − 1 points to the largest. The best score ballot gives k to every x with c(x) > 0 and 0 to the others. *(Proved: the first is the rearrangement inequality, the second is *Score and Approval*, Section 1; both up to ties of measure zero.)*

So score asks of each coefficient only its sign, and Borda only the order of the coefficients. In the corner (T) the front-runners' coefficients dominate: the preferred front-runner has the largest, the other the smallest. The best Borda ballot puts the preferred front-runner first and the other last, the strategy known as burying. The middle is ordered by c(x) ≈ p(x, a₁)(u_x − u_{a₁}), which depends on how the ties of the other candidates with the leader compare and on intensities, and (T) does not fix it. Below, the ties of the other candidates with the leader are taken as equally likely, written (E); then the middle is in sincere order. *(Assumption made here; the effect of dropping it is in Section 3.)* The best score ballot is k times the approval ballot of the leader rule.

## 3. Stage 2

**Proposition 2.** In the corner (T) with (E) and three candidates, the Borda ballot is a function of the score ballot: both show the preferred front-runner, and the Borda ballot shows nothing else, since the third candidate is always in the middle. So Borda uses no more strategic information than score. With four or more candidates neither ballot is a function of the other: the Borda ballot shows the order of the middle candidates, the score ballot shows which of them stand above the leader. *(Proved, from Proposition 1 and the lemma of the [README](README.md), Section 2.)*

In bits under impartial culture (exact over all rankings; *computed*):

| m | H(Borda) | H(score) | H(Borda \| score) | H(score \| Borda) |
|---|---|---|---|---|
| 3 | 1.00 | 1.92 | 0 | 0.92 |
| 4 | 2.00 | 2.79 | 0.67 | 1.46 |
| 5 | 3.58 | 3.64 | 1.79 | 1.85 |
| 6 | 5.58 | 4.47 | 3.27 | 2.15 |

H(Borda) = 1 + log₂ (m − 2)!, one bit for the front-runners and the sincere order of the middle; H(score) is the formula of *Plurality and Approval*, Section 11. From six candidates on, the strategic Borda ballot carries more bits than the strategic score ballot, although each carries a part the other lacks. Away from the corner (weights P₀ + λR as in *Plurality and Approval*, Section 11) the zero for three candidates becomes 0.03 bits at λ = 0.01 and 0.74 bits at λ = 1, and for more candidates both conditional entropies stay large (*computed*). This is the trade-off that Giles and Postl describe for small electorates with private information: approval expresses intensity but does not convey the full ordinal ranking (cited). Here it appears among strategic ballots: score keeps one threshold per candidate, Borda one order.

## 4. Polls

**Proposition 3.** In the corner (T), with any order of the middle, Borda has no self-confirming poll. *(Proved.)*

*Proof.* At a poll (a₁, a₂) with a₁ ahead, a₁ gets (m − 1)N(a₁ > a₂) points and a₂ gets (m − 1)N(a₂ > a₁) with N(a₂ > a₁) < N/2. Every ballot gives the middle candidates the scores 1 to m − 2 between them, so their totals add up to N(m − 1)(m − 2)/2, and the largest is at least N(m − 1)/2, more than a₂'s. The runner-up is overtaken. ∎

So the worst case of Borda has to be read from the walk of polls, where the next poll is the top two of the strategic tallies.

**Proposition 4 (three candidates).** In the corner (T), the poll (a₁, a₂) is followed by the poll (w, x), where w is the winner of a₁ against a₂ by majority and x the third candidate. So from any poll the leader is the Condorcet winner after at most two rounds and stays so; without one the leader moves around the cycle. *(Proved; checked on random profiles.)*

*Proof.* The middle candidate x gets one point from every voter, N in all. The winner w of a₁ against a₂ gets 2N(w > the other), more than N, and the loser less than N. ∎

With three candidates the strategic Borda walk is therefore a sequence of pairwise contests in which the winner meets the remaining candidate. With four or more candidates a *dark horse* appears: a middle candidate that many voters rank high in the middle can overtake the leader without beating it. On random profiles with a Condorcet winner (101 voters, every ordered pair as starting poll), the Condorcet winner ends as the steady leader of the walk in 69 and 49 per cent of the walks for four and five candidates under impartial culture and in 59 and 45 per cent in the spatial model; in 7 to 17 per cent it never leads again. *(Computed.)* Score, like approval, has the Condorcet winner as the leader of its only self-confirming poll (*Plurality and Approval*, Proposition 2).

## 5. The order for this pair

With three candidates, in the corner (T): Borda uses no more strategic information than score (Proposition 2), and both bring the Condorcet winner to the lead and keep it there, score at its self-confirming poll and Borda through its walk (Proposition 4). Borda lies below score for the majority target, at stage 2 only. With four or more candidates the pair is not ordered at stage 2, since each strategic ballot carries information that the other lacks, while in the worst case score is ahead: Borda's walk often loses the Condorcet winner to a dark horse. *(From Propositions 2 to 4 and the computations.)*

The design choice behind the pair, requiring each score exactly once, removes the threshold from the strategic ballot and puts an order in its place. With three candidates the order is empty and only the loss shows; from four candidates on it is a real trade, and its cost is that no poll confirms itself. *(Interpretation.)*

For comparison, Myerson (2002) compares scoring rules for three candidates, among them Borda, by their equilibria in large Poisson games (cited); the equilibria there rest on a finer calculus of pivot probabilities than the corner used here.

## 6. Open questions

1. Without (E): in Laslier's model the ties of the middle candidates with the leader differ with their tallies, so the middle of the Borda ballot is no longer sincere. How does that change Proposition 2 for four or more candidates and the dark horses of Section 4?
2. The smooth model, as for instant runoff: do Borda's polls settle anywhere away from the corner, and where?
3. A Borda walk with memory, as for approval (*Plurality and Approval*, Section 6): does it keep the Condorcet winner for four or more candidates?

## References

- Giles, A. and Postl, P. Equilibrium and effectiveness of two-parameter scoring rules. *Mathematical Social Sciences* (2014). † Journal and year taken from the file name of the author's version (https://discovery.ucl.ac.uk/10157804/1/ScoringMSSFinalDec13.pdf), not checked.
- Myerson, R. B. (2002). Comparison of scoring rules in Poisson voting games. *Journal of Economic Theory* 103(1), 219–251. doi:10.1006/jeth.2001.2830.
