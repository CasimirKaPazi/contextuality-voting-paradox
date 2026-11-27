# The Honest Axis

*Working note, part of [Strategic Information](README.md), first draft. The other notes compare methods under strategy. This note adds the second axis that a complete comparison needs: what a method achieves when every voter is honest. The two axes are not of the same kind. Honest voting with the utilitarian target is the ideal, the best result if nobody looks at the polls; strategic voting is where voters who do look at them are drawn, and its natural target is the majority relation. The note defines the honest measure in the terms of the README, shows which methods hold the utilitarian sum under honesty, and describes the direction from the honest end to the strategic one as the sharpening of the voters' beliefs. Proved statements and interpretation are marked; nothing is computed. Conventions as in the README; the normalisations as in [Intensities and the Utilitarian Target](intensity.md).*

## 1. Honest ballots and the honest count

Under strategy a ballot is a best reply to a belief. Under honesty it is a report, and each method needs a statement of what an honest report is. A voter's utilities enter only up to scale (*Intensities and the Utilitarian Target*, Proposition 1, holds for honest reports on a bounded ballot as well: the ballot has a largest and a smallest value), so honest ballots are stated for utilities brought to a common scale. Write ν(u) for the voter's utilities with the worst candidate at 0 and the best at 1.

| Method | Honest ballot |
|---|---|
| Plurality | the favourite |
| Approval | the candidates above the voter's mean utility |
| Score, 0 to k | k ν(u), rounded to whole scores |
| Borda, and every method on rankings | the voter's ranking |
| Round ballots | the utilities with mean zero and variance one |

*(Conventions. For approval there is no agreed honest ballot; the mean is the choice of a voter without information and is used here. Another choice changes the approval row of the tables below and nothing else.)*

The *honest count* of a profile is the count of the honest ballots. Like the strategic count of the README, Section 2, it is a linear function of the histogram of types, and the two stages of information apply to it with the honest ballot in place of the best reply. A poll plays no part: the honest count is one map, where the strategic count is one for every poll.

The target on this axis is the utilitarian one, for a stated normalisation: the candidate with the largest sum of ν(u) over the voters, or of the utilities with mean zero and variance one.

## 2. Which methods hold the utilitarian sum when voters are honest

**Proposition 1.** The honest count of a method contains the normalised utilitarian sums, for every profile, exactly when the voter's normalised utilities can be recovered, by one linear function for all voters, from what the honest ballot adds to the count. Among the methods of the table this holds for score voting with a continuous scale (for the normalisation ν) and for round ballots (for mean and variance), and for no method with finitely many ballots.

*Proof.* The sums are linear in the histogram of types with the normalised utilities as coefficients; by the argument of the README, Section 2, Proposition, they are determined by the honest count exactly when they are combinations of its rows. A method with finitely many ballots has rows with finitely many values, and the normalised utilities take a continuum. ∎ *(Proved.)*

**Proposition 2 (finite scales).** With scores 0 to k and n honest voters, the winner of score voting has a sum of normalised utilities within n/k of the largest: on average over the voters, within 1/k of the best candidate.

*Proof.* Each honest score differs from k ν(u) by at most one half, so each total, divided by k, differs from the sum of ν(u) by at most n/(2k). The winner has the largest total. ∎ *(Proved.)*

**Proposition 3 (the honest order).** The honest ballots of plurality, of approval and of the methods on rankings are functions of the honest ballot of score voting with a continuous scale. The honest plurality ballot is a function of the honest ranking. Neither the honest approval ballot nor the honest ranking is a function of the other.

*Proof.* The favourite, the ranking and the candidates above the mean are read off from ν(u), and the favourite from the ranking. Two voters with the same ranking can have different candidates above their means, and conversely. ∎ *(Proved.)*

So on the honest axis the order is the order of stage 1: what the ballot can carry. Finer scores are better, without limit, and a ranking and an approval ballot are two different reductions of a score ballot, neither above the other. This is the reverse of the strategic axis, where intermediate scores carry nothing (*The Ballot Polytope*, Proposition 3). Rankings hold no intensities at all; how far a rule on rankings can then be from the utilitarian winner is the subject of the literature on distortion (Procaccia and Rosenschein 2006†) and is not taken up here.

## 3. From honest to strategic

**Proposition 4.** In the linear regime, at the belief in which all pairwise ties are equally likely, the honest ballot is a best reply under plurality, approval, Borda and round ballots. Under score voting with three or more score levels, an honest ballot with an intermediate score is the unique best reply at no belief.

*Proof.* At that belief the best ballot is the point of the ballot polytope furthest in the direction of the utilities with their mean subtracted (*Intensities and the Utilitarian Target*, Proposition 2), and for the four methods this is the honest ballot of the table. A score ballot with an intermediate score is not a vertex of the cube (*The Ballot Polytope*, Proposition 2). ∎ *(Proved.)*

The belief in which all ties are equally likely is the belief of a voter who knows nothing about the race. So for the methods of Proposition 4 honesty is not opposed to strategy: it is the strategy of the uninformed. The honest count is the strategic count at one particular poll, the empty one.

This gives the direction between the two axes. A voter's belief can be anywhere between knowing nothing and knowing the other ballots. At the first end the best reply is the honest ballot, and it reveals the most: under Borda the whole ranking, under round ballots the intensities (*What a Ballot Reveals*, Section 5; *Intensities and the Utilitarian Target*, Section 3). At the other end the voter chooses among attainable winners and reveals one comparison at most (*What a Ballot Reveals*, Proposition 3). Polls move the voters from the first end towards the second, and the count that would have been honest becomes the strategic count of a sharper and sharper poll. The empty poll does not confirm itself: once the honest tallies are known the candidates are no longer level, the ties are no longer equally likely, and the honest ballot is no longer the best reply. Where the movement ends is a self-confirming poll, and in the corners those are on the side of the majority relation (*Plurality and Approval*, Proposition 2; *Instant Runoff and Plurality*, Proposition 3). *(Interpretation of the propositions cited.)*

So the two axes are the two ends of one line, and they are not symmetric. The honest end is where a method does best by the utilitarian target and where it cannot stay; the strategic end is where it comes to rest and where the majority relation is what it can still serve. A method is described by what it holds at each end, and by how much it loses on the way.

## 4. Both measures

| Method | Honest count holds | Normalised utilitarian sum, honest voters | Honest ballot a best reply for the uninformed | Strategic end (the ladder of *Bounds from Criteria*, Section 5) |
|---|---|---|---|---|
| Plurality | first preferences | no | yes | one comparison |
| Approval | who is above each voter's mean | no | yes | the leader's row, in its corner |
| Score, 0 to k | the sums within n/(2k) | within 1/k per voter; exactly with a continuous scale | no, for three or more levels | as approval: the count becomes approval's |
| Borda | sums of ranks | no | yes | less than the leader's row in its corner |
| Round ballots | the sums, for mean and variance | yes | yes | no certification of the leader |
| Rankings with a count that contains the margins (BTR-plurality and other Condorcet methods) | the margins, and what else the count keeps | no: no intensities | not examined | up to the whole majority relation, where the beliefs allow |

*(From Propositions 1 to 4 and the notes cited.)*

Three things can be read from the table.

- *Score voting is the method with the widest gap between its ends.* Honest, it holds the utilitarian sum as closely as the scale allows; under strategy it is approval. Its honest ballot is the only one in the table that is no one's best reply.
- *Approval, Borda and plurality lose nothing at the first step*: their honest counts are strategic counts. What they hold when honest is modest, and it is what they are designed to hold.
- *Round ballots hold the utilitarian sum and their honest ballot is the uninformed best reply.* On the honest axis they do what score voting does, without asking the voters to act against their interest at the start. What they do as beliefs sharpen is open; they cannot certify a leader (*Intensities and the Utilitarian Target*, Proposition 4).

No method is at the top of both columns. The honest column is led by ballots that are linear in the utilities, the strategic column by counts that keep the margins, and a count of totals cannot be both (*Intensities and the Utilitarian Target*, Proposition 4). *(Interpretation.)*

## 5. Open questions

1. The loss along the line. For each method, the utilitarian quality of the strategic count as a function of the sharpness of the belief, from the empty poll to the corner. In the smooth model the precision s is this parameter, and approval's runs move from the utilitarian winner towards the Condorcet winner as it grows (*The Smooth Model across Methods*, Section 4).
2. The honest measure in numbers, for the methods and profiles of *The Smooth Model across Methods*: how often the honest winner is the utilitarian winner and the Condorcet winner, to set beside the resting polls. The Ballot Front Finder Lab measures the same under its own strategies.
3. Round ballots under sharpening beliefs: self-confirming polls and worst case.
4. The honest ballot under methods on rankings as a best reply: at which beliefs the sincere ranking is a best reply under instant runoff and BTR-plurality.
5. The convention for honest approval, and whether a statement like Proposition 4 singles one out.

## References

- Procaccia, A. D. and Rosenschein, J. S. (2006). The distortion of cardinal preferences in voting. *Cooperative Information Agents X*, Lecture Notes in Computer Science 4149, 317–331. †
