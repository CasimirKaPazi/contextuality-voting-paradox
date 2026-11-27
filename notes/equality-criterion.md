# The Equality Criterion and Reversal

*Working note. It reads the Equality Criterion of Wolk, Quinn and Ogren (2023) in terms of the reversal of preferences, the involution that appears throughout* Cycles and Twists *and* Four Levels of Obstruction in Social Choice, *and derives two incompatibilities: with full probabilistic independence and unanimity (from Theorems 5 and 5′ of* Four Levels*), and with strategy-proofness and unanimity (from Gibbard 1977). It ends with what this means for the random fallback of CORE. Ballots are strict rankings throughout. Proved statements, computed checks and interpretation are marked.*

## 1. The criterion

A rule passes the Equality Criterion if for every ballot b there is an opposite ballot b̃, with the opposite preferences, such that adding b and b̃ to any profile does not change the outcome; for rules whose outcome is a lottery, the lottery must not change (Wolk, Quinn and Ogren, Appendix A, Definition 3). On strict rankings the opposite of b is its reverse. The definition also requires the outcome to be unchanged by permuting the ballots, so the criterion includes anonymity. Its purpose, in the authors' words, is that voters who disagree can cast equally weighted and opposite votes, and they connect it with vote-splitting.

## 2. Blindness to the reversal-symmetric part

A ballot together with its reverse is fixed by reversal: reversing every preference exchanges the two. The criterion says that a rule must ignore such pairs. Every profile is a sum of a part that reversal fixes and a part that reversal changes in sign, and in vote shares this is a linear decomposition. The criterion asks, roughly, that the outcome depend only on the second part. For three alternatives the first part is Saari's reversal component, the part of a profile made of rankings paired with their reverses.

**Which rules pass** (proved; checked on random profiles for four alternatives, `scripts/symmetry/equality_criterion.py`):

- **Rules that depend only on pairwise margins pass.** A ranking and its reverse contribute opposite amounts to every margin, so the pair adds nothing. This covers Minimax, Smith//Minimax, Schulze, Ranked Pairs and maximal lotteries, and Gibbard's duple rules (a random pair of alternatives decided by majority).
- **A positional rule with weights w₁ ≥ … ≥ w_m passes exactly when w_k + w_(m+1−k) is the same for every k.** If it is, the pair gives every candidate the same extra score. If it is not, take the profile in which every ranking appears once: all candidates tie, and adding b and its reverse gives candidate c the extra score w_k + w_(m+1−k), with k the position of c in b, which breaks the tie. For three alternatives the condition leaves only Borda; for four, any weights symmetric about the middle, such as (1, 1, 0, 0), pass.
- **Plurality fails**, and in a definite direction: the pair abc, cba gives a point each to a and c and none to b. A balanced pair of voters moves the outcome towards the extremes and away from the compromise. **Antiplurality fails in the other direction**: the pair gives b two points and a and c one each. The criterion excludes a bias against compromise and a bias for it alike.
- **Random ballot and uniform random dictatorship fail.** In a profile where all n voters rank b, the lottery puts probability 1 on b's top (or on b), and adding b and its reverse lowers it to (n + 1)/(n + 2).

*Reading.* A rule that fails the criterion does not treat a voter and the opposite voter as equal and opposite. The space of ballots then has a preferred direction: some strategic moves count for more than their opposites. Plurality's preferred direction runs away from compromise, which is why voters there must abandon their favourite to support a compromise. *(Interpretation.)*

## 3. Two incompatibilities

**Proposition 1.** No rule that assigns to every profile, of every size, a lottery over rankings satisfies full probabilistic independence of irrelevant alternatives, unanimity and the Equality Criterion.

*Proof.* By *Four Levels*, Theorems 5 and 5′, at each size of electorate the rule is a mixture of dictatorships. Its weights are determined by the rule: the weight of voter k is the probability that x is placed above y when k alone prefers x to y. The criterion includes anonymity, so all weights are equal, and the rule is uniform random dictatorship at every size. That fails the criterion (Section 2). ∎

**Proposition 2.** No decision scheme defined for electorates of every size, over at least three alternatives, is strategy-proof, Pareto-optimal and satisfies the Equality Criterion.

*Proof.* By Gibbard (1977), a strategy-proof decision scheme that gives no probability to Pareto-dominated alternatives is a random dictatorship. By anonymity, included in the criterion, it is uniform random ballot, which fails the criterion (Section 2). ∎

**What the proofs use.** Both incompatibilities appear already with electorates of one and of three voters, a single ballot b and a single profile. Let one voter cast b, and let three voters cast b, b̃, b. For Proposition 1 it is enough that the rules for one and for three voters are fully independent and unanimous, that the rule for three voters is anonymous, and that the two profiles receive the same lottery. The rule for one voter is then that voter's dictatorship and gives b probability 1; the rule for three voters is uniform random dictatorship and gives b probability 2/3. For Proposition 2 the same holds with the rule for three voters strategy-proof, Pareto-optimal and anonymous, and the rule for one voter only Pareto-optimal. Pareto-optimality alone makes the single voter's top certain, so Gibbard's theorem is needed for three voters only; the top of b then has probability 1 against 2/3. The criterion asks this equality for every ballot, every profile and every size of electorate; the propositions need it once. *(Proved here, from the cited theorems; checked in Lean, with Gibbard's 1977 theorem as a hypothesis for Proposition 2, `lean/EqualityCriterion.lean`.)*

Both propositions are short consequences of known characterisations. What they show is where the criterion stands. It is satisfied by rules built on pairwise margins, among them maximal lotteries and Gibbard's duple rules, which give up unanimity. It is not satisfied by any of the rules that the characterisations single out: the mixtures of dictatorships, which are the only fully independent and unanimous lotteries, and random ballot, the only strategy-proof and Pareto-optimal one. Equal and opposite votes and strategy-proofness exclude each other once unanimity is required. *(Proved here, from the cited theorems.)*

## 4. The random fallback of CORE

CORE's fallback is uniform random ballot (*CORE and the Formal Results*, Section 2), so by Section 2 it fails the Equality Criterion, in the same direction as plurality. A voter and the opposite voter together raise the chance of the two extremes and lower that of everything between them. The fallback gives a compromise no standing of its own. This is the gamble of Section 3c of *CORE and the Formal Results* seen from the electorate: a compromise can only arise by agreement, never by the draw.

Under CORE this is a deliberate division of labour, not an oversight. By Proposition 2 the fallback cannot be both strategy-proof and equal in the sense of the criterion. CORE takes the strategy-proof side for the fallback and leaves the bias of the draw to be corrected by deliberation, where a balanced pair of participants can agree on the compromise between them. Whether a consensus procedure could instead use a fallback that passes the criterion, such as maximal lotteries, and what it would lose in manipulability, is the comparison of fallbacks left open in *CORE and the Formal Results* (question 4). *(Interpretation, from Proposition 2.)*

At ties the criterion leaves no room for proportionality: for a neutral rule it forces the uniform lottery over candidates at every profile made of reversal pairs, which fails independence of clones. The working note *Equality of Voters and Alternatives* takes this up. It calls the criterion of this note EC-V, equality of voters, and proposes a criterion, EC-VA, that adds independence of clones and states the exception that this forces at ties.

## 5. Reversal elsewhere in the repository

The pairs that the criterion asks a rule to ignore are the fixed points of the involution that *Cycles and Twists* divides by. On the pivotal-voter path of *Cycles and Twists*, Section 5, a mixture of dictatorships passes through exactly such a point, the even mixture of a ranking and its reverse, and a dictatorship jumps across it. Rules that depend only on margins see the profile through the part that changes sign under reversal. Those are the rules that the criterion admits, and the rules on which the obstructions of *Four Levels* act. *(Interpretation.)*

## References

- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Saari, D. G. (2011). Geometry of voting. In *Handbook of Social Choice and Welfare* II, ch. 27, Elsevier.
- Wolk, S., Quinn, J. and Ogren, M. (2023). STAR Voting, equality of voice, and voter satisfaction: considerations for voting method reform. *Constitutional Political Economy* 34, 310–334. doi:10.1007/s10602-022-09389-3.
- *Four Levels of Obstruction in Social Choice*, *Cycles and Twists* (drafts); *CORE and the Formal Results* (working note), all in this repository.
