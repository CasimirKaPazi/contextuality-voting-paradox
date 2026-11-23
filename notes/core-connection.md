# CORE and the Formal Results

*Working note for thread G of the roadmap. It places the CORE mechanism (Consensus Or Random Exclusion; `papers/CORE_13.md`) against the results of* Four Levels of Obstruction in Social Choice, Walls and Strategy *and* Consistency as an Extension Problem. *Four connections are stated: a further characterisation of CORE's fallback, from aggregation, with the limit of what electorate conditions say about it; a reading of the draw as the hidden variable of random dictatorship together with an exact decomposition of what participants hold in the sequential variant and the floor against rational groups; the exact place of CORE relative to Gibbard's theorems; and a reading of its bargaining in terms of fixed points. Proved statements, computed checks and interpretation are marked. The note ends with the material it would contribute to a follow-up to the CORE paper.*

## 1. CORE in brief

The participants deliberate toward a unanimously accepted proposal, possibly a lottery. At any time any participant may call for a removal: one participant present, drawn uniformly and possibly the caller, leaves the deliberation but keeps their stake in the outcome. If removals run to the end, the last participant enacts their ideal. The fallback is therefore random dictatorship over the participants, and the value of this lottery to participant i at a set S is i's *endowment* e_i(S), the average of i's utilities for the ideals of the members of S. In the *one-shot* variant a stalled deliberation goes straight to the lottery. In the *sequential* variant, which the paper recommends for all but small groups, smaller groups may agree along the way.

## 2. The fallback from three directions

CORE's paper justifies the fallback by Gibbard's (1977) characterisation, extended by Gibbard (1978), Hylland (1980) and Dutta, Peters and Sen: a strategy-proof rule that chooses an option everyone ranks first is a random dictatorship. The results of this repository give one further characterisation, from aggregation, and examine the fallback from a third side, electorates, where the conditions turn out not to single it out.

**From aggregation.** By Theorems 5 and 5′ of *Four Levels*, for any number of alternatives and voters, every lottery over rankings that satisfies unanimity and full probabilistic independence of irrelevant alternatives (the joint lottery on any set of pairs depends only on the voters' comparisons on those pairs) is a mixture of dictatorships. If it is also anonymous, all weights are equal, so it is uniform random dictatorship (*Four Levels*, Division). Its winner, the top of the drawn voter's ranking, is CORE's fallback. So uniform random ballot is the winner distribution of the only anonymous lottery over rankings that respects unanimity and independence in this joint sense.

Strategy-proofness and independence are different conditions, and the two characterisations are parallel rather than one. On the strategy side, weakening the condition from dominant strategies leaves Gibbard's mixtures of unilateral and duple rules. On the aggregation side, weakening full to pairwise independence leaves rules with subadditive power such as the coin rule (Barberà and Sonnenschein), and the gap between the two is signalling, not contextuality. McLennan (1980) connected additivity of power with strategy-proofness, and is the closest precedent for treating the two together.

**From electorates.** Random ballot is affine in the vote shares. It therefore satisfies consistency read for joint draws of winners (*Consistency as an Extension Problem*, Section 3b) and participation read for joint draws, which is SD-participation: an added voter raises the probability of each initial segment of their own ranking. Both are checked on random profiles (`scripts/core/core_checks.py`, part 2). A fallback that elects every Condorcet winner can have neither (*Four Levels*, Theorem 4; Brandt, Geist and Peters). In the scenario of *Consistency as an Extension Problem*, Section 3c, with joins and one-voter extensions as contexts, random ballot is a global section once the Condorcet principle is dropped.

**The electorate conditions do not single out the fallback.** Every scoring rule with uniform tie-breaking satisfies them as well, and plurality and Borda also satisfy unanimity on first choices (checked on random profiles, `scripts/core/core_checks.py`, part 2). For consistency the reason is short. Let W_p be the set of candidates with the highest score at p. If a candidate wins at both p and q, the winners at p + q are exactly the candidates that win at both, since a score at p + q can reach the sum of the two maxima only for them. So L(p + q)(a) = 1/|W_p ∩ W_q|, which is at least 1/|W_p| + 1/|W_q| − 1; and if a does not win at both, the right-hand side is at most zero. Both conditions are linear in the lotteries for fixed profiles, so mixtures of these rules satisfy them too. The electorate side therefore leaves a convex family that runs from random ballot, which counts first choices in proportion, to plurality, which gives everything to the largest count, and further to rules that use the whole ranking. What separates random ballot within it is proportionality, each first choice getting at least its share, which is CORE's coalition floor and forces random ballot at once, or strategy-proofness, or independence over rankings (the first two columns of the table).

| | strategy | aggregation | electorates |
|---|---|---|---|
| condition | strategy-proofness, unanimity | full independence, unanimity | consistency and participation for joint draws |
| result | random dictatorship (Gibbard 1977; Hylland) | mixtures of dictatorships (*Four Levels*, Theorems 5, 5′) | satisfied by random ballot, and also by every scoring rule; impossible with the Condorcet principle |
| with anonymity | uniform random dictatorship | uniform random dictatorship | |

**What CORE does with the dropped condition.** The fallback ignores the pairwise structure, which is how it escapes the level-1 obstructions. CORE reintroduces that structure only through unanimous improvement on the fallback, which is not a rule applied to a profile. A Condorcet winner can be agreed on under CORE only if everyone prefers it to the lottery, and then only as one of the options the bargaining may settle on; that it is a Condorcet winner plays no role. A Condorcet winner that some participant finds worse than the lottery cannot be enacted with certainty. Maximal lotteries, the other distinguished lottery (*Consistency as an Extension Problem*, Section 4), make the opposite choice: they keep the Condorcet principle and are consistent and participatory only for lotteries compared as wholes. *(The comparison is a reading of the cited and computed facts.)*

## 3. The draw is the hidden variable

In *Four Levels*, random dictatorship is non-contextual with one hidden variable, the identity of the dictator, and becomes strongly contextual once the voters' permutations are divided out: its hidden variable is the symmetry break. CORE makes this variable physical. Let D be the participant who would be left if removals ran to the end.

**Proposition (martingale).** Under uniform removals, given the current set S of participants, D is uniformly distributed on S. Hence

  e_i(S) = E[ u_i(a*_D) | the removals so far ],

and the endowments e_i(S_0), e_i(S_1), … along any sequence of calls form a martingale.

*Proof.* By induction on |S|: the removed participant is uniform on S, and given who was removed, by the induction hypothesis D is uniform on the rest; so each member of S is D with probability 1/|S|. The second statement is the definition of e_i(S) as the average over S. A conditional expectation of a fixed random variable along an increasing flow of information is a martingale. ∎

The fair-call results of the CORE paper follow at once. Theorem 1 (a call leaves the expected endowment unchanged) is the martingale property for one step. Corollary 1.1 (any sequence of calls, decided in any way on what has happened) is optional stopping for a stopping time bounded by n − 1. Corollary 1.3 (the caller must stand in the draw) is the observation that exemption destroys the uniformity of D: the removals then carry information about who called, not only about D. In the extreme case of a participant who always calls and is exempt, D is that participant with certainty (computed for five participants, `scripts/core/core_checks.py`, part 1). Proposition 5 (sortition preserves the benchmark) is the same statement for a uniform sample S: drawing S and then D uniformly within S leaves D uniform on everyone.

The proposition gives the veil of the CORE paper (Section 11) an exact form. Before an agreement, every participant faces the same unrevealed variable D. The one-shot variant reveals it all at once. The sequential variant reveals it by elimination, one non-dictator at a time, and lets those who remain renegotiate with what they have learned. That is why, in the sequential variant, holdings and benchmark come apart (Section 7 of the paper): the benchmark is the expected value of the ideal of D, a martingale whatever anyone does, while holdings depend on the agreements that smaller groups reach once they know that D is among them. The martingale is about the draw, not about what is enacted. *(Proposition proved here; the reading of the veil is interpretation.)*

## 3a. Holdings: the endowment plus surpluses

The martingale gives the benchmark. What participants actually hold in the sequential variant differs from it, and the difference has an exact form that does not depend on any theory of which agreements groups reach.

Fix any behaviour of the groups: each group S of two or more participants, if the process reaches it, either agrees on some lottery or calls. Let h(S) be the vector of values, to all n participants, of the process from S on, and c(S) the value of a call at S, the average of h(S ∖ {j}) over the members j of S. Call s(S) = h(S) − c(S) the *surplus* of S over its own call; it is zero if S calls.

**Proposition (decomposition of holdings).** For every participant i,

  h_i(V) = e_i(V) + Σ_{S ⊆ V, |S| ≥ 2} s_i(S) / C(n, |S|),

where C(n, k) is the binomial coefficient.

*Proof.* Unfold h(V) = s(V) + c(V) and c(S) = average of h(S ∖ {j}) down to single participants, where h({j}) is the value of j's ideal. Each group S of size k is reached in this unfolding with the probability that uniform removals from V pass through S, which is 1/C(n, k), since the set left after n − k removals is a uniformly random set of size k. The single participants contribute the value of the ideal of D, whose expectation is e_i(V). ∎

In the language of probability this is the Doob decomposition of the holdings with respect to the martingale of Section 3: the endowment is the martingale part, and the surpluses captured along the way are the rest. It is an identity, and holds whatever the groups do (checked on random instances, `scripts/core/core_checks.py`, part 3).

Its consequences:

- **One-shot variant.** Smaller groups never act, so h(V) = e(V) + s(V). A participant who accepts only agreements worth at least a call keeps the endowment, which is Theorem 4 of the CORE paper.
- **Where the shifts come from.** If every participant accepts only agreements worth at least a call, then s_i(S) ≥ 0 for every group S containing i, and

  h_i(V) ≥ e_i(V) + Σ_{S ∌ i} s_i(S) / C(n, |S|).

  Every shortfall below the endowment comes from groups that formed without i, through the surplus they captured over their own call, as seen by i. The weights of the groups of size k that do not contain i add up to (n − k)/n, the probability that i has been removed by the time k participants are left.
- **The examples of Section 7 of the CORE paper.** In the first, the pair of participants 2 and 3 agrees on D, with surplus (−105, 4, 4) over the pair's call; the other pairs reach no agreement. The decomposition gives the value of a call at the full group as (6.67, 3.33, 3.33) + (−105, 4, 4)/3 = (−28.33, 4.67, 4.67), the paper's table. In the second example the same term is positive for participant 1.
- **The endowment is one possible holding.** The lottery a call would lead to is always acceptable, weakly, to every member of a group. If every group adopts exactly that, all surpluses vanish and everyone holds their endowment. The value shifts of the sequential variant are therefore the surpluses of smaller groups. They come from those groups agreeing on something better than their own fallback, which is the purpose of the sequential variant.

The open equilibrium question of the CORE paper is thereby reduced to a question about the surpluses: which surplus vectors s(S) groups capture, and how they fall on participants outside the group. The selection-free part, the endowment, is separated from the selection-dependent part, the weighted sum. *(Proposition proved here; the reduction of the open question is a reformulation, not an answer.)*

## 3b. Against rational groups

The CORE paper's floor in the sequential variant, f_i = t_i/n + ē_i/n + (n − 2)w_i/n (Proposition 2 and Theorem 4 of the paper), is what i can guarantee against arbitrary others. It allows them to agree on i's worst outcome once i is gone, even when that costs them. The question of Section 3a, how large the shortfall from groups without i can be, has a sharper form when the others are only assumed to be rational in the weakest sense.

Call a behaviour of the groups *individually rational* if every group that agrees gives each member at least what a call would give that member, given what happens afterwards. Any member can call at any time, so every equilibrium of any bargaining protocol in the groups has this property. A call at S leads to a lottery over outcomes, so calling is the case in which S agrees on exactly that lottery. Fixing a lottery L_S for every group therefore describes every individually rational behaviour, and the condition is a linear inequality for each member. Write G_i for the least value of the whole process to i over all individually rational behaviour of the groups without i, when i refuses every proposal and calls.

**Proposition (rational floor).** G_i is the most that i can guarantee against individually rational others, and

  f_i ≤ G_i ≤ e_i.

G_i is the value of a linear program in the lotteries L_S of the groups without i.

*Proof.* By Section 3a, the groups containing i contribute surpluses s_i(S) ≥ 0 when i accepts only what is worth a call, and the others can make them zero by refusing whenever i is present, which is individually rational for them. So i's refusal costs i nothing, and against it the others choose the lotteries of the groups without i. The value to i and the constraints of individual rationality are linear in these lotteries. The others can call everywhere, which gives e_i; and an individually rational behaviour is one of the behaviours allowed in the paper's floor, which gives f_i ≤ G_i. ∎

In the example of Section 7.1 of the CORE paper G_1 = f_1 = −28.33: agreeing on D is individually rational for the pair of participants 2 and 3, and it is participant 1's worst outcome. On random instances with independent utilities, G_i lies well inside the interval. Measured in units of i's utility range, it lies above f_i by 0.15 to 0.26 on average and below e_i by 0.015 to 0.08, for three to six participants. G_i < e_i occurs in 9 percent of instances with three participants and in 80 percent with six. The worst behaviour is not found by letting each group in turn do the worst it can to i: smaller groups' choices change the call values, and with them what larger groups may agree on. That is why it is a linear program and not a recursion. Requiring every group's agreement to be Pareto-efficient for its members raises the floor only a little, by 0.01 to 0.05 on average for up to five participants (`scripts/core/rational_floor.py`, parts 1 and 2). *(Computed.)*

**Theorem (one dimension).** Let the outcomes be points on a line, possibly with lotteries over them. Let each participant j have utility u_j(x) = β_j − α_j |x − p_j|, with α_j > 0, and let the peak p_j be an available outcome, so that it is j's ideal. Then under any individually rational behaviour of the groups, at every group S the process reaches, every participant, whether a member of S or not, values what follows at least as much as the random ballot over the members of S. In particular every participant holds at least their endowment at every stage, and G_i = e_i.

*Proof.* The theorem follows from a lemma that does not use the line. Let E_S be the random ballot over the members of S, and suppose that

(∗) for every group S and every participant's utility u there are a_m ≥ 0 for the members m of S and a constant c with u(x) ≥ Σ_m a_m u_m(x) + c for every outcome x, with equality at the ideals of the members.

Then for every u and every reached S, the value under u of the outcome law D(S) from S is at least u(E_S). By induction on |S|: for a single participant, D(S) = E_S. For larger S, the lottery of a call is the average of the laws D(S ∖ {k}), which is worth at least the average of the E_{S∖{k}}, that is E_S, to every u. An agreement L gives each member at least that, so u_m(L) ≥ u_m(E_S). Then u(L) ≥ Σ a_m u_m(L) + c ≥ Σ a_m u_m(E_S) + c = u(E_S), the last step by the equality on the support of E_S.

On a line (∗) holds by two elementary facts. Let q₁ ≤ … ≤ q_s be the peaks of the members of S, and p the peak of u. If q_j ≤ p ≤ q_{j+1}, then |x − p| ≤ λ|x − q_j| + (1 − λ)|x − q_{j+1}| with λ = (q_{j+1} − p)/(q_{j+1} − q_j), with equality for every x outside the open interval between q_j and q_{j+1}, and so at every member's peak. If p ≤ q₁, then |x − p| ≤ |x − q₁| + (q₁ − p), with equality for every x ≥ q₁; the case p ≥ q_s is symmetric. Rescaling by α and shifting by β keeps the weights non-negative. ∎

So with one issue and losses proportional to distance, rationality of the others is enough: no group can push a participant below their endowment, the harm of Section 7.1 of the CORE paper cannot occur, and joining is safe against rational others exactly when e_i ≥ o_i, as in the one-shot variant. The effect of Section 7.2, a removed participant gaining from the others' compromise, remains possible. The reason is visible in the proof. A compromise that every member accepts is pulled towards the middle of the members. To someone between two members it is at least as good as the lottery over them, because the loss is convex in position. To someone outside the members it is no worse, because the lottery already places everything on the far side.

**Where it stops.** Each hypothesis matters (`scripts/core/rational_floor.py`, part 3; largest shortfall in units of utility range, over 370 participant–instance pairs with four to six participants). With peaks that are not available outcomes, so that a participant's ideal is only the nearest outcome, G_i < e_i occurs in 146 cases, by up to 0.07. With quadratic loss it occurs in 302 cases, by up to 0.045. For distance in the plane it occurs in 108, by up to 0.011. With a concave loss such as the square root of the distance it never occurs, for a different reason.

**Proposition (concave loss).** Let the outcomes be points on a line, u_j(x) = β_j − α_j h(|x − p_j|) with α_j > 0 and h strictly concave and increasing, h(0) = 0, and let every peak be an available outcome. For a group S with distinct peaks q₁ < … < q_s, let A_S be the matrix with entries h(|q_k − q_m|).

1. A lottery that puts mass away from the members' peaks is strictly worse for every member than one that moves that mass onto the peaks.
2. A_S is invertible and the weights w = A_S⁻¹ 1 are all positive. They are proportional to the lottery over the peaks that maximises the expected loss h(|X − Y|) between two independent draws X, Y from it.
3. The random ballot over S is the only lottery that every member weakly prefers to it.
4. The only individually rational behaviour is that every group calls. The sequential variant then coincides with the one-shot variant, and every participant holds exactly their endowment.

*Proof.* 1. Mass at x between consecutive peaks, x = λq_k + (1 − λ)q_{k+1}, is moved to q_k and q_{k+1} with weights λ and 1 − λ. No member's peak lies strictly between them, so for every member m, |x − q_m| is the same mixture of |q_k − q_m| and |q_{k+1} − q_m|, two different numbers. Strict concavity of h makes the loss at x larger than the mixture of the losses. Mass beyond the extreme peaks is moved to the nearest of them, which brings it closer to every member.

2. One fact does the work. Let v ≥ 0 be weights on a set T of peaks, not all zero, and F(x) = Σ_{m∈T} v_m h(|x − q_m|). If F takes the same value c at every point of T, then F > c at every peak outside T. Between consecutive points of T every term is h of a non-constant affine function of x, so F is strictly concave there and lies above its value c at the ends; beyond the extreme points of T every distance grows, so F grows.

   Existence: let p* maximise pᵀA_S p over the lotteries p on the peaks. Moving a little mass from a peak in its support to any other peak cannot increase the value, so (A_S p*)_k equals some λ > 0 on the support of p* and is at most λ elsewhere. By the fact, with v = p*, no peak lies outside the support, so p* is positive and A_S (p*/λ) = 1. Invertibility: if A_S c = 0 with c ≠ 0, move along w + tc from w = p*/λ until a first coordinate reaches zero. This gives weights v ≥ 0, zero at some peak, with A_S v = 1, so F = 1 at every peak, which the fact excludes. So w = p*/λ is the unique solution, and it is positive.

3. By 1, a lottery that every member weakly prefers to the random ballot u lies on the peaks, say p (with u its weights on the distinct peaks, if members share a peak). The members' losses are the entries of A_S p and A_S u, after rescaling each member's utility. Since A_S is symmetric and A_S w = 1, the weighted totals wᵀA_S p and wᵀA_S u both equal 1. With positive weights no entry of A_S p can be smaller than that of A_S u without another being larger, so A_S p = A_S u, and p = u by invertibility.

4. By induction on the size of the group: if every smaller group calls, a call at S leads to the random ballot over S, and by 3 that is the only individually rational lottery at S. ∎

For three members the weights are explicit. Write x = h(q₂ − q₁), y = h(q₃ − q₂) and z = h(q₃ − q₁); then w = ((x + z − y)/(2xz), (x + y − z)/(2xy), (y + z − x)/(2yz)), and the middle weight is positive exactly because z < x + y, the strict triangle inequality that strict concavity gives. With linear loss the most spread-out lottery puts everything on the two extreme peaks, the interior weights vanish, and the argument stops: that is where compromises begin to have value. The script checks the positivity numerically for 2 to 11 members and several losses, and shows a zero weight for min(d, 0.3), which is concave but not strictly (part 5). *(Proved here.)*

The three cases make a scale. With strictly concave loss no lottery improves on the random ballot of a group for all its members, so the fallback is already efficient for every group and there is nothing to agree on. With linear loss compromises gain, and by the theorem they never harm anyone outside the group. With convex loss, such as quadratic, they gain and can harm those outside. Among the one-dimensional cases computed, the harm of Section 7.1 of the CORE paper occurs only with loss beyond linear or with ideals away from the peaks. *(Theorem and proposition proved here; the limits computed.)*

## 3c. Who can agree: curvature as attitude to risk

Read the other way round, Section 3b says that the random ballot is a floor no rational group can be argued out of, and that gains from agreement appear only where losses are at least linear in distance. Participants need not share one curvature. A loss h(d) that is concave in distance prefers a gamble over near and far positions to a sure middle one: it is risk-seeking about position. A linear loss is risk-neutral, a convex loss risk-averse. The random ballot is a gamble, and agreement under CORE is the removal of part of that risk. Who can agree with whom is then a question about the mixture of attitudes in a group.

**Proposition (concave and linear members).** Let the outcomes be points on a line, let every member j of a group S have loss h_j(|x − p_j|) with h_j increasing, h_j(0) = 0 and h_j either strictly concave or linear, and let every peak be an available outcome. Call the members whose peak is the leftmost or the rightmost the *extremes*.

1. If every extreme has linear loss and some member's peak lies strictly between the outermost peaks, the random ballot over S can be improved: some member gains strictly and none loses.
2. If S has two members, the random ballot cannot be improved.
3. If S has three members with distinct peaks and an extreme has strictly concave loss, the random ballot cannot be improved.

*Proof.* 1. Let q₁ < q₂ ≤ … ≤ q_{s−1} < q_s be the peaks. Move a small mass a from q₁ to q₂ and a mass b from q_s to q_{s−1}, with a(q₂ − q₁) = b(q_s − q_{s−1}). The mean of the lottery is unchanged and all its mass stays between the extremes. On that interval a linear extreme's loss is the distance of the mean from its peak, so both extremes are indifferent. Every member that is not an extreme has its peak between q₂ and q_{s−1}, so every unit moved comes strictly closer to it: each of them gains strictly, whatever the shape of their loss. 2. Mass between the two peaks is weakly worse for both members than the same mass split onto the peaks, by concavity. On the two peaks, more weight for one is less for the other. 3. Write t = q₂ − q₁ and D = q₃ − q₁, and look for positive weights λ such that F(x) = Σ_j λ_j h_j(|x − q_j|) takes the same value at the three peaks. Solving the three linear equations, the weights of the two extremes are always positive. The middle member's weight is positive exactly when

  h₁(t)/h₁(D) + h₃(D − t)/h₃(D) > 1.

For a linear extreme the ratio is t/D or (D − t)/D, so two linear extremes give exactly 1. Strict concavity of either extreme raises its ratio above that, so the sum exceeds 1. With positive weights, F is concave between consecutive peaks, since every term is, and grows beyond them. So F is at least its common value c at every outcome. The weighted total loss of a lottery is its average of F, which is at least c and equals c at the random ballot. A lottery that no member finds worse therefore makes no member better. ∎

For more members, the converse of 1 is computed, not proved. In 4,000 random groups of 2 to 7 members with individual exponents h_j(d) = d^γ_j, γ_j < 1 or γ_j = 1, the random ballot could be improved exactly when both extremes were linear and a peak lay between them (`scripts/core/curvature.py`, part 1; the construction and the three-member weights in part 2). For a single strictly concave loss shared by all members the converse holds for any number of members (Section 3b).

So the people at the edges decide. Members inside can be anything; agreement needs both members at the edges to be at least risk-neutral about distance, and then it consists of moving the lottery inwards without moving its mean. A risk-seeking member at an edge prefers the gamble, and every compromise costs them.

**Risk-averse members.** With a convex member in the group, agreement is almost always possible. In random groups of two to four members, the random ballot could be improved in 92 to 100 percent of cases with at least one convex member, against 0 for groups of concave members only and of concave members with one linear member (part 3; groups of linear members only: 0 for two, 1.00 from three). A condition as sharp as the one above was not found.

**Who can be harmed.** The same attitudes decide who loses from agreements made without them (part 4; the linear program of Section 3b, three to five participants, curvature drawn at random). Without other convex participants a risk-seeking outsider is pushed below the endowment in 27 percent of cases, by up to 0.05 of their utility range. The groups' mean-preserving contractions are exactly what they dislike. A linear outsider is affected in 15 percent of cases, by at most 0.002; the source of these small shortfalls has not been traced. A convex outsider is affected in 1 percent, by less than 0.001. Once another participant is convex, everyone is at risk: 78 to 88 percent of cases, by up to 0.09.

*Reading.* The random ballot is the fallback that everyone shares. Agreement is the trade of risk for certainty, and it is available where people at the edges of a group would rather have the average than the gamble. The value shifts of Section 7 of the CORE paper fall on those who would rather have kept the gamble, and on everyone once some participants are risk-averse. *(Proposition proved for the cases stated; the rest computed; the reading is interpretation.)*

## 3d. Particular bargaining rules

Sections 3a–3c bound what groups can do. A definite rule closes the selection question. Let every group S the process reaches bargain over lotteries with its own call as the disagreement point, by one of five rules:
- **utilitarian:** the largest sum of gains;
- **Kalai–Smorodinsky:** the largest equal fraction of each member's best possible gain;
- **Nash:** the largest product of gains;
- **Raiffa, one step:** each member's best individually rational lottery, averaged. This is random dictatorship over the improvements, one level up (Section 5);
- **Raiffa:** that step repeated from the new point until it stops.

**Proposition (mean of the peaks).** Let the outcomes be points on a line, u_j(x) = β_j − α_j|x − p_j| with α_j > 0, and let every peak be an available outcome. Under any individually rational behaviour of the groups, every group S that agrees picks a lottery inside the interval of its members' peaks, whose mean is μ_S, the mean of those peaks. A Pareto-efficient agreement gives every participant, member or not, the value of the point μ_S. So every efficient rule leads to the same holdings, the value of the mean of all peaks, in the one-shot and in the sequential variant alike. *(Proved.)*

*Proof.* By induction, every reached group's call is a lottery inside the interval of its peaks with mean μ_S. For a single participant this is the ideal. A call averages the laws of the groups S ∖ {k}, whose means μ_{S∖{k}} average to μ_S.
- **The mean is pinned.** For the two members at the edges of S, the sum of the expected distances E|X − q₁| + E|X − q_s| is at least q_s − q₁, with equality exactly when X stays in the interval. The call attains it. Individual rationality for both therefore keeps X in the interval and fixes E X − q₁ and q_s − E X, so E X = μ_S.
- **Jensen.** Given the mean, E|X − p| ≥ |μ_S − p| for every p. Mixing the two available outcomes next to μ_S, to give mean μ_S, attains equality for every p that is not strictly between them. That includes every peak, since the peaks are outcomes. This lottery is the best individually rational one for every member at once. ∎

So on a line with linear loss there is no selection problem. Bargaining has one efficient answer, and CORE implements the mean of the ideal points, not the median. The random ballot fixes the mean. The members at the edges, whose losses depend only on the mean, have nothing to trade, and the members in between take the compromise at the mean. The mean is set by the ideals the participants would enact if they were last. A threat to enact another point is not credible, since the last participant has no reason to enact anything but their ideal. *(Interpretation.)*

**Computed comparison** (`scripts/core/bargaining_rules.py`). Shifts against the endowment are in units of each participant's utility range, over 300 participants in instances of three to five participants. The last column gives, for comparison, the largest shortfall that individual rationality alone allows (e − G, Section 3b):

| Family | below endowment | largest shortfall (rules) | largest shortfall allowed | mean gain |
|---|---|---|---|---|
| independent uniform utilities | 18–19 % for every rule | 0.24 (Raiffa, one step) to 0.32 (utilitarian, Nash) | 0.36 | +0.04 to +0.05 |
| line, linear loss | none | 0 | 0 | +0.063, the same for every rule |
| line, quadratic loss | none | 0 | 0.042 | +0.13 |
| plane, distance | 1 % (utilitarian only) | 0.004 (utilitarian), 0 for the others | 0.010 | +0.03 |

With spatial structure, the natural rules do not realise the harm that individual rationality allows. It needs a group to pick, among its improvements, one that moves the outcome away from an outsider. Only the utilitarian rule in the plane does so, and slightly. Without structure the harm is common, and the rule changes its size but hardly its frequency: Raiffa's one-step rule, which spreads the gain over the members' own best improvements, harms least. *(Computed; the reading is interpretation.)*

## 3e. Beyond the line: the mean rule

The proposition of Section 3d builds the agreement from points on a line. Building segments between the peaks, then segments between points of those, and so on, fills out the convex hull of the peaks. On that outcome space one part of the result survives in every dimension, and one part does not.

Let the outcomes form a convex set X containing every participant's ideal, and call the following the *mean rule*: every group S the process reaches agrees on the mean μ_S of its members' ideals.

**The recursion.** Under the mean rule, the call at S is the uniform lottery over the points μ_{S∖{k}}. Since μ_{S∖{k}} = μ_S − (p_k − μ_S)/(|S| − 1), these points are the members' ideals reflected through μ_S and shrunk by the factor 1/(|S| − 1), and their mean is μ_S again. Each step of the sequential variant contracts the configuration about the same point. *(Proved.)*

**Proposition (the mean is safe).** If every participant's utility is concave on X, the mean rule is individually rational at every group the process reaches. Every participant, member or not, weakly prefers μ_S to the call at S, and every participant ends with at least their endowment, in the one-shot and in the sequential variant. This holds in particular for u_j(x) = β_j − α_j h_j(‖x − p_j‖) with any norms and any convex increasing h_j, so that each participant may have their own norm and loss. *(Proved.)*

*Proof.* The call at S is a lottery with mean μ_S, and the random ballot over V is a lottery with mean μ_V. A concave utility values the mean of a lottery at least as much as the lottery (Jensen). A norm is convex and h_j is convex and increasing, so h_j(‖x − p_j‖) is convex in x. ∎

**Efficiency, not uniqueness.** With Euclidean distance and linear loss, no point improves on μ_S for every member of S. The mean lies in the convex hull of the members' ideals, which is the set of efficient points, and every lottery is weakly worse for everyone than its own mean. *(Proved; computed for 200 groups, `scripts/core/mean_rule.py`, part 2.)* On a line with linear loss the mean is the only efficient agreement (Section 3d). In the plane it is one among many: when the ideals are not all on one line, the triangle inequality is strict for every member, so the mean is strictly better than the call for everyone, and every point of the hull close enough to it is efficient and individually rational as well. The selection question returns. *(Proved.)*

**Where it stops.** Concavity is needed. With loss √d, which is risk-seeking in the sense of Section 3c, the mean rule fails individual rationality and leaves participants below their endowment, by up to 0.3 of their utility range in random instances (part 1).

**The rules near the mean** (part 3; the plane, Euclidean distance, three and four participants, 37 instances). The outcomes are the ideals, the means of all groups and four further points of the hull:

| Loss | rules below endowment | distance of the rules' expected outcome from μ_V | mean gain, mean rule | mean gain, rules |
|---|---|---|---|---|
| distance | none, for every rule | 0.011 (utilitarian) to 0.027 (Kalai–Smorodinsky) | +0.092 | +0.074 (Raiffa, one step) to +0.095 (utilitarian) |
| squared distance | none | 0 for utilitarian and Nash, up to 0.013 (Raiffa, one step) | +0.252 | +0.238 to +0.252 |

With the groups' means available as outcomes, none of the five rules harms anyone in the plane. With only arbitrary points available, the utilitarian rule did in 1 percent of cases (Section 3d). The rules settle close to the mean, and with squared distance the utilitarian and Nash rules choose it exactly. The utilitarian choice is the mean for equal weights, since the mean minimises the sum of squared distances. *(Computed.)*

*Reading.* The mean rule is a canonical selection: symmetric, consistent along the removal process, and harmless to everyone whenever attitudes to risk about position are neutral or averse. It needs the compromise points to be available. In the plane, harm to outsiders appeared only where they were missing. For deliberation this suggests putting the averages of the positions on the table. *(Interpretation.)*

## 3f. Agreements that are safe for everyone

Section 3e shows that the mean rule harms no one. It is the extreme case of a whole class of agreements with that property, and the class has a known characterisation.

Let the outcomes form a convex set X in a finite-dimensional space, and compare lotteries with finite support. Write L ≤ M (*L is less risky than M*) if every expected utility with a concave utility function on X weakly prefers L to M. By Strassen's theorem this holds exactly when there is a pair (A, B) of random outcomes with A distributed as L, B as M, and E[B | A] = A. In other words, L arises from M by splitting its outcomes into pieces, pooling the pieces into blocks and replacing each block by its mean (in one dimension Rothschild and Stiglitz: M is a mean-preserving spread of L). *(Known.)* Call an agreement *safe* if it is less risky than the call of its group.

**Proposition (safe agreements).** Suppose every group the process reaches agrees on a safe lottery, or calls.

1. Every reached group's outcome is less risky than the random ballot over its members. So every participant with a concave utility, member or not, holds at least their endowment at every stage.
2. Every agreement has mean μ_S, the mean of the members' ideals. The point μ_S is less risky than every lottery with that mean, so every participant with a concave utility weakly prefers it to every other safe agreement. The mean rule is the only rule whose agreements are safe and certain.
3. The outcome from a reached group S can be realised as E[p_D | Z]: the expected ideal of the participant D who would be left last, given some partial information Z about the draw. The random ballot is the case of full information, the mean rule the case of none.

*(Proved.)*

*Proof.* 1. By induction on the size of S. A call averages the outcomes of the groups S ∖ {k}, each less risky than the random ballot over S ∖ {k}, and averages of these ballots give the random ballot over S. Both pooling and averaging respect the order, and the order is transitive. 2. Pooling keeps the mean, and the random ballot over S has mean μ_S. Jensen's inequality gives the rest. 3. By 1 and Strassen's theorem, with B the ideal of a uniformly drawn member of S, which is how D is distributed given S (Section 3). ∎

In the language of Section 3, the mean rule enacts the forecast of the martingale in position rather than in utility. It enacts the expected ideal of the eventual dictator instead of waiting for the draw. A safe agreement decides how much of the draw to reveal before enacting the forecast. On this class there is no selection problem, since everyone who is not risk-seeking prefers to reveal nothing, and that choice harms no one. *(Interpretation.)*

**The rules and the class** (`scripts/core/convex_order.py`). Part 1 checks the proposition with random pooling in every group and random concave utilities. Part 2 tests each agreement of the five rules of Section 3d against its call, by a linear program for the pair (A, B). The setting is the plane, Euclidean distance, the outcomes of Section 3e, three and four participants and 60 instances.

- **Pairs.** A pair's agreements are always safe. Individual rationality for both members confines a lottery to the segment between their ideals with mean at its midpoint (Section 3d), and on a segment every such lottery is less risky than the even lottery over the endpoints.
- **All groups.** Counting all groups reached, pairs included, agreements leave the safe class in about a third of them: 32 percent for the utilitarian rule, 36 to 37 percent for the others.
- **Outsiders.** When an agreement leaves the safe class, an outsider is worse off than under the call of that group only rarely. This happened to 3 of 70 outsiders under the utilitarian rule and 1 of 80 under Kalai–Smorodinsky, by less than 0.004 of their utility range. It never happened under Nash or either Raiffa rule. Over the whole process nobody ended below the endowment (Section 3e).

*(Computed.)* So the rules use the room that the members' particular utilities give them. The gain to the members comes with the loss of the guarantee for those outside, which in these instances is used little.

## 3g. The call structure as a game

Sections 3b–3f ask what groups can and do agree on. The CORE paper leaves open how the calls themselves behave under strategic play. One protocol makes this precise.

At every group S the process reaches, one member is drawn uniformly and proposes a lottery. Then every member accepts or calls. If all accept, the lottery is enacted. Otherwise one member is drawn uniformly and removed, and the game goes on at the smaller group. A single member enacts their ideal. Utilities are known to everyone.

**Proposition (sequential rationality).**

1. Fix what follows each smaller group. A member's vote matters only when every other member accepts, and then it decides between the proposal and the call. So accepting exactly the proposals worth at least the call is weakly dominant. Without this refinement, every behaviour in which all members always call is an equilibrium, and it gives the endowment.
2. In every subgame-perfect equilibrium in undominated votes, the drawn member proposes a lottery that is best for them among those every member weakly prefers to the call. Before the draw, the expected outcome at S is the average of these lotteries over the members: one step of Raiffa's discrete procedure, with the call as disagreement point. The equilibria are found by backward induction over the groups, with one linear program for each possible proposer.
3. If each proposer's best acceptable lotteries all give the other members the same values, the equilibrium values are unique. They are then the holdings of the Raiffa one-step rule of Section 3d.

*(Proved. For two-person bargaining, extensive games of this kind are known to support Raiffa's procedure, with repeated rounds leading to his sequential solution; see Myerson and Trockel. The single step for any number of members is the same elementary argument.)*

*Proof.* 1. If another member calls, the removal happens whatever the vote. 2. By induction on the size of S, the outcome from every smaller group is fixed, and so is the call at S. Given 1, a proposal is enacted exactly when every member weakly prefers it to the call. Any other proposal leads to the call, which the proposer can also obtain by proposing it. The proposer's problem is a linear program over lotteries. 3. Expected utility is linear, so averaging over the drawn proposer gives Raiffa's step. ∎

**Computed** (`scripts/core/call_game.py`; the four families of Section 3d, three to five participants, 56 instances each). The game, computed node by node with acceptance checked, agrees with the Raiffa one-step rule to within 10⁻⁹ (part 1).

- **Uniqueness.** In the uniform, quadratic-line and plane families, every one of the 1,280 proposer problems per family fixed the others' values. On the line with linear loss, 38 percent left them open, by up to 0.34 of the utility range (part 2). A proposer at an edge cares only about the mean (Section 3d), so they are indifferent between lotteries that matter to the members inside. Every such equilibrium is still individually rational, so by the theorem of Section 3b nobody falls below the endowment. Breaking ties in favour of the other members gives the mean of the peaks.
- **What recognition is worth.** At the full group, the drawn proposer gains over the group's expected value by 0.019 of their utility range on average for independent utilities, 0.015 on the line with quadratic loss, 0.008 in the plane and nothing on the line with linear loss. The largest gain was 0.27 (part 3).

*Reading.* This answers Question 3 of Section 6 for complete information.
- **No remainder in the calls.** Calls carry no strategic remainder. With visible moves, sequential rationality solves the call structure by backward induction, as visible turns do in the veto-then-pick example of *Walls and Strategy*.
- **The draw is used twice.** The draw that removes can also recognise who proposes. The uniform symmetry of the fallback then appears a second time, in who speaks first, and the ex ante fairness of Section 3 extends to the proposals.
- **What remains.** Two things remain. One is the choice among a proposer's indifferent options, as on the line. The other is incomplete information: a proposer needs every member's call value, which depends on that member's private utility and on what smaller groups would do. A finite formalisation with private utilities is a game form, and the barrier of Section 4 is expected to return there (not shown).
- **Steering the selection.** Random recognition carries out Raiffa's step, which leaves the safe class of Section 3f in about a third of the groups. A protocol that admitted only poolings of the call as proposals would lead every proposer with a concave utility, weakly, to the mean. It would thus carry out the mean rule. Several rounds of interim agreements within a group would carry out further steps of Raiffa's procedure (Section 5).

*(Interpretation.)*

## 4. Where CORE stands relative to Gibbard

*Walls and Strategy* gives two exact statements that the CORE paper describes in words.

**The dichotomy.** By Theorem 3, every game form with at least three outcomes is dictatorial or has a participant at some preference for whom no program always computes a best reply. By Theorem 6, with lotteries as outcomes, a non-dictatorial procedure either keeps this barrier or is straightforward and inefficient ex ante. CORE's fallback is the straightforward part: the last participant simply enacts their ideal, so there is nothing to compute. Deliberation, which recovers the ex ante gains, is case (i). The CORE paper's Section 9.5 compares this with incompleteness and leaves the comparison as an analogy. Theorem 3 makes it a theorem about any formalisation of deliberation as a finite game form: what remains is a diagonal of the halting type, in substance Canning's (1992), and with opponents required to be rational it is the absence of a strict Nash strategy (Propositions 4, 5 and 5′ for the cases settled).

**A floor computable from inside.** In the one-shot variant a participant's endowment needs only the participants' ideals, not a model of anyone's strategy, and a call secures it. This is the computable floor of *Walls and Strategy*, Section 4. In the sequential variant what can be secured without modelling others is the individual floor of the paper's Proposition 2.

**What does not transfer.** Theorems 3 and 6 concern game forms with finitely many strategies and a fixed set of outcomes. CORE's deliberation has neither: proposals may be lotteries and may introduce options that were on no list (the paper's Theorem 3 on where the gains lie). The theorems therefore bound every way of formalising deliberation as a game form, and say that no such formalisation can remove the barrier while recovering the gains. They do not describe deliberation itself, which is what the paper leaves open on purpose. Whether the open search has properties that no finite formalisation has is a question these results cannot reach.

**Turns.** The observation on simultaneity in *Walls and Strategy* (sequential rationality with visible moves removes the rational diagonal in the veto-then-pick example) bears on the sequential variant: calls are public and taken one at a time, and each removal is observed before the next move. With complete information the remainder disappears: the call structure is solved by backward induction, and with random recognition its outcome is one step of Raiffa's procedure in every group (Section 3g). With private utilities it is not settled. *(Open.)*

## 5. Bargaining, cycles and fixed points

*(Interpretation throughout.)* Section 9.4 of the CORE paper argues that with a fixed set of options that cannot be mixed, revisions of ballots can only circle a Condorcet cycle; that lotteries dissolve the cycle; and that interim agreements, which lock in a gain for everyone, turn circling into convergence, as in Raiffa's procedure. In the terms of *Cycles and Twists* and *The Switch Between Fixed Point and No Fixed Point*:

- circling is the winding of Section 4 of *Cycles and Twists*: on the cycle there is no fixed point, and a revision that climbs at every step never closes;
- admitting lotteries is the switch "adding values": the cycle is filled into a disc, which has a centre, and the uniform lottery is a fixed point of the cyclic renaming;
- locking in gains makes the process monotone in time: no participant's value can fall back, so the process cannot return to an earlier state, and an increasing bounded sequence converges. This is the switch "acyclic covers glue", with acyclicity in time. Raiffa's procedure is also random dictatorship applied again, one level up, over the improvements on the current benchmark.

So CORE uses two of the three switches between no fixed point and a fixed point: it adds values (lotteries) and it removes cycles (lock-in). The third, going around twice, does not appear.

## 6. Questions

1. **The sequential equilibrium.** By Section 3a, what participants hold in the sequential variant is the endowment plus the weighted surpluses of the groups. Which surpluses groups capture is the remaining question. In the language of thread A the surpluses are data on the poset of sub-electorates, one vector per group, constrained only by the individual rationality of the members. How large the shortfall can be under individual rationality alone is settled in Section 3b: it is a linear program, and it is zero on a line with losses proportional to distance. Which families of surpluses arise from particular bargaining rules in every group is answered for five rules in Section 3d: on a line with linear loss every efficient rule gives the same result, the mean of the ideal points, and with spatial structure the rules hardly realise the harm individual rationality allows. Open: whether the floor has a closed form beyond the line (in the plane it falls below the endowment, by little in the cases computed), whether the criterion of Section 3c (both edges linear) holds for any number of members with individual concave losses, what plays its role when some members are convex, and whether the absence of a canonical selection is an obstruction of a definite level. Beyond the line, the mean rule (Section 3e) is a canonical selection that is individually rational and harms no one whenever utilities are concave on a convex outcome space, but it is no longer the only efficient one. It is the least risky of the agreements that are safe for every concave utility, those less risky than the call (Section 3f). The open part of the selection question is therefore what happens outside that class, where the members' particular utilities decide.
2. **Characterisation of the winner lottery.** *Answered negatively in Section 2:* consistency and participation for joint draws, with anonymity, neutrality and unanimity on first choices, leave a convex family containing every scoring rule with uniform tie-breaking. A characterisation of random ballot by conditions on winner lotteries alone needs proportionality or a condition of the strategic kind.
3. **The call structure as a game.** *Answered for complete information in Section 3g:* with a uniformly drawn proposer at every group and undominated votes, the subgame-perfect equilibria are found by backward induction, and their outcome is one step of Raiffa's procedure in every group. Open: private utilities, where a proposer does not know the members' call values, and protocols that steer the selection (for instance proposals restricted to poolings of the call, which leads to the mean rule).
4. **Fallbacks compared.** Section 2 gives one side of the comparison between random ballot and maximal lotteries as fallbacks. A second side is the Equality Criterion (working note *The Equality Criterion and Reversal*): random ballot fails it, in the direction of plurality, while maximal lotteries pass, and no strategy-proof Pareto-optimal fallback can pass it. The other side, how manipulable each is when used as the fallback of a consensus procedure, is open.

## 7. Material for a follow-up

The CORE paper stays as it is, a standalone introduction to the method. What is new here belongs in a follow-up, once it is settled:

- the characterisation of the fallback from aggregation (Section 2), beside Gibbard's and Hylland's from strategy, and the electorate properties of random ballot;
- the martingale proposition (Section 3), from which the fair-call results, the rule that callers stand in the draw and the sortition result follow, and the reading of the veil as the unrevealed draw;
- the decomposition of holdings (Section 3a), which locates the value shifts of the sequential variant in the surpluses of the groups that form without a participant;
- the rational floor (Section 3b): against individually rational others, what a participant can guarantee is a linear program between the paper's floor and the endowment, and on a line with losses proportional to distance it is the endowment, so that joining is safe exactly when the endowment exceeds the outside option; under strictly concave loss on a line no group has anything to agree on, and the sequential variant reduces to the one-shot;
- who can agree (Section 3c): with mixed curvature, a group of concave and linear members can improve on its random ballot exactly when both members at its edges are linear (proved for the construction, for two and three members, computed beyond); convex members make agreement almost always possible, and the harm to outsiders follows the same attitudes to risk;
- the negative answer on the electorate side (Section 2): consistency and participation alone do not single out the fallback;
- CORE's exact place relative to Gibbard's theorems (Section 4), with the limit of what the theorems say about open deliberation;
- particular bargaining rules (Section 3d): on a line with linear loss every efficient rule leads to the mean of the ideal points, so there is no selection problem; with spatial structure the natural rules hardly harm outsiders (only the utilitarian rule in the plane, slightly), while with unstructured utilities about a fifth of participants end below their endowment under every rule;
- the mean rule (Section 3e): with concave utilities on a convex outcome space, agreeing on the mean of the members' ideals in every group is individually rational, consistent along the removal process (each call is the ideals reflected through the mean and shrunk), and leaves everyone at least at the endowment; on a line with linear loss it is the only efficient agreement, in the plane one of many;
- safe agreements (Section 3f): an agreement is weakly better than the call for every concave utility exactly when it arises from the call by pooling outcomes and enacting the block means (Strassen). If every group agrees safely, everyone holds at least the endowment; the outcome is the expected ideal of the eventual dictator given partial information about the draw, and the mean rule, which reveals nothing, is the least risky;
- the call structure as a game (Section 3g): with complete information and a uniformly drawn proposer at every group, accepting exactly what is worth the call is weakly dominant, and the subgame-perfect outcome is one step of Raiffa's procedure in every group, so the calls carry no strategic remainder; the draw that removes can also recognise;
- whatever comes of the questions in Section 6, in particular the sequential equilibrium and the call game with private utilities.

## References

- Barberà, S. and Sonnenschein, H. (1978). Preference aggregation with randomized social orderings. *Journal of Economic Theory* 18, 244–254.
- Brandt, F., Geist, C. and Peters, D. (2017). Optimal bounds for the no-show paradox via SAT solving. *Mathematical Social Sciences* 90, 18–27.
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Diskin, A., Koppel, M. and Samet, D. (2011). Generalized Raiffa solutions. *Games and Economic Behavior* 73, 452–458.
- Dutta, B., Peters, H. and Sen, A. (2007). Strategy-proof cardinal decision schemes. *Social Choice and Welfare* 28, 163–179; erratum 30 (2008), 701–702.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Heitzig, J. and Simmons, F. W. (2012). Some chance for consensus: voting methods for which consensus is an equilibrium. *Social Choice and Welfare* 38, 43–57.
- Hylland, A. (1980). Strategy proofness of voting procedures with lotteries as outcomes and infinite sets of strategies. Mimeo, University of Oslo.
- McLennan, A. (1980). Randomized preference aggregation: additivity of power and strategy proofness. *Journal of Economic Theory* 22, 1–11.
- Myerson, R. B. (1991). *Game Theory: Analysis of Conflict.* Harvard University Press (pp. 393–394).
- Raiffa, H. (1953). Arbitration schemes for generalized two-person games. In *Contributions to the Theory of Games II*, Princeton University Press, 361–387.
- Rothschild, M. and Stiglitz, J. E. (1970). Increasing risk: I. A definition. *Journal of Economic Theory* 2, 225–243.
- Strassen, V. (1965). The existence of probability measures with given marginals. *Annals of Mathematical Statistics* 36, 423–439.
- Trockel, W. (2011). An exact non-cooperative support for the sequential Raiffa solution. *Journal of Mathematical Economics* 47, 77–83.
- *CORE: Consensus Or Random Exclusion* (`papers/CORE_13.md`); *Four Levels of Obstruction in Social Choice*, *Walls and Strategy*, *Cycles and Twists* (drafts); *Consistency as an Extension Problem*, *The Switch Between Fixed Point and No Fixed Point* (working notes), all in this repository.
