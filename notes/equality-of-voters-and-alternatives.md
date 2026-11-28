# Equality of Voters and Alternatives

*Working note. The Equality Criterion of Wolk, Quinn and Ogren (2023) asks that a ballot together with its reverse never changes the outcome: opposite voters weigh the same. It is called EC-V here, equality of voters (see* The Equality Criterion and Reversal*). Independence of clones asks the same of alternatives: none gains or loses by having similar alternatives beside it. This note shows that no rule has both and that two exceptions are forced. It proposes a criterion, equality of voters and alternatives (EC-VA), that states them: EC-V, except at ties that a fraction of a vote can break, and independence of clones, except for candidates that no ballot distinguishes. The definition is in Section 6. Sections 1 to 5 reach it in steps for strict rankings, where only the first exception occurs and a whole vote suffices: the conflict at ties, a first form of the criterion, a tie-breaker with which maximal lotteries pass, and a description of the ties. Section 6 allows equal rankings and gives the definition; Section 7 checks approval and score voting; Section 8 asks what determines the tie-breaker and gives the one in which the drawn voters vote again. Rules give lotteries over candidates and are defined for electorates of every size. Proved statements, computed checks (`scripts/symmetry/equality_voters_alternatives.py`, `equality_equal_rankings.py` for Section 6, `equality_approval_score.py` for Section 7) and interpretation are marked.*

## 1. The two equalities conflict at ties

A *balanced profile* is one made only of reversal pairs: every ballot b occurs as often as its reverse b̃. All pairwise margins of a balanced profile are zero, so every rule built on margins has a full tie there.

**Proposition 1.** A neutral rule that satisfies EC-V gives the uniform lottery over all candidates at every balanced profile.

*Proof.* For balanced profiles P and Q, EC-V gives L(P) = L(P + Q) = L(Q), so all balanced profiles have one lottery. A renaming of the candidates maps {b, b̃} to a balanced profile, so by neutrality the common lottery is fixed by every renaming. ∎

**Proposition 2.** No neutral rule satisfies EC-V and independence of clones (when a candidate is replaced by a group of clones, adjacent on every ballot, the group receives the probability the candidate had and every other candidate keeps its probability).

*Proof.* {ab, ba} is balanced, so a gets ½ by Proposition 1. Cloning a gives {a a′ b, b a′ a}, again balanced, so a, a′ and b get ⅓ each and the group a, a′ gets ⅔. In the same way, from m − 1 to m candidates a cloned group gets 2/m instead of 1/(m − 1). ∎

So the tie value that EC-V allows counts candidates: at {abc, cba} it gives the compromise b one third, and a tie between a and b gives probability to whoever else is on the ballot. The tie value that respects clones counts voters. Random ballot does: at {a a′ b c, c b a′ a} the tops are a and c, as without the clone. But random ballot at ties fails EC-V. At {bac, cab} all margins are zero and random ballot gives b and c one half each; adding abc and cba keeps all margins at zero and gives a ¼, b ¼, c ½. *(Computed, parts 1 and 2 of the script.)* For two candidates the two tie values agree, which is why majority with a fair coin satisfies EC-V.

*Reading.* Each balance axis, the line through b and b̃, has its own symmetric tie value under random ballot, ½ top(b) + ½ bottom(b). EC-V asks for one tie value for all axes at once, and the only one is uniform over the candidates. At a tie a rule can treat opposite voters as cancelling or treat similar alternatives as one, not both. *(Interpretation.)*

*Precedent.* The literature on ranked pairs met the same point from the side of the clones. Tideman's rule with ties between pairs resolved in every possible way is not independent of clones at every profile, and Zavist and Tideman (1989) restore independence by ordering tied pairs with a voter's ballot. *(Cited.)*

## 2. Why the problem sits at the boundary

**Proposition 3.** A rule that depends only on vote shares, satisfies EC-V and is continuous in the shares is constant.

*Proof.* Let p be a profile of n voters and add k copies of the pair b, b̃. The shares tend to those of {b, b̃} as k grows, and the lottery stays L(p). By continuity L(p) = L({b, b̃}) for every p. ∎

So for a rule that satisfies EC-V, every value it takes occurs arbitrarily close to every balanced profile. A balanced profile is not a boundary between two sides; all sides meet there. Random ballot is continuous, which is why it cannot satisfy EC-V. For maximal lotteries the script shows the effect directly: adding a thousand reversal pairs to a cycle leaves the lottery unchanged while the pair makes up more than 99% of the electorate. *(Proved; computed, part 3.)*

**Three candidates.** Write the margins as x = m_ab, y = m_bc, z = m_ca. The tie planes x = 0, y = 0, z = 0 divide margin space into eight cones. In six of them some candidate beats both others. In the remaining two, where x, y, z have the same sign, there is a cycle. For the cycle a > b > c > a the maximal lottery is (y, z, x)/(x + y + z): each candidate is weighted by the margin of the contest it is not part of. It does not change along rays, so shrinking a cycle towards the origin keeps its lottery, and the lotteries of all cycles fill the open triangle. All three tie planes meet only at the origin, where every lottery is maximal, random ballot among them. *(Proved by solving the three inequalities; computed, part 4.)*

On a face of the cycle cone, for example z = 0 with x, y > 0 (a beats b, b beats c, a ties c), the maximal lotteries form the segment from the cycle's limit (y, 0, x)/(x + y) to a, the limit from the side where a beats both others. The rule is undecided exactly on the set that joins the values from the two sides. *(Computed, part 4.)*

*Reading.* A deterministic outcome divides the space into regions and has to assign each boundary point to one of them. A set of lotteries at the boundary does not have to: it contains the values of both sides and what lies between. *(Interpretation.)*

## 3. The criterion, first form

Equality of voters asks for EC-V, equality of alternatives for independence of clones, and by Proposition 2 no neutral rule has both. The criterion keeps both and states the exception. This section gives it in the form it takes for strict rankings; Section 6 gives the definition for ballots of any kind, of which this form is a special case.

For a rule L, call a profile p *settled* if reversal pairs never change the outcome from p on: L(p + Q) = L(p) for every balanced profile Q. Otherwise p is a *tie*. EC-V says that every profile is settled.

**First form (strict rankings).** An anonymous and neutral rule L satisfies equality of voters and alternatives if:

1. **Equal alternatives.** L is independent of clones, at every profile.
2. **Equal voters, except at ties within one vote.** For every tie p there is a ballot r such that p + r is settled.

A settled profile stays settled when reversal pairs are added, so the ties are the profiles at which EC-V is suspended, and condition 2 says how far the suspension may reach: one voter. This is Tideman's resolvability (1987) applied to the failures of EC-V. It makes a tie an exception without reference to a continuum: ties do occur in finite electorates, but each is one voter away from a settled profile. It is also what excludes "the Condorcet winner if there is one, otherwise random ballot": there every cycle is a tie, and a cycle with margins of three or more is still a cycle after one more ballot. For a rule that depends only on margins wherever its outcome is unique, the ties in this sense are among the rule's own ties.

The criterion does not include unanimity or any other condition of responsiveness: like EC-V, it is passed by the reverse of every rule that passes it. It does not restrict how a tie is broken, beyond independence of clones.

**Proposition 4.** If L is neutral and independent of clones, then for three or more candidates every profile that consists of a ballot and its reverse is a tie.

*Proof.* Suppose P = {b, b̃} is settled. For a renaming σ, the profile σP is settled too, by neutrality, and both are balanced, so L(P) = L(P + σP) = L(σP) = σL(P). Hence L(P) is uniform, 1/m for each candidate. The two candidates at the top of b are adjacent on both ballots, so P arises by cloning from P₀ = {b₀, b̃₀} with m − 1 candidates, where one candidate x takes the place of the two. By independence of clones L(P₀) gives x the probability 2/m and every other candidate 1/m. The renaming that reverses b₀ maps P₀ to itself, so L(P₀) gives the top and the bottom of b₀ the same probability. The top is x, and with m − 1 ≥ 2 the bottom is another candidate. ∎

The exception is therefore forced, not a convenience. *(Proved.)*

## 4. Breaking ties

The definition is generous to the tie-breaker: it only has to keep the complete rule anonymous, neutral and independent of clones. Three tie-breakers for maximal lotteries, used wherever the maximal lottery is not unique:

| Tie-breaker | The complete rule is independent of clones | EC-VA |
|---|---|---|
| Uniform lottery over all candidates | no (Proposition 2); the complete rule satisfies EC-V instead | no |
| A random voter chooses among all alternatives | no: fails when clones tie with each other (Proposition 5) | no |
| A random voter chooses the maximal lottery that is best for their ballot | yes (Proposition 6) | **yes** |

**Proposition 5.** Let L be independent of clones and let p′ arise from p by replacing x with clones X. Then L(p′) gives every candidate outside X its probability under L(p), and X in total the probability of x. If p is not a tie and the clones tie with each other, the tie-breaker at p′ can only divide the share of X among its members.

*Proof.* This is independence of clones applied to L at p and p′. ∎

*Example (computed, part 7).* Four voters rank a above b and two rank b above a: a wins with certainty. Replace a by a and a′, with three voters preferring each to the other: a ties a′, both beat b by two, and the maximal lotteries are all lotteries on a and a′. A random voter choosing among all alternatives gives a, a′ and b one third each: cloning the winner has given the loser a chance.

So the tie-breaker in which the drawn voter may choose any alternative does not pass. A tie between clones of a winner would reopen the whole decision. The tie has to be broken with respect to the tie only, and the next proposition gives a way of doing so that keeps the draw of a voter.

**Lemma (clones and maximal lotteries).** Let p′ arise from p by replacing x with clones X. A lottery on the candidates of p′ is maximal for p′ exactly when its merge (the probabilities of X added up into x) is maximal for p and, if the merge gives x positive probability, its division of that probability among X is maximal for the profile restricted to X.

*Proof.* Write π for the merge, s = π_x, and c for the division. For y outside X the condition at y is the same for the lottery and for π. For y in X it reads (πᵀG)_x + s (cᵀG_X)_y ≥ 0. Adding these up with weights c_y gives (πᵀG)_x ≥ 0, since cᵀG_X c = 0 (for s = 0 the condition is this inequality itself); so π is maximal. A maximal π with s > 0 has (πᵀG)_x = 0, because πᵀGπ = 0 is a sum of non-negative terms, and the condition becomes cᵀG_X ≥ 0. The converse reads the same lines backwards. ∎ *(This is composition-consistency of maximal lotteries, Brandl, Brandt and Seedig 2016, for the set of all maximal lotteries.)*

**Proposition 6.** Draw a voter at random and choose, among the maximal lotteries, the one that is best for that voter's ballot in lexicographic order: the largest probability for the voter's first candidate, then, among those, the largest for the second, and so on. Maximal lotteries completed in this way satisfy EC-VA.

*Proof.* The rule is anonymous and neutral, and it is the unique maximal lottery wherever there is one. *Clones.* Fix a voter. By the Lemma the merges of the maximal lotteries of p′ are exactly the maximal lotteries of p, and the division among X can be chosen independently of the merge. For the candidates the voter ranks above X the choice therefore proceeds as in p. At X, let M be the largest probability still available for x. If M = 0 the clones get nothing. Otherwise the probability of a clone is the product of the share of X and the clone's part in the division, and at the first clone that can get a positive part, the largest product requires the share M. Either way X receives M in total, and the choice continues below X as in p. So the voter's best lottery for p′ merges to the voter's best lottery for p, and so does the average over voters. *Ties.* The rule depends only on margins where the maximal lottery is unique, so those profiles are settled; by Section 5 every other profile has an even number of voters and becomes one of them when any ballot is added. ∎ *(Proved; computed on random profiles with ties, with a candidate replaced by two or three clones, part 7.)*

In the example above every voter's best maximal lottery is the voter's favourite of a and a′, so each gets one half and b nothing. The tie-breaker stays inside the set of maximal lotteries by construction. A simpler one does not: with a tying b, a beating c by 2 and c beating b by 4, the maximal lotteries put nothing on c and need p_a ≥ 2 p_b; a random voter's favourite among a and b gives one half each, outside the set, while the voters' best maximal lotteries are a for those who prefer a and (⅔, ⅓, 0) for those who prefer b. *(Computed, part 8.)*

*Reading.* Random ballot by itself is independent of clones. The failure of the second tie-breaker comes from combining a rule that decides with a fallback that forgets what was decided. In the third, the drawn voter decides only what was left undecided. *(Interpretation.)*

**Which rules pass.** The rules of this table are rules on strict rankings, judged by the first form. All of them depend only on the shares of the ballots, so passing the first form means passing the definition of Section 6. Rules are taken with a tie-breaker, since the criterion is about the complete rule. The second and third columns together are condition 2: a rule whose outcomes away from its own ties change under reversal pairs has ties, in the sense of the definition, that no single vote breaks.

| Rule | Independent of clones | A ballot and its reverse cancel, away from the rule's own ties | Each of the rule's ties is within one vote | EC-VA |
|---|---|---|---|---|
| Maximal lotteries, ties broken by a random voter's best maximal lottery | yes (Proposition 6) | yes, depends on margins only | yes; ties need an even electorate (Section 5) | **yes** |
| Maximal lotteries, ties broken by a random voter choosing any alternative | no (Proposition 5) | yes | yes | no |
| Ranked pairs with margins, tied pairs ordered by a random voter's ballot (Zavist and Tideman 1989) | yes (Zavist and Tideman 1989) | yes, depends on margins only | yes (Tideman 1987; computed) | **yes**, on the cited statements |
| Schulze with margins, ties broken by a random voter's favourite among the winners | yes: the set of winners is independent of clones also at ties (remark below; Schulze 2011; proof of Proposition 20) | yes, depends on margins only | yes (Schulze 2011; computed) | **yes** |
| Borda | no | yes | yes | no |
| Plurality | no | no | yes | no |
| Antiplurality | no | no | no: one ballot leaves at least two of three tied candidates tied | no |
| Random ballot | yes | no: every profile is a tie | | no |
| Uniform lottery over candidates | no | yes, and has no ties | | no |

Zavist and Tideman order tied pairs by the ballot of one voter; drawing that voter at random keeps the rule anonymous. The computed cases for ranked pairs and Schulze are random profiles of two to six voters on three and four candidates, with the set of possible winners (part 9). *(Cited and computed as marked.)*

*Remark (sets of winners).* Suppose a rule gives every profile a set of winners that is independent of clones as a set: when x is replaced by X, the winners outside X stay the same, and some clone is a winner exactly when x was one. Then breaking ties by a random voter's favourite among the winners gives a complete rule that is independent of clones, because a voter ranks a clone above every other winner exactly when the voter ranked x above them. For ranked pairs with tied pairs in every order the supposition fails at some ties (Zavist and Tideman 1989), which is why their rule orders the tied pairs instead. *(Proved.)*

**Further rules on strict rankings.** The same three questions for the common deterministic rules, on random profiles of three and four candidates with a candidate replaced by two or three clones (`scripts/symmetry/equality_rule_survey.py`). A rule that depends only on the margins cannot be changed by a ballot and its reverse.

| Rule | A ballot and its reverse cancel, away from the rule's own ties | Independent of clones | EC-VA |
|---|---|---|---|
| Ranked pairs, Schulze | yes, depend on margins only | yes, as in the table above | **yes**, as in the table above |
| Split Cycle | yes, depends on margins only | yes (Holliday and Pacuit 2023; no failure computed) | no: its ties are not within a fraction of a vote |
| Minimax, Copeland, Kemeny, Black, Baldwin, Nanson, Borda | yes, depend on margins only | no (computed) | no |
| Instant runoff | no (computed) | yes (Tideman 1987; no failure computed) | no |
| Plurality, antiplurality, Bucklin, Coombs | no (computed) | no (computed) | no |

Baldwin, Nanson and Black use Borda scores, which are sums of margins, among all or among the remaining candidates. In the computed cases minimax and Baldwin fail independence of clones only when a candidate is replaced by three clones that form a cycle among themselves; for minimax this is Tideman's observation (1987) that it is independent of clones in pairs but not in larger sets.

Split Cycle fails by its ties alone. Let a beat b by 10, b beat c by 10, c beat a by 6, d beat c by 6, a beat d by 2 and d beat b by 2. Both a and d are undefeated, and they remain so in every multiple of the profile with one ballot added: the tie fills a region of profiles, not a boundary. At this profile ranked pairs elects a and Schulze elects d, and in all computed profiles their winners are among the winners of Split Cycle. They decide what Split Cycle leaves open, in two different ways. *(Computed.)*

So of the rules examined, those that pass are the ones that depend on the margins only, are independent of clones and leave undecided only what a fraction of a vote decides: ranked pairs, Schulze and maximal lotteries. Instant runoff fails on the side of the voters, the other rules that depend on margins on the side of the alternatives. *(Computed and cited as marked.)*

## 5. Which profiles are ties

For maximal lotteries the ties, the profiles at which the maximal lottery is not unique, can be described exactly. Let G be the margin matrix, G_xy the number of voters who prefer x to y minus the number who prefer y to x. A lottery p is maximal when Σ_x p_x G_xy ≥ 0 for every y. Call a candidate *essential* if some maximal lottery gives it positive probability, and let E be the set of essential candidates and G_E their margin matrix.

**Proposition 7.**
(a) Every maximal lottery, restricted to E, lies in the kernel of G_E.
(b) If the maximal lottery is not unique, then G_E has nullity at least two, and some set S of essential candidates, of even size at least two, has a margin matrix with Pfaffian zero.
(c) If all margins are odd, in particular if the number of voters is odd, the maximal lottery is unique (Laffond, Laslier and Le Breton 1997).

*Proof.* (a) Let p and q be maximal. Then pᵀGq ≥ 0 and qᵀGp ≥ 0, and the two are negatives of each other, so both vanish. The terms (pᵀG)_y q_y of the first sum are non-negative, so each vanishes: (pᵀG)_y = 0 whenever q_y > 0. Hence pᵀG vanishes on E, and p is zero outside E. (b) Two different maximal lotteries are two independent vectors in the kernel of G_E. A skew-symmetric matrix has even rank. If |E| is even, G_E is singular and its Pfaffian, whose square is the determinant, is zero. If |E| is odd, the nullity is odd, so at least three, and removing any one candidate leaves a singular matrix of even size, at least two. (c) The Pfaffian of a skew-symmetric matrix of size 2k is a signed sum over the (2k − 1)!! ways of dividing the 2k candidates into pairs, each term the product of the margins of its pairs. With all margins odd it is a sum of an odd number of odd terms, so it is not zero, and (b) applies. ∎

In every computed case the set of maximal lotteries has dimension exactly the nullity of G_E minus one. A unique maximal lottery then has nullity one and, since the rank is even, is carried by an odd number of candidates. *(Proved as stated; the equality computed, part 5.)*

**Consequences for the criterion.**

- Ties occur only in electorates of even size, and any one added ballot removes them. This is condition 2 for maximal lotteries, in a strong form. *(Proved, from (c); computed, part 6.)*
- In vote shares the ties form a set of measure zero: for each even set S the Pfaffian of G_S is a polynomial in the shares that is not identically zero. This is the continuous counterpart of condition 2. *(Proved.)*

**Proposition 8 (maximal lotteries as Pfaffians).** Let E be an odd number of candidates in some order e_1, …, e_n, and let v_j = (−1)^(j−1) Pf(G_{E∖e_j}), with the Pfaffian of the margins among the other members of E.

(a) For every candidate y, the sum Σ_j v_j G_{e_j y} is the Pfaffian of the margins among e_1, …, e_n, y, in this order. It is zero when y belongs to E, so v lies in the kernel of G_E.
(b) If the v_j are all positive or all negative, and for every y outside E the Pfaffian of (a) has their sign, then the lottery with probabilities v_j / Σ v is the unique maximal lottery.
(c) If S is an even set of candidates with Pf(G_S) = 0, then for every z in S the vector v of S∖z, with zero for z, lies in the kernel of G_S.
(d) Let the Pfaffian of exactly one even set S vanish at a margin matrix, and let the maximal lottery there not be unique. Then the maximal lotteries form a segment. Its two endpoints are the lotteries of (b) for two odd sets, each of which is S without one candidate or S with one more. For margin matrices nearby, on either side of the surface Pf(G_S) = 0, the maximal lottery is unique, is carried by one of the two sets, a different one on each side, and tends to the corresponding endpoint.

*Proof.* (a) is the expansion of a Pfaffian along its last row. When y is one of the e_j, the matrix has two equal rows and columns, and its Pfaffian is zero. (b) Let p be the lottery. By (a), pᵀG is zero on E and positive outside, so p is maximal. For another maximal lottery q, the proof of Proposition 7 (a) gives (pᵀG)_y = 0 wherever q_y > 0, so q gives probability only to E, and by Proposition 7 (a) it lies in the kernel of G_E. Some v_j is not zero, so G_E has an invertible part of size n − 1, its kernel is the line through v, and q = p. (c) By (a) the vector lies in the kernel of the margins among S∖z, and its product with the column of z is, up to sign, Pf(G_S). (d) is proved in Appendix B. ∎

Parts (a) and (b) are the conditions of Kaplansky (1995) for a symmetric game in which every strategy is used, applied to the candidates that carry the lottery. On 1500 random margin matrices with three to seven candidates the unique maximal lottery always has this form. For three candidates in a cycle, v = (m_bc, −m_ac, m_ab), the lottery of Section 2. *(Proved; computed, `scripts/symmetry/maximal_lottery_pfaffians.py`, parts 1 and 2.)*

**Regions and walls.** Margin space is thus divided into regions, one for each odd set E that carries the lottery, and in each region the lottery is a ratio of Pfaffians of the margins. The walls are surfaces Pf(G_S) = 0 for even sets S: a member x of E reaches probability zero where Pf(G_{E∖x}) = 0, and a candidate y outside E stops losing to the lottery where Pf(G_{E∪y}) = 0. By (d), on a wall away from the other walls the maximal lotteries are the segment between the lotteries of the two sides, and the sets that carry the lottery on the two sides are S without one candidate or S with one more. *(Proved, Appendix B; computed on 180 crossings of walls with four, five and six candidates, part 3.)*

**Ties of higher order.** For a pair the Pfaffian is the margin itself, so the first case of (b) is the pairwise tie. For four candidates it is

Pf = m_ab m_cd − m_ac m_bd + m_ad m_bc,

one product for each way of splitting the four into two pairs. It can vanish with no margin zero. The script builds a profile of 20 voters: b beats a by 4, c beats a and b by 4, a beats d by 2, d beats b by 2 and c by 4. The maximal lotteries form a segment from (0.4, 0, 0.2, 0.4), carried by the cycle a, c, d, to (0.25, 0.25, 0, 0.5), carried by the cycle a, b, d. Raising the margin of a over d makes the Pfaffian negative and leaves the first lottery's cycle; lowering it leaves the second. *(Computed, part 5.)*

So a pairwise tie is a tie between two candidates inside a pair, and the tie of the next order is a tie between two cycles inside a group of four. These are the walls for S a pair and for S a group of four. Across the wall of a pair, the lottery is carried by one of its two candidates or by a cycle of three that contains the pair; across the wall of a group of four, by three of the four or by a group of five that contains them. *(Interpretation, from the computed cases.)*

**Margins as rotations.** A skew-symmetric matrix generates a rotation, and its kernel is the axis. By (a), every maximal lottery is an axis of the rotation among the essential candidates. For three candidates every rotation has an axis, (m_bc, m_ca, m_ab), which is the lottery of the cycle found in Section 2. For four candidates a rotation in general has no axis: it turns two planes at two rates. It has one exactly when the Pfaffian vanishes. In quaternions, G acts on the four coordinates as x ↦ px + xq with imaginary quaternions

p = −½ (m_ab + m_cd, m_ac − m_bd, m_ad + m_bc), q = −½ (m_ab − m_cd, m_ac + m_bd, m_ad − m_bc),

one coordinate for each way of splitting the four candidates into two pairs, and Pf = |p|² − |q|². The tie of second order is a balance between the left and the right part of the margins, as the pairwise tie is a balance between two candidates. An odd renaming exchanges the two lengths and so changes the sign of the Pfaffian. *(Computed, parts 4 and 5; the standard decomposition of rotations in four dimensions.)*

This is the step from the complex numbers to the quaternions of *A Ladder of Lost Properties*, here on the side of the alternatives: with three, the margins have one axis; with four, a left and a right part that do not commute into one. The count differs by one from the table there, which counts the dimension of the space of ballots. A balanced profile is also the fourth step of that note's table made exact: a non-trivial electorate whose parts cancel. With five candidates that all carry the lottery, Proposition 8 makes the probability of each proportional to the Pfaffian of the other four, that is, to the balance |p|² − |q|² of their margins. Whether ties of third order, among six candidates, have a similar reading is open. *(Interpretation.)*

## 6. Equal rankings

Sections 1 to 5 assume strict rankings. This section allows ballots that rank candidates equal. The reverse of a ballot reverses its order, so the ballot that ranks all candidates equal is its own reverse. Margins are defined as before, and a ballot and its reverse still add nothing to any margin.

Propositions 1 to 4 hold unchanged: their proofs use only strict ballots, which are still available. Proposition 7 (a) and (b) hold for every margin matrix. Two things change, and each requires an exception to be stated more carefully.

**Ties are no longer within one vote.** A ballot that ranks x and y equal adds nothing to their margin, so the margins of a profile no longer share the parity of the electorate, and Proposition 7 (c) says nothing about electorates of odd size. Three voters:

a = c > b = d;  b > a > d > c;  d > c > b > a.

Here a beats d, d beats c, c beats b and b beats a, each by one vote, while a ties c and b ties d. The maximal lotteries form the segment from ½a + ½c to ½b + ½d. None of the 75 possible fourth ballots makes the maximal lottery unique. For four candidates with margins between −1 and 1 this is, up to renaming, the only tie that one ballot does not settle. *(Computed, parts 1 and 2 of `scripts/symmetry/equality_equal_rankings.py`.)*

A fraction of a vote always settles a tie:

**Proposition 9.** For every profile p, every k ≥ 2 and every strict ballot r, the profile made of k copies of p and the ballot r has a unique maximal lottery.

*Proof.* Its margin matrix is kG + R, with G the margin matrix of p and R that of r. A Pfaffian is a polynomial with integer coefficients in the entries, so for every even set S of candidates the Pfaffian of (kG + R)_S equals that of R_S modulo k. With the candidates of S listed in the order of r, R_S has +1 everywhere above the diagonal, and its Pfaffian is 1 (expanding along the first row gives an alternating sum of an odd number of ones); another listing changes at most the sign. So for k ≥ 2 no even Pfaffian vanishes, and Proposition 7 (b) applies. ∎

Proposition 7 (c) is the same argument modulo 2, applied to the margins themselves. In shares of the electorate, adding r to k copies of p is adding the fraction 1/k of a strict vote to p. Every tie of maximal lotteries is settled by half a strict vote, by a third, and so on; only the whole vote can fail. *(Proved; computed on random profiles, part 3.)*

**The exception for voters, restated.** Assume that L depends only on the shares of the ballots, so that a fraction of a vote has a meaning. Condition 2 becomes:

2′. **Equal voters, except at ties within a fraction of a vote.** For every tie p there are a number k ≥ 1 and a ballot r such that k copies of p together with r form a settled profile.

- Condition 2 is the case k = 1 and implies 2′. Sections 3 and 4 use that case.
- The fraction is not the resolution of the rule or of its ballots. A rule with coarse ballots, or one that uses little of what the ballots say, is measured in the same unit as every other rule and does not get a coarser one.
- Because L depends only on shares, a tie is a tie in every multiple of the electorate, and 2′ applies to each multiple. Settled profiles therefore lie arbitrarily close to every tie in vote shares. A rule that counts every cycle as a tie still fails, since a cycle in a large electorate remains one when a vote is added. So does antiplurality: of three tied candidates two remain tied. A rule that treats a lead of fewer than some fixed number of votes as a tie is excluded as well, because it does not depend on shares only.

**Clones with equal rankings.** Tideman's definition of a set of clones (1987) excludes ties with outsiders: no voter ranks a candidate outside the set equal to a member or between two members. Replacing x by clones is then defined only if no ballot ranks x equal to another candidate, and for ballots with few levels the criterion almost never applies. A wider definition applies more often: X is a set of clones if on every ballot every outsider is above all of X, below all of X or equal to all of X. Put differently, removing all members of X but one gives the same profile whichever member is kept, up to its name. The clones then have the margins of x against every outsider, and the Lemma of Section 4 holds with the same proof. But a second exception is forced.

**Proposition 10.** With clones in the wider sense, let L be neutral and independent of clones, and let p be a profile in which every ballot ranks a and x equal. Then L(p) gives a and x probability zero.

*Proof.* Exchanging a and x maps p to itself, so by neutrality they have the same probability q. Replace x by x and x′, ranked equal on every ballot. On every ballot each other candidate, a included, compares in the same way with both, so they are clones. In the new profile a, x and x′ can be exchanged, so each has the same probability q′. Independence of clones gives q′ = q for a and 2q′ = q for the clones. Hence q = 0. ∎

A rule that gives probability to two candidates that no ballot distinguishes can therefore not treat one of them as replaceable by clones. The condition with its exception:

1′. **Equal alternatives, except for candidates no ballot distinguishes.** L is independent of clones in the wider sense, for every set of clones X such that no outsider is ranked equal to X on every ballot.

On strict rankings 1′ is condition 1. *(Proposition 10 proved; computed example, part 4.)*

**The tie-breaker.** With equal ranks a ballot orders classes of candidates, and one voter's best maximal lottery need not be unique. Draw voters at random, one after another. Each narrows the current set of maximal lotteries to those that are best for the voter's ballot: the largest total probability for its first class, then the largest for its second, and so on. When every ballot of the profile has been drawn, a random strict order of the candidates decides what is still open, in the same way. The order in which new ballots come up depends only on their shares. On strict rankings the first voter decides everything, and this is the tie-breaker of Proposition 6.

**What the voters leave open.** In the random profiles computed, the voters leave open only the division of probability among candidates that no ballot distinguishes. This is not always so. Six candidates, eight voters:

g > c=d > e > a=b;  c=d > e > a=b > g;  e=g > a=b > c=d;  a=b > c=d > e=g;
e > b=d > g > a=c;  b=d > g > a=c > e;  e=g > a=c > b=d;  a=c > b=d > e=g.

The candidates a, b, c, d tie pairwise; e beats a and b and loses to c and d; g beats a and c and loses to b and d. Every ballot ranks a, b, c, d as two pairs, a=b against c=d or a=c against b=d. When voters who rank a=b first and a=c first come up early, what remains is the segment of lotteries (t, ½ − t, ½ − t, t) on a, b, c, d, from ½b + ½c to ½a + ½d. Along it every class of every ballot keeps its total, so no further voter narrows it. The ballots distinguish the four candidates from each other, but not these lotteries. *(Computed, part 6.)*

How the last order is drawn then matters. With a uniformly random order of the candidates the rule gives a the probability 1/16, and when a is replaced by two clones, the clones together receive 3/40. The order has to respect the clones.

**The tree of clone sets.** If two clone sets overlap, their union, their intersection and their differences are clone sets (Appendix A, Step 3). Families of sets closed in this way have a decomposition tree, as the modules of a graph do (Chein, Habib and Maurer 1981; Habib and Paul 2010): the clone sets that overlap no other clone set form a tree under inclusion, with the single candidates as leaves, and the children of a node are of one of three kinds. Either no union of several, but not all, of them is a clone set; or they form a line in which exactly the unions of neighbours are clone sets; or every union of them is a clone set. For strict rankings this is the tree of Elkind, Faliszewski and Slinko (2012). The third kind, with three or more children, occurs exactly for candidates that no ballot distinguishes: on a ballot that ranks a member of one child above a member of another, a member of a third child is above both or below both, and is then not placed alike against one of the two other unions.

Draw the order along the tree: at every node the children are put in a uniformly random order, except in a line, where one of its two directions is drawn; then the same inside each child. A set of clones is then consecutive in the order unless it consists of some, but not all, of a group of candidates that no ballot distinguishes, which is the exception of 1′. Berker et al. (2025) use the same tree to make deterministic rules consistent under cloning. With this order the rule is independent of clones in the example: a has 1/16, and its clones together have 1/16.

**Proposition 11.** Maximal lotteries on rankings with equal ranks, with ties broken by random voters in turn and then by an order of the candidates drawn along the tree of clone sets, satisfy EC-VA.

*Proof.* The rule is anonymous and neutral and depends only on the shares of the ballots. Where the maximal lottery is unique the rule depends on margins only, so these profiles are settled, and 2′ follows from Proposition 9. Condition 1′ is proved in Appendix A: the set of maximal lotteries after cloning is a product of the set before and a set of divisions among the clones, every voter narrows the two factors separately, and an order in which the clones are consecutive does the same. ∎

*(Proved, with the decomposition tree taken from the cited theorem. Computed: 496 random profiles with three and four candidates outside the exception, where the voters leave only indistinguishable candidates open and both ways of drawing the order agree, and the example, parts 5 and 6.)*

*Reading.* The two exceptions are of one kind. Opposite voters cancel each other, and candidates that no ballot distinguishes cannot be told apart: in both cases the ballots say nothing about the choice that remains, and what is left to count is the candidates. With strict rankings only the first occurs. The example above is a third case of the same kind, lotteries that no ballot distinguishes; it needs no exception, only a tie-breaker that knows the clones. *(Interpretation.)*

**The definition.** The two restated conditions are the criterion. They can be stated for ballots of any kind for which three operations are defined: renaming the candidates, reversing a ballot, and removing a candidate from a ballot. Strict rankings, rankings with equal ranks, approval ballots and score ballots are of this kind.

- A profile is *balanced* if every ballot occurs as often as its reverse. A profile p is *settled* for a rule L if L(p + Q) = L(p) for every balanced profile Q, and a *tie* otherwise.
- A set X of candidates is a *set of clones* in a profile if removing all members of X but one gives the same profile whichever member is kept, up to its name. For strict rankings these are candidates adjacent on every ballot; for rankings with equal ranks it is the wider sense above. L is *independent of clones* for X if X receives in total the probability its remaining member has in the smaller profile, and every other candidate keeps its probability.
- Two candidates are *indistinguishable* in a profile if exchanging them leaves every ballot unchanged.

**Definition (EC-VA).** An anonymous and neutral rule L that depends only on the shares of the ballots satisfies **equality of voters and alternatives** if:

1′. **Equal alternatives, except for candidates no ballot distinguishes.** L is independent of clones for every set of clones none of whose members is indistinguishable from a candidate outside the set.

2′. **Equal voters, except at ties within a fraction of a vote.** For every tie p there are a number k ≥ 1 and a ballot r such that k copies of p together with r form a settled profile.

For rankings with equal ranks, a candidate outside a set of clones is indistinguishable from a member exactly when it is ranked equal to the set on every ballot, so 1′ is the condition stated above. For strict rankings no two candidates are indistinguishable and 1′ is condition 1, so a rule on strict rankings that depends only on shares and satisfies the first form of Section 3 satisfies the definition. Proposition 10 holds for ballots of any kind, with "indistinguishable" in place of "ranked equal on every ballot" and the same proof.

The kind of ballot is part of what is judged. Ballots that name a single candidate have no reverses among them, and a ballot naming a candidate has no counterpart naming two clones, so neither condition can be stated for a rule on such ballots. As a rule on rankings, plurality fails both (Section 4).

## 7. Approval and scores

A score ballot gives every candidate a score from 0 to K; an approval ballot is the case K = 1. The reverse of a ballot gives K minus the score, and removing a candidate leaves the other scores as they are. A set of clones is then a set of candidates with the same score on every ballot, and two candidates are indistinguishable when they have the same score on every ballot. Score voting elects the candidates with the largest total. Ties are broken as in Section 6: voters are drawn at random one after another, each narrows the tied candidates to those the voter scores highest among them, and when every ballot has been drawn the remaining candidates share the probability equally.

**Proposition 12.** Score voting with any range, approval voting included, with ties broken by random voters in turn, satisfies EC-VA.

*Proof.* The rule depends only on the shares of the ballots. *2′.* A ballot and its reverse add K to every total, so a profile with a single winner is settled. At a tie, one more ballot that gives K to one of the tied candidates and 0 to the others leaves a single winner; k = 1 suffices. *1′.* Clones have equal totals, so after x is replaced by X the winners are the same, with X in place of x. Every voter scores the members of X alike, so each step of the tie-breaker treats X as it treated x. When every ballot has been drawn, the remaining candidates have the same score on every ballot. If a member of X remains together with an outsider, the two are indistinguishable, which the exception excludes. Otherwise X receives in total what x received. ∎

*(Proved; computed for K = 1, 2, 5 on random profiles with three and four candidates: every profile with a single winner is settled, every tie is within one vote, and the rule is independent of clones in all cases outside the exception, `scripts/symmetry/equality_approval_score.py`, parts 1 to 3.)*

Three limits of this result:

- **The usual tie-breaker fails.** With the uniform lottery over the tied winners, two tied candidates that some ballot separates have one half each, and cloning one of them gives its clones two thirds. Approval and score voting pass with ties broken by the voters, not with ties broken by lot among the candidates. *(Computed, part 3.)*
- **Clones follow what the ballot records.** If candidates that are only adjacent in the order of every ballot counted as clones, as they do for rankings, score voting would not be independent of them. Three voters score a 5 and x 1, two score x 5 and a 0: a wins with 15 to 13. Add x′ next to x on every ballot, with 4 from the first three and 5 from the other two: x′ wins with 22. Under the definition x and x′ are not clones here, since removing one or the other leaves different profiles. A ranking cannot record how far apart adjacent candidates are; a score ballot does, and candidates it sets apart are not interchangeable. *(Computed, part 4; the last sentence interpretation.)*
- **STAR fails.** STAR voting takes the two candidates with the largest totals and elects the one preferred by more voters. Three voters score a 1 and x 0, two score x 5 and a 0, and a third candidate scores less than both. The runoff is between x and a, and a wins three to two. With x replaced by two clones, the runoff is between the clones. Away from its ties STAR satisfies EC-V, since a ballot and its reverse add K to every total and cancel in every runoff (Wolk, Quinn and Ogren 2023), and it fails 1′. *(Computed, part 5.)*

**BTR-score.** A score ballot can also be read for pairwise preferences: a voter prefers x to y when x has the higher score. BTR-score (Hiveism, *Four levels of voting methods*) puts the candidates in the order of their totals and compares the two lowest pairwise; the loser is eliminated and the winner meets the next candidate up, until one is left. A pairwise tie goes to the candidate higher in the order. Equal totals are ordered as ties are broken for score voting: random voters in turn put tied candidates in the order of their scores, and candidates with the same score on every ballot are ordered at random. A candidate who beats every other pairwise is elected whatever the totals.

**Proposition 13.** BTR-score satisfies EC-VA, for every range and any number of candidates. A profile whose outcome does not depend on how equal totals are ordered is settled, and K + 1 copies of any profile together with one suitable ballot form such a profile.

*Proof.* *1′.* Clones have the same score on every ballot, so they have the same total and the same margins against every other candidate, and they tie pairwise with each other. No voter separates them, and by the exception no outsider is still tied with them when every ballot has been drawn. So the clones are consecutive in the order, in the place of x. If the candidate coming from below beats x, it beats every clone in turn and passes them as it passed x. Otherwise the lowest clone takes over, each clone above takes over from the one below by the rule for pairwise ties, and the highest clone goes on as x did. A clone wins exactly when x won, and nothing else changes. *Settled.* A ballot and its reverse add K to every total and nothing to any margin, so the order of the totals, its ties and the possible outcomes stay the same. *2′.* For K = 1 the margin between two candidates is the difference of their totals, so the candidate highest in the order wins, and one more ballot for one of the candidates with the largest total decides. Let K ≥ 2, and consider a group of candidates with equal totals. Call a member w of the group a *king* if every member that beats w pairwise fails to beat some member, other than w, that does not beat w. Every group has a king: take a member w that as many members as possible do not beat, counting w itself. If u beat w and every other member that does not beat w, none of these would beat u, nor does u itself, and u would do better. Now let the ballot give, in every group, 2 to a king, 1 to the members that do not beat it, and 0 to the members that do, and add it to K + 1 copies of the profile. Groups with different totals stay in their order. Within a group the king is first, then the members that do not beat it, then the others, and a pairwise tie between candidates with different scores on the ballot now goes to the higher score, while the other comparisons are as before. Follow a group from below. A member that beats the king cannot pass the members that do not, since it fails to beat one of them; a member that does not beat the king loses to it or ties with it and has the lower score. So unless the candidate arriving from below beats every member of the group, the group passes on its king, and otherwise it passes on that candidate. Neither depends on the order of equal totals. Going up from the lowest group, the outcome does not depend on it either. ∎

The ballot of the proof uses three score levels, and with K ≥ 2 two are not always enough: with scores 0 to 2, seven candidates, all totals equal and the pairwise comparisons of the Paley tournament, no ballot with two levels settles the tie. *(Proposition proved; computed for K = 1, 2, 5, including the ballot of the proof on every tie found, part 6.)*

| Rule | Independent of clones, outside the exception | A ballot and its reverse cancel, away from the rule's own ties | Each of the rule's ties is within a fraction of a vote | EC-VA |
|---|---|---|---|---|
| Approval or score voting, ties broken by random voters in turn | yes (Proposition 12) | yes | yes, within one vote | **yes** |
| Approval or score voting, ties broken by the uniform lottery over the tied winners | no | yes | yes | no |
| BTR-score, equal totals ordered by random voters in turn | yes (Proposition 13) | yes | yes, within one vote added to K + 1 copies (Proposition 13) | **yes** |
| STAR | no | yes (Wolk, Quinn and Ogren 2023) | not checked | no |
| Maximal lotteries on rankings with equal ranks, ties broken by random voters in turn and an order drawn along the tree of clone sets (Section 6) | yes (Proposition 11) | yes, depends on margins only | yes (Proposition 9) | **yes** |
| Ranked pairs on rankings with equal ranks, the voters voting again (Section 8) | yes (Proposition 19) | yes, depends on margins only | yes, within one vote (Proposition 19) | **yes** |
| Schulze on rankings with equal ranks, the voters voting again (Section 8) | yes (Proposition 20) | yes, depends on margins only | yes, within one vote (Proposition 20, after Schulze 2011) | **yes** |

## 8. What determines the tie-breaker

The criterion restricts the tie-breaker only through independence of clones. This section asks what a further condition, proportionality to the voters, determines. Ballots are strict rankings.

Call a rule *proportional* on a set of profiles with the same margins if for two electorates in the set the lottery of their union is the average of their lotteries, weighted by their sizes. A tie-breaker in which a random voter chooses a maximal lottery, by a rule that depends on the voter's ballot and on the margins, is proportional on every such set. So is the uniform lottery over the candidates.

**Proposition 14 (full ties).** Let L be anonymous, neutral and independent of clones, and proportional on the profiles in which all margins are zero. For such a profile let T give each candidate the share of the voters who rank it first, and B the share who rank it last.

(a) With three candidates T = B, and L = T: the rule is random ballot.
(b) With four or more candidates L = αT + (1 − α)B, with one number α between 0 and 1 for all these profiles.
(c) If in addition L gives no probability to a candidate whom no voter ranks first, then α = 1 and L is random ballot.

The proof is in Appendix C. *(Proved; the equations of its second step solved numerically for clones from two, three and four candidates, `scripts/symmetry/equality_tie_breakers.py`, part 1.)*

*Reading.* This is the counterpart of Proposition 1. There, equality of voters and neutrality force the uniform lottery where everything is tied. Here, equality of alternatives, neutrality and proportionality force random ballot, up to the rule that draws a voter and takes the voter's last choice, which is independent of clones as well. The two tie values of Section 1 are each the only one of its kind. *(Interpretation.)*

**Away from full ties the tie-breaker is not determined.** Three rules by which the drawn voter decides, each proportional and each choosing a maximal lottery:

- *best first*, the rule of Proposition 6: the largest probability for the voter's first candidate, then for the second, and so on;
- *worst last*: the smallest probability for the voter's last candidate, then for the second last, and so on;
- *the voter votes again*: the limit, as k grows, of the maximal lottery of k copies of the profile together with one more copy of the voter's ballot.

**Proposition 15.** (a) Maximal lotteries with ties broken by worst last satisfy EC-VA. (b) For every profile p and strict ballot r the limit in the third rule exists and is a maximal lottery of p, and maximal lotteries with ties broken in this way satisfy EC-VA. (c) At a full tie all three rules are random ballot.

*Proof.* (a) As for Proposition 6, with one change at the clones. The candidates the voter ranks below X are treated as in p. If the smallest probability still available for x is zero, the clones can all have probability zero, and they do exactly where x has. Otherwise go up the clones: a clone whose smallest available share of the division is zero narrows only the division, and at the first clone whose smallest available share e is positive, the top clone at the latest, the smallest probability is reached exactly where the probability of x is smallest and the share is e. In both cases the merge is narrowed as by x in p. (b) The margins of k copies of p with r are k times G + R/k, with R the margins of r. The Pfaffians of G + εR are polynomials in ε, not identically zero by Proposition 9, so for small ε > 0 none of them vanishes and their signs do not change. By Step 1 of Appendix B the maximal lottery is then the lottery p^E of one odd set E, a quotient of polynomials in ε that stays between 0 and 1, so it has a limit. A limit of maximal lotteries of G + εR is maximal for G, and it is the maximal lottery of p where that is unique. By the Lemma the unique maximal lottery of k copies of a profile with clones, with a ballot, merges to that of the k copies without clones, and so do the limits and their averages over the voters. The rule depends on shares only, and ties are within a fraction of a vote by Section 5. (c) With all margins zero, best first gives the voter's first candidate everything, worst last gives every other candidate nothing, and the maximal lottery of the single ballot r is its first candidate. ∎

At a wall of Section 5 the third rule has a simple reading. By Proposition 8 (d) the limit is the end of the segment on the side to which the voter's ballot moves the Pfaffian of S: the voter tips the profile off the wall. It is the fraction of a vote of condition 2′, cast by a random voter.

The three rules differ at the tie between two cycles of Section 5. A voter with a > d > b > c takes the end of the segment with the most for a under best first, (0.4, 0, 0.2, 0.4), and the end with nothing for c under worst last, (0.25, 0.25, 0, 0.5). Over the 20 voters best first gives (0.3025, 0.1625, 0.07, 0.465), worst last (0.34, 0.1, 0.12, 0.44), and the voter voting again (0.3175, 0.1375, 0.09, 0.455). Of the 24 possible ballots, the third rule chooses the same end as both others for 16, as best first alone for 5 and as worst last alone for 3. *(Proposition proved; computed, `scripts/symmetry/equality_tie_breakers.py`, parts 2 and 3: all three independent of clones on 500 random profiles.)*

**With equal ranks: the voters vote again in turn.** A ballot with equal ranks need not settle a tie, so one voter is not enough. Draw voters independently until every ballot of the profile has come up. Add the first new ballot to the profile with a small weight, the second with a weight that is small against the first, and so on, and last a strict order of the candidates drawn along the tree of clone sets (Section 6), with the smallest weight. Take the maximal lottery of the profile so enlarged and let the weights go to zero, each infinitely faster than the one before.

**Proposition 16.** This limit exists and is a maximal lottery of the profile. On strict rankings the rule is the third rule of Proposition 15. Maximal lotteries with ties broken in this way satisfy EC-VA for rankings with equal ranks.

*Proof.* The Pfaffians of the enlarged margins are polynomials in the weights, and each weight occurs in them with a power of at most half the number of candidates. Read "infinitely faster" as: the i-th weight is ε to the power N^(i−1), for a fixed N larger than that. Then the term of a polynomial that decides its sign for small ε, the one with the least power of the last weight, among those the least power of the one before, and so on, is the same for every such N. No Pfaffian is identically zero, since with the strict order alone the Pfaffian of a set S is plus or minus the last weight to the power |S|/2. So for small ε the maximal lottery is unique and is the lottery p^E of one odd set (Appendix B, Step 1), a quotient of polynomials with values between 0 and 1; its limit exists, is a quotient of leading coefficients, and is maximal for the profile. On strict rankings the Pfaffians with the first ballot alone are not identically zero (Proposition 9), so their deciding terms contain no later weight, and the limit is that of Proposition 15 (b). For 1′, let X be a set of clones as in Appendix A. Every added ballot ranks the outsiders alike against X, and X is consecutive in the strict order (Appendix A, Step 3), so the enlarged margins have X as clones, and by the Lemma of Section 4 their unique maximal lottery merges to that of the enlarged margins without the clones. The order with x in place of X is distributed as the order drawn for the smaller profile (Appendix A, Step 3), and the voters are the same. Two ballots that differ only inside X are one ballot without the clones; it then enters twice, the second time with a weight that is small against the first, and this changes the first weight by a factor that tends to 1 and leaves the limit as it is. 2′ holds by Proposition 9. ∎

*(Proved. Computed exactly, with polynomials in the weights and the Pfaffians of Proposition 8: the rule gives a maximal lottery and is independent of clones on 846 random profiles with three to five candidates outside the exception, and agrees with Proposition 15 (b) on strict rankings, `scripts/symmetry/equality_votes_again.py`. The six-candidate profile of Section 6 is beyond that script.)*

**Proposition 17 (the average over the voters).** Let the ballots of a profile have any positive weights, and write s_r for the share of the ballot r.

(a) The rule of Proposition 16 satisfies, at every profile p,

    L(p) = Σ_r s_r · lim L(p + εr)   (ε → 0, ε > 0).

The lottery at a profile is the average, over the voters, of what the rule gives when that voter's weight is raised a little and brought back.

(b) A rule that gives the maximal lottery wherever it is unique and satisfies this equation agrees with the rule of Proposition 16 at every profile at which each ballot of the profile, added with a small weight, leaves a unique maximal lottery. All profiles of strict rankings are of this kind. Best first and worst last do not satisfy the equation at the tie above.

*Proof.* (b) The right side contains only unique maximal lotteries, so the equation gives L(p), and Proposition 16 gives the same. (a) Where the maximal lottery is unique it is continuous, and the equation holds. Let p be a tie. For a list A of different ballots of p write G(A) for what Proposition 16 gives once the ballots of A have come up in this order: the limit lottery if p with A added is settled, the average over the tree orders if every ballot is in A, and otherwise the sum of G(A, u) s_u / (1 − s_A) over the ballots u not in A, with s_A the share of A. So L(p) = Σ_r s_r G(r). Fix r and write H(A) for the limit, as δ goes to zero, of the same quantity at the profile p + δr. We show H(A) = G(r, A without r) for every list A, by induction on the number of ballots not in A. The profile p + δr with A added has, for small δ, the margins of p with r and then A without r added, up to a factor at the weight of r that tends to 1; so it is settled in the one case exactly if it is in the other, with the same limit, and the tree of clone sets is the same, since it depends only on which ballots occur. If r is in A, the two sums run over the same ballots u with the same weights. If r is not in A, the sum for H(A) has the term of r, which is H(A, r) = G(r, A) by the case before, with weight s_r / (1 − s_A), and the terms of the other u, which sum to G(r, A) (1 − s_A − s_r) / (1 − s_A). Together H(A) = G(r, A). For the empty list this is lim L(p + δr) = G(r). ∎

*(Proved. Computed: at 210 random profiles with three and four candidates and equal ranks, 70 of them ties, the lottery differs from the average of the lotteries with one weight raised by 10⁻⁷ by less than 10⁻⁷, same script.)*

Proposition 3 says that a rule with EC-V that is continuous is constant, so every rule of interest jumps at the ties. The equation of Proposition 17 is what remains of continuity: at a jump the rule takes the mean of its values on the sides, and the sides are weighted by the voters who point to them. For rankings with equal ranks the equation does not determine the rule by the argument of (b), because a ballot may leave the tie in place; whether it determines the rule up to the choice at profiles that stay ties under every change of the weights is open (Section 9). *(This paragraph interpretation.)*

**The same tie-breaker for other rules.** Score voting, ranked pairs, the Schulze method and BTR-score only compare sums over the ballots: totals, margins, or the smallest margin along a path. Such a rule can be applied to a profile with ballots added at infinitely small weights without taking a limit. Every sum becomes a list, its value in the profile, then its value on the first added ballot, on the second, and so on, and lists are compared in lexicographic order. So "the voters vote again in turn" is defined for each of these rules as in Proposition 16: voters are drawn until every ballot has come up or a single winner is left.

**Proposition 18.** (a) For score voting, this is the tie-breaker of Section 7. (b) For every rule that only compares sums, the rule completed in this way satisfies the equation of Proposition 17, whatever is done when every ballot has come up, provided it depends only on which ballots occur.

*Proof.* (a) The candidates with the largest list of totals are those with the largest total, among them those with the highest score on the first drawn ballot, and so on. (b) The proof of Proposition 17 (a) uses two facts about the rule. For a small weight δ the profile p + δr gives the comparisons of p with r added first, since the rule makes finitely many comparisons. And a ballot that occurs a second time further down a list changes no comparison of lists. Both hold here. ∎

For ranked pairs and the Schulze method on rankings with equal ranks, every ballot is drawn, and the last ballot is an order of the candidates drawn along the tree of clone sets. For ranked pairs, pairs whose lists are still equal are ordered by this last ballot in the way Zavist and Tideman (1989) order tied pairs by a voter's ballot: by the higher of the two candidates in the order, then by the lower. For Schulze, ballots are drawn until a single winner is left, and of several winners that remain at the end the one highest in the last ballot is elected.

**Proposition 19 (ranked pairs).** Ranked pairs with the voters voting again, and pairs with equal lists ordered by the last ballot, satisfies EC-VA for rankings with equal ranks.

*Proof.* The rule depends only on the shares of the ballots, and a profile at which every order of the pairs with equal margins gives the same winner is settled, since a ballot and its reverse change no margin. *1′.* Let p′ arise from p by replacing x with clones X, outside the exception, let the same voters be drawn for both, and let the last ballot of p be that of p′ with x in place of X; it is distributed as the order drawn for p (Appendix A, Step 3). For a pair that is not inside X, its image is the pair with x in place of a member of X. The pairs (a, y) with a in X and y outside have the list of (x, y), up to entries of a ballot that occurs twice, which change no comparison, and X is consecutive in the last ballot. So of two pairs that are not inside X and have different images, the one that is locked first in p′ has the image that is locked first in p. We show, along the order of p′, that a pair not inside X is locked in p′ exactly if its image is locked in p. Let this hold for the pairs before the pair e′ with image e. If e is locked in p and e′ were left out, there would be a path of locked pairs of p′ against e′; its image, without the pairs inside X, would be a path of locked pairs of p against e, and the locked pairs of p contain no cycle. If e is left out in p, there is a path against it of pairs locked before e. Put the same member of X in place of x on this path, the member in e′ if there is one. The pairs of this path come before e′ and are locked, so e′ is left out. Hence a candidate outside X has a locked pair against it in p′ exactly if it has one in p, and the members of X all have one from outside exactly if x has. The winner is the same outsider in both, or x in p and a member of X in p′.

*2′.* Let p be a tie. Lock its pairs in some order, and let r be a strict ranking that contains the locked pairs. Every pair with a positive margin against r was left out, so against it there is a path of locked pairs with margins at least as large. Add r as one more ballot. A pair ranked as in r, with margin g ≥ 0 before, now has g + 1, and a pair against r with margin g > 0 before now has g − 1. Lock the pairs in any order the new margins allow. The pairs ranked as in r close no cycle among themselves, so each is locked as long as no pair against r is. A pair against r with margin g before comes after the pairs of its path, which now have at least g + 1, so it is left out. Hence in every order the locked pairs are those ranked as in r, and its first candidate wins. One ballot suffices, k = 1. ∎

Locking pairs with equal lists in every order, as is usual for ties between pairs, does not do here. Let two voters rank a > b > c > d, two c > d > a > b, and one each d > b > c > a, d > b > a > c and b > d > c > a. The margins of b over c and of d over a are 3, and those of a over b and c over d are 1. If a voter a > b > c > d is drawn first and the last ballot is a > b > c > d, the pairs (a, b) and (c, d) have the same list at the end: every ballot that ranks a above b ranks c above d. Locking (a, b) first leaves out (c, d) and elects d; locking (c, d) first elects b. Two pairs on which every voter agrees are separated by no vote, so here the rule needs the order of the last ballot and not only its comparisons. *(Computed.)*

**Proposition 20 (Schulze).** The Schulze method with the voters voting again, and the winner highest in the last ballot elected when several remain, satisfies EC-VA for rankings with equal ranks.

*Proof.* The rule depends only on the shares, and a profile with a single winner is settled, since a ballot and its reverse change no margin. *1′.* Let p′, p, X and x be as before, at any stage, with the strengths of the pairs as lists. A path of p′ from one outsider to another that passes through X can be shortened: go from the first member of X on the path directly to where the path leaves X, which is a pair with the same list from every member. The shortened path is no weaker and is a path of p with x for that member. Likewise a path from an outsider to a member a can be cut at the first member it reaches, and a path from a to an outsider can start at the last member it leaves, each with a in the place of that member. So the strongest paths between outsiders have the same strength in p′ and p, and those between a member and an outsider have the strength of those between x and the outsider. An outsider is therefore a winner of p′ exactly if it is a winner of p, and a member is a winner exactly if x is one and no member has a stronger path to it than it has back. The relation "has a stronger path to it than back" is transitive for strengths in any order (Schulze 2011), so some member has no member above it: some member wins exactly if x does. This holds at every stage, and a single winner remains the single winner at later stages, since the lists are only extended. So the two profiles end with corresponding winners or with corresponding sets, and X is consecutive in the last ballot, so the highest winner of p′ is a member of X exactly if the highest winner of p is x.

*2′*, after Schulze (2011), who shows that one ballot makes any of several winners the single winner. Let p be a tie and a one of its winners. Write P[u, v] for the strength of the strongest path from u to v, the smallest margin on it, and 0 if there is no path of positive margins. Let r rank a first and the others by P[·, a], largest first, and among equals so that every candidate is below the one before it on a strongest path from a; the strongest paths from a can be chosen as a tree. The two demands agree: if e comes before f on the strongest path from a to f and P[f, a] > P[e, a], then the margin of e over f is at most P[e, a], so P[a, f] < P[f, a], and a is not a winner. Add r as one more ballot. The pairs on the strongest paths from a gain 1, and a candidate with no path from a now has the margin 1 from a; so the strongest path from a to any g has at least P[a, g] + 1. Let T be a together with the candidates h with P[h, a] > P[a, g]. Then g is not in T, a pair from outside T into T has a margin of at most P[a, g], or its first candidate would be in T, and r ranks T above the rest, so the pair now has at most P[a, g] − 1. Every path from g to a contains such a pair. So a is the single winner, with k = 1. ∎

Sharing equally among several remaining winners does not do. Take a cycle of x, y and z, two voters each for x > y > z, y > z > x and z > x > y, and replace x by the clones a and a′, ordered each way by one voter of each kind. In the branches where the clones win, both remain at the end, since the path through y and z is as strong in one direction as in the other, and a′ has probability 1/6 in total. Replace a by two clones that half of the voters order each way: three winners remain, and a′ has 1/9. *(Computed.)*

On random profiles with one to five voters and three and four candidates, both rules are independent of clones in all cases outside the exception, 385 for ranked pairs and 233 for Schulze. All 142 ties of ranked pairs found are removed by the ballot of the proof. At 191 ties of Schulze with three to five candidates, the ballot of the proof makes each of the tied winners the single winner, 411 cases. *(Propositions 18 to 20 proved; this paragraph computed, `scripts/symmetry/equality_votes_again_rules.py`, which also checks Proposition 18 (a) for ranges 1, 2 and 5 and the two profiles above.)*

So the three rules that pass on strict rankings (Section 4) also pass on rankings with equal ranks, with one tie-breaker: maximal lotteries (Proposition 16), ranked pairs and Schulze. They differ in what they need of the last ballot. Maximal lotteries use only its comparisons, Schulze also its first candidate among the winners, ranked pairs its order of the pairs.

Seen this way the tie-breaker is not an addition to the rule. A tie is a comparison that comes out equal, and it comes out equal only because every voter is counted at full weight or not at all. Counting the voters once more at weights below any vote, the rule decides by its own comparisons. *(This paragraph interpretation.)*

So independence of clones and proportionality fix the tie value where everything is tied and leave a choice where the tie is partial. Best first and worst last read the ballot of the drawn voter from the top or from the bottom. The third rule needs no such choice. It uses only the operation that the exception of condition 2′ already names, a fraction of one more vote, and the vote is that of a random voter. *(The last two sentences interpretation.)*

## 9. Open questions

1. The tie-breaker at partial ties (Section 8): whether every proportional tie-breaker that is independent of clones and chooses among the maximal lotteries is a mixture of rules of the three kinds. And whether the equation of Proposition 17 determines the rule of Proposition 16 also for rankings with equal ranks, up to the choice at profiles that stay ties under every change of the weights.
2. The side of the alternatives in the Strategic Information thread. Its README, Section 6, gives the Equality Criterion a strategic form (opposite voters cast ballots that cancel in the count); what independence of clones becomes when all voters follow the common rationale is not worked out.

## Appendix A. Proof of condition 1′ in Proposition 11

Let p′ be a profile of rankings with equal ranks, X a set of clones in p′ none of whose members is indistinguishable from a candidate outside X, and p the profile in which X is replaced by x. For a lottery q on the candidates of p′, its *merge* μ(q) adds the probabilities of X up into x. For a set S of lotteries on the candidates of p and a set E of lotteries on X, write

S ⊗ E = { q : μ(q) lies in S, and q restricted to X is μ(q)_x times a member of E }.

By the Lemma of Section 4 the maximal lotteries of p′ are F ⊗ D, with F the maximal lotteries of p and D those of p′ restricted to X. *Narrowing* a set by a ballot keeps the lotteries with the largest total for the first class of the ballot, among them those with the largest total for the second class, and so on.

**Step 1: one voter.** Let r′ be a ballot of p′, r the same ballot with X replaced by x, and r′|X its restriction to X. Then narrowing S ⊗ E by r′ gives (S narrowed by r) ⊗ (E narrowed by r′|X).

Every outsider compares alike with all of X. So either r′ ranks all of X in one class, possibly with outsiders, or X fills several consecutive classes that contain no outsider. In the first case every class total of r′ is a class total of r at the merge, and r′|X ranks X equal, so only S is narrowed. In the second case the same holds for the classes above X. Let M be the largest probability of x that is left. If M = 0, the classes of X have total zero and narrow nothing, as the class of x in r narrows nothing; and S ⊗ E does not depend on E. If M > 0, the total of a class of X is the probability of x times the share of that class in the division. Going down the classes of X, a class whose largest available share is zero narrows nothing. At the first class whose largest available share e is positive, the largest total is M e, and it is reached exactly where the probability of x is M and the share is e. From there on the probability of x is M and the shares are narrowed class by class. So the merge has been narrowed by the class of x in r and the division by r′|X. The classes below X depend on the merge only.

After narrowing, every class total of the ballot is constant on the set, and it stays constant on subsets. So narrowing again by the same ballot, or by a ballot that narrowed nothing before, changes nothing.

**Step 2: all voters.** Draw voters independently, each ballot with its share. By Step 1, after any sequence of voters the set for p′ is S ⊗ E, where S is the set for p after the same voters. When every ballot of p′ has come up, every ballot of p has come up, and the further voters changed nothing for p. So when the voters are done, the set for p′ is S ⊗ E, with S distributed as the set that the voters leave open for p.

**Step 3: the tree.** Count the single candidates and the set of all candidates as clone sets.

*(a) Closure.* Let A and B be clone sets that overlap: they meet and neither contains the other. A candidate outside A ∪ B compares alike with all of A and with all of B, and the two share a member, so A ∪ B is a clone set. A candidate outside A ∩ B is outside A or outside B and compares alike with all of that set, so A ∩ B is one. For A∖B, let z lie in A ∩ B and w in B∖A. A member u of A∖B is outside B, so it compares with z as with w; and w is outside A, so it compares alike with every such u. Hence z compares alike with all of A∖B, and candidates outside A do so anyway. The cited theorem gives the tree, and it says in addition that every clone set that is not a node is a union of children of a node of the second kind (consecutive in the line) or of the third.

*(b) Replacing X by x.* Let Y′ be a set of candidates of p′ that contains X or is disjoint from it, and Y the same set with X replaced by x. Then Y′ is a clone set of p′ exactly when Y is one of p: a candidate outside X compares with all of X as with x, and a candidate in X compares with a candidate outside as x does. Every clone set of p arises in this way. If such a Y′ other than X is overlapped by a clone set Z′ of p′, it is overlapped by one that contains X or is disjoint from it. If Z′ is not of this form itself, it overlaps X (a clone set inside X cannot overlap Y′), and Z′ ∪ X and Z′∖X are clone sets by (a); when Y′ is disjoint from X, Z′ ∪ X overlaps it, and when Y′ contains X, either Z′ ∪ X overlaps it or Y′ lies inside Z′ ∪ X and Z′∖X overlaps it. Two sets that contain X or are disjoint from it overlap exactly when the sets with x in place of X do. So the nodes of the tree of p are x and the sets Y for nodes Y′ of the tree of p′ that contain X or are disjoint from it. The kind of a node is read off from which unions of its children are clone sets, so by the first sentence of (b) Y is of the same kind as Y′ whenever the children of Y′ contain X or are disjoint from it.

*(c) X in the tree.* If X is a node of the tree of p′, its members are consecutive in every order drawn along that tree, and by (b) the tree of p is the tree of p′ with everything below X replaced by the leaf x. If X is not a node, it is a union of several, but not all, children of a node of the second or third kind, which then has at least three children. With three or more children the third kind consists of candidates that no ballot distinguishes, which the assumption on X excludes. So X is a run of neighbours in a line. Both directions of the line keep X consecutive, and by (b) the tree of p has the same line with the run replaced by x, or two children if only one other child is left. In both cases the order drawn for p′, with X replaced by x, is distributed as the order drawn for p.

**Step 4: the order.** A strict order in which X is consecutive is a ballot of the second kind in Step 1. So narrowing S ⊗ E by the order drawn for p′ gives (S narrowed by the order with x in place of X) ⊗ (E narrowed by the order on X). A strict order leaves a single lottery. So the merge of the lottery chosen for p′ is the lottery that the order with x in place of X chooses from S. By Steps 2 and 3 its distribution is that of the lottery chosen for p. ∎

## Appendix B. Proof of Proposition 8 (d)

For an odd set E write v^E for the vector of Proposition 8 and p^E for v^E divided by the sum of its coordinates, where that sum is not zero. The coordinates of v^E, and the sums Σ_j v_j G_{e_j y} for candidates y outside E, are Pfaffians of even sets, up to sign. Let G* be the margin matrix of the statement: the Pfaffian of S vanishes there and that of no other even set does.

**Step 1: away from the walls.** If no even Pfaffian vanishes at G, the maximal lottery is unique by Proposition 7 (b), and it is p^E for the set E that carries it: it lies in the kernel of G_E by Proposition 7 (a), so G_E is singular and E is odd; and a part of G_E of size |E| − 1 is invertible, so the kernel is the line through v^E.

**Step 2: the maximal lotteries at G\*.** Let E* be the essential candidates at G*. By Proposition 7 (b) and its proof, the margins among E* have a kernel of dimension at least two, and E* contains an even set with Pfaffian zero, which is S. If |E*| were odd, the kernel would have dimension at least three and every part of size |E*| − 1 would be singular, which gives at least three even sets with Pfaffian zero. So |E*| is even, its Pfaffian vanishes, and E* = S. If the kernel K of the margins among S had dimension four or more, the parts of size |S| − 2 would be singular. So K is a plane, and the maximal lotteries at G* are the lotteries q on S that lie in K and have (qᵀG*)_y ≥ 0 for every y outside S: a segment P. By Proposition 8 (c), K contains the vector of S∖z for every z in S, whose coordinate at z is zero and whose other coordinates are not.

**Step 3: the endpoints.** At an endpoint q of P, either a coordinate of q at some z in S is zero, or (qᵀG*)_y = 0 for some y outside S; otherwise q could be moved along the segment both ways. In the first case q is p^{S∖z}, since the members of K with coordinate zero at z form the line through the vector of S∖z. In the second case q, with zero for y, lies in the kernel of the margins among S ∪ y. A part of size |S| of these is invertible, so the kernel is the line through the vector of S ∪ y, whose coordinate at y is ± Pf(G*_S) = 0, and q is p^{S∪y}. Only one of these conditions holds at q. A second zero coordinate, at z′, would be the Pfaffian of S without z and z′; a zero coordinate at z together with (qᵀG*)_y = 0 would be the Pfaffian of S with y in place of z; and (qᵀG*)_y = 0 for two candidates y and y′ would put q in the kernel of the margins among S, y and y′, whose Pfaffian would vanish. An inner point of P satisfies none of them: a zero coordinate would make it an endpoint, and if (qᵀG*)_y vanished at an inner point it would vanish on all of P, and an endpoint would satisfy it together with the condition that ends the segment there.

**Step 4: each endpoint belongs to one side.** Let q = p^E be an endpoint, with E equal to S∖z or S ∪ y, and consider the conditions of Proposition 8 (b) for E at margin matrices near G*. Each is the sign of the Pfaffian of an even set. Those of sets other than S are not zero at G*, and they have the required signs there because q is a maximal lottery that is positive on E, or on S when E = S ∪ y; so they have them nearby. The one remaining condition is the sign of Pf(G_S): for E = S∖z it says that z loses to the lottery, for E = S ∪ y that the coordinate of y has the sign of the others. So on one side of the surface Pf(G_S) = 0 the lottery p^E is the unique maximal lottery, and on the other side it is not a maximal lottery.

**Step 5: the two sides.** Let G_n tend to G* on one side of the surface. By Step 1 the maximal lottery at G_n is p^E for some odd set E, the same one along a subsequence. The vector v^E is not zero at G*, so these lotteries tend to p^E at G*, which is maximal there, lies in P and so gives probability only to S. Hence E is S with one more candidate, or E lies inside S, the lottery has a zero coordinate in S, and by Step 3 E is S without one candidate. In both cases the limit satisfies one of the conditions of Step 3 and is an endpoint of P. So each side has an endpoint whose set carries the maximal lottery at points of that side arbitrarily near G*. By Step 4 an endpoint belongs to one side only, and two endpoints cannot belong to the same side, since near G* on that side each would be the unique maximal lottery. So the two endpoints belong to the two sides, and by Step 4 the maximal lottery near G* on either side is p^E for the set of its endpoint, which tends to that endpoint. ∎

## Appendix C. Proof of Proposition 14

Let Z_m be the fully tied profiles with m candidates, as vectors of the shares of the rankings.

**Step 1: weights.** By proportionality L is an affine function on Z_m. The profile in which all rankings have the same share lies in Z_m and has only positive shares, so L is the restriction to Z_m of a function p ↦ Σ_r s_r ψ(r), where s_r is the share of the ranking r. Averaging ψ over the renamings does not change it on Z_m, so ψ can be taken neutral, and then it gives the candidate in position k of r a weight w_k that depends on k only. So L gives y the sum of w_k times the share of the voters who rank y in position k, and the weights add up to one. They may depend on m; write w′ for the weights with m + 1 candidates.

**Step 2: clones.** Let C be the profiles in Z_{m+1} in which two candidates x and x′ are adjacent on every ballot. For a ranking r′ of this kind and a candidate y other than x′, let Δ_y(r′) be the weight that y receives from r′, or x and x′ together if y = x, minus the weight that y receives from r′ with x′ removed. Independence of clones says that Σ s_{r′} Δ_y(r′) = 0 on C. The profile in which all these rankings have the same share lies in C, so this sum vanishes whenever all margins are zero, and Δ_y is a combination of the functions of r′ that are +1 if u is above v and −1 if not, one for each pair u, v. For y other than x, Δ_y depends only on the position of y and on whether y is above or below the clones. Averaging the combination over the renamings that fix y and the pair of clones leaves three terms: λ times the number of other candidates, not clones, below y minus the number above; μ times +1 or −1 as y is above or below the clones; and a multiple of the number of other candidates above the clones minus the number below, which varies while the position of y stays the same and therefore has coefficient zero. For y in position k above the clones this gives w′_k − w_k = λ(m − 2k) + μ, and for y in position k + 1 below the clones, position k without x′, it gives w′_{k+1} − w_k = λ(m − 2k + 2) − μ. Comparing the first for k + 1 with the second for k, w_{k+1} − w_k = 4λ − 2μ for 2 ≤ k ≤ m − 2. So the weights of the positions 2 to m − 1 form an arithmetic progression.

**Step 3: three parts.** Hence w is a combination of the weight on the first position, the weight on the last position, equal weights, and weights that fall in equal steps from m − 1 to 1 − m. The last give y the sum of its margins against the other candidates, which is zero on Z_m. So L = aT + bB + c on Z_m, with a + b + mc = 1.

**Step 4: no uniform part.** Take the profile of m candidates with all rankings equally often, where every candidate has 1/m by neutrality, and replace x by x and x′ so that all rankings with the two adjacent are equally often. This profile lies in C, and T and B give each other candidate 1/m in it. So (a′ + b′)/m + c′ = 1/m, and with a′ + b′ + (m + 1)c′ = 1 this gives c′ = 0. For three or more candidates, therefore, L = αT + (1 − α)B.

**Step 5: the three statements.** (a) With three candidates, the profiles in which every ranking has the share of its reverse are fully tied, and both conditions leave two shares free, so they are the same profiles; there T = B. (b) The profile with one quarter each of bacd, cabd, dacb and dbca is fully tied, and a is never first and is last on one quarter of the ballots; more candidates are added to it by replacing a candidate with two clones, each ballot once in either order. For a profile p of this kind and the profile p′ obtained from it by one more such step, independence of clones gives α′T + (1 − α′)B = αT + (1 − α)B at p, with T ≠ B, so α′ = α: the number is the same for four or more candidates. In the profile above L gives a the probability (1 − α)/4, so α ≤ 1, and in the profile with all ballots reversed it gives a the probability α/4, so α ≥ 0. (c) In the first of these profiles no voter ranks a first, so (1 − α)/4 = 0. ∎

## References

- Berker et al. (2025). From independence of clones to composition consistency: a hierarchy of barriers to strategic nomination. arXiv:2502.16973.
- Brandl, F., Brandt, F. and Seedig, H. G. (2016). Consistent probabilistic social choice. *Econometrica* 84, 1839–1880.
- Chein, M., Habib, M. and Maurer, M. C. (1981). Partitive hypergraphs. *Discrete Mathematics* 37, 35–50.
- Elkind, E., Faliszewski, P. and Slinko, A. (2012). Clone structures in voters' preferences. *Proceedings of the 13th ACM Conference on Electronic Commerce*, 496–513.
- Fishburn, P. C. (1984). Probabilistic social choice based on simple voting comparisons. *Review of Economic Studies* 51, 683–692.
- Habib, M. and Paul, C. (2010). A survey of the algorithmic aspects of modular decomposition. *Computer Science Review* 4, 41–59.
- Hiveism. Four levels of voting methods. https://hiveism.substack.com/p/four-levels-of-voting-methods
- Holliday, W. H. and Pacuit, E. (2023). Split Cycle: a new Condorcet-consistent voting method independent of clones and immune to spoilers. *Public Choice* 197, 1–62. arXiv:2004.02350.
- Kaplansky, I. (1945). A contribution to von Neumann's theory of games. *Annals of Mathematics* 46, 474–479.
- Kaplansky, I. (1995). A contribution to von Neumann's theory of games II. *Linear Algebra and its Applications* 226–228. doi:10.1016/0024-3795(95)00167-P.
- Laffond, G., Laslier, J.-F. and Le Breton, M. (1997). A theorem on symmetric two-player zero-sum games. *Journal of Economic Theory* 72, 426–431.
- McGarvey, D. C. (1953). A theorem on the construction of voting paradoxes. *Econometrica* 21, 608–610.
- Schulze, M. (2011). A new monotonic, clone-independent, reversal symmetric, and Condorcet-consistent single-winner election method. *Social Choice and Welfare* 36, 267–303.
- Tideman, T. N. (1987). Independence of clones as a criterion for voting rules. *Social Choice and Welfare* 4, 185–206.
- Wolk, S., Quinn, J. and Ogren, M. (2023). STAR Voting, equality of voice, and voter satisfaction: considerations for voting method reform. *Constitutional Political Economy* 34, 310–334.
- Zavist, T. M. and Tideman, T. N. (1989). Complete independence of clones in the ranked pairs rule. *Social Choice and Welfare* 6, 167–173.
- *The Equality Criterion and Reversal*, *A Ladder of Lost Properties* (working notes), in this repository.
