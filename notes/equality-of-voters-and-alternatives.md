# Equality of Voters and Alternatives

*Working note. The Equality Criterion of Wolk, Quinn and Ogren (2023) asks that a ballot together with its reverse never changes the outcome: opposite voters weigh the same. It is called EC-V here, equality of voters (see* The Equality Criterion and Reversal*). Independence of clones asks the same of alternatives: none gains or loses by having similar alternatives beside it. This note shows that no rule has both and that two exceptions are forced. It proposes a criterion, equality of voters and alternatives (EC-VA), that states them: EC-V, except at ties that a fraction of a vote can break, and independence of clones, except for candidates that no ballot distinguishes. The definition is in Section 6. Sections 1 to 5 reach it in steps for strict rankings, where only the first exception occurs and a whole vote suffices: the conflict at ties, a first form of the criterion, a tie-breaker with which maximal lotteries pass, and a description of the ties. Section 6 allows equal rankings and gives the definition; Section 7 checks approval and score voting. Rules give lotteries over candidates and are defined for electorates of every size. Proved statements, computed checks (`scripts/symmetry/equality_voters_alternatives.py`, `equality_equal_rankings.py` for Section 6, `equality_approval_score.py` for Section 7) and interpretation are marked.*

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
| Schulze with margins | yes (Schulze 2011); not checked here at ties | yes, depends on margins only | yes (Schulze 2011; computed) | open at ties |
| Borda | no | yes | yes | no |
| Plurality | no | no | yes | no |
| Antiplurality | no | no | no: one ballot leaves at least two of three tied candidates tied | no |
| Random ballot | yes | no: every profile is a tie | | no |
| Uniform lottery over candidates | no | yes, and has no ties | | no |

Zavist and Tideman order tied pairs by the ballot of one voter; drawing that voter at random keeps the rule anonymous. The computed cases for ranked pairs and Schulze are random profiles of two to six voters on three and four candidates, with the set of possible winners (part 9). *(Cited and computed as marked.)*

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

**Ties of higher order.** For a pair the Pfaffian is the margin itself, so the first case of (b) is the pairwise tie. For four candidates it is

Pf = m_ab m_cd − m_ac m_bd + m_ad m_bc,

one product for each way of splitting the four into two pairs. It can vanish with no margin zero. The script builds a profile of 20 voters: b beats a by 4, c beats a and b by 4, a beats d by 2, d beats b by 2 and c by 4. The maximal lotteries form a segment from (0.4, 0, 0.2, 0.4), carried by the cycle a, c, d, to (0.25, 0.25, 0, 0.5), carried by the cycle a, b, d. Raising the margin of a over d makes the Pfaffian negative and leaves the first lottery's cycle; lowering it leaves the second. *(Computed, part 5.)*

So a pairwise tie is a tie between two candidates inside a pair, and the tie of the next order is a tie between two cycles inside a group of four. In both cases the undecided set joins the outcomes on the two sides. A unique maximal lottery is carried by an odd set of candidates, and the surfaces Pf(G_S) = 0 for even S are where the carrying set can change. That the undecided set always joins the neighbouring outcomes in this way is not proved. *(Interpretation, from the computed cases.)*

**Margins as rotations.** A skew-symmetric matrix generates a rotation, and its kernel is the axis. By (a), every maximal lottery is an axis of the rotation among the essential candidates. For three candidates every rotation has an axis, (m_bc, m_ca, m_ab), which is the lottery of the cycle found in Section 2. For four candidates a rotation in general has no axis: it turns two planes at two rates. It has one exactly when the Pfaffian vanishes. In quaternions, G acts on the four coordinates as x ↦ px + xq with imaginary quaternions

p = −½ (m_ab + m_cd, m_ac − m_bd, m_ad + m_bc), q = −½ (m_ab − m_cd, m_ac + m_bd, m_ad − m_bc),

one coordinate for each way of splitting the four candidates into two pairs, and Pf = |p|² − |q|². The tie of second order is a balance between the left and the right part of the margins, as the pairwise tie is a balance between two candidates. An odd renaming exchanges the two lengths and so changes the sign of the Pfaffian. *(Computed, parts 4 and 5; the standard decomposition of rotations in four dimensions.)*

This is the step from the complex numbers to the quaternions of *A Ladder of Lost Properties*, here on the side of the alternatives: with three, the margins have one axis; with four, a left and a right part that do not commute into one. The count differs by one from the table there, which counts the dimension of the space of ballots. A balanced profile is also the fourth step of that note's table made exact: a non-trivial electorate whose parts cancel. Whether ties of third order, among six candidates, have a similar reading is open. *(Interpretation.)*

## 6. Equal rankings

Sections 1 to 5 assume strict rankings. This section allows ballots that rank candidates equal. The reverse of a ballot reverses its order, so the ballot that ranks all candidates equal is its own reverse. Margins are defined as before, and a ballot and its reverse still add nothing to any margin.

Propositions 1 to 4 hold unchanged: their proofs use only strict ballots, which are still available. Proposition 7 (a) and (b) hold for every margin matrix. Two things change, and each requires an exception to be stated more carefully.

**Ties are no longer within one vote.** A ballot that ranks x and y equal adds nothing to their margin, so the margins of a profile no longer share the parity of the electorate, and Proposition 7 (c) says nothing about electorates of odd size. Three voters:

a = c > b = d;  b > a > d > c;  d > c > b > a.

Here a beats d, d beats c, c beats b and b beats a, each by one vote, while a ties c and b ties d. The maximal lotteries form the segment from ½a + ½c to ½b + ½d. None of the 75 possible fourth ballots makes the maximal lottery unique. For four candidates with margins between −1 and 1 this is, up to renaming, the only tie that one ballot does not settle. *(Computed, parts 1 and 2 of `scripts/symmetry/equality_equal_rankings.py`.)*

A fraction of a vote always settles a tie:

**Proposition 8.** For every profile p, every k ≥ 2 and every strict ballot r, the profile made of k copies of p and the ballot r has a unique maximal lottery.

*Proof.* Its margin matrix is kG + R, with G the margin matrix of p and R that of r. A Pfaffian is a polynomial with integer coefficients in the entries, so for every even set S of candidates the Pfaffian of (kG + R)_S equals that of R_S modulo k. With the candidates of S listed in the order of r, R_S has +1 everywhere above the diagonal, and its Pfaffian is 1 (expanding along the first row gives an alternating sum of an odd number of ones); another listing changes at most the sign. So for k ≥ 2 no even Pfaffian vanishes, and Proposition 7 (b) applies. ∎

Proposition 7 (c) is the same argument modulo 2, applied to the margins themselves. In shares of the electorate, adding r to k copies of p is adding the fraction 1/k of a strict vote to p. Every tie of maximal lotteries is settled by half a strict vote, by a third, and so on; only the whole vote can fail. *(Proved; computed on random profiles, part 3.)*

**The exception for voters, restated.** Assume that L depends only on the shares of the ballots, so that a fraction of a vote has a meaning. Condition 2 becomes:

2′. **Equal voters, except at ties within a fraction of a vote.** For every tie p there are a number k ≥ 1 and a ballot r such that k copies of p together with r form a settled profile.

- Condition 2 is the case k = 1 and implies 2′. Sections 3 and 4 use that case.
- The fraction is not the resolution of the rule or of its ballots. A rule with coarse ballots, or one that uses little of what the ballots say, is measured in the same unit as every other rule and does not get a coarser one.
- Because L depends only on shares, a tie is a tie in every multiple of the electorate, and 2′ applies to each multiple. Settled profiles therefore lie arbitrarily close to every tie in vote shares. A rule that counts every cycle as a tie still fails, since a cycle in a large electorate remains one when a vote is added. So does antiplurality: of three tied candidates two remain tied. A rule that treats a lead of fewer than some fixed number of votes as a tie is excluded as well, because it does not depend on shares only.

**Clones with equal rankings.** Tideman's definition of a set of clones (1987) excludes ties with outsiders: no voter ranks a candidate outside the set equal to a member or between two members. Replacing x by clones is then defined only if no ballot ranks x equal to another candidate, and for ballots with few levels the criterion almost never applies. A wider definition applies more often: X is a set of clones if on every ballot every outsider is above all of X, below all of X or equal to all of X. Put differently, removing all members of X but one gives the same profile whichever member is kept, up to its name. The clones then have the margins of x against every outsider, and the Lemma of Section 4 holds with the same proof. But a second exception is forced.

**Proposition 9.** With clones in the wider sense, let L be neutral and independent of clones, and let p be a profile in which every ballot ranks a and x equal. Then L(p) gives a and x probability zero.

*Proof.* Exchanging a and x maps p to itself, so by neutrality they have the same probability q. Replace x by x and x′, ranked equal on every ballot. On every ballot each other candidate, a included, compares in the same way with both, so they are clones. In the new profile a, x and x′ can be exchanged, so each has the same probability q′. Independence of clones gives q′ = q for a and 2q′ = q for the clones. Hence q = 0. ∎

A rule that gives probability to two candidates that no ballot distinguishes can therefore not treat one of them as replaceable by clones. The condition with its exception:

1′. **Equal alternatives, except for candidates no ballot distinguishes.** L is independent of clones in the wider sense, for every set of clones X such that no outsider is ranked equal to X on every ballot.

On strict rankings 1′ is condition 1. *(Proposition 9 proved; computed example, part 4.)*

**The tie-breaker.** With equal ranks a ballot orders classes of candidates, and one voter's best maximal lottery need not be unique. Draw voters at random, one after another. Each narrows the current set of maximal lotteries to those that are best for the voter's ballot: the largest total probability for its first class, then the largest for its second, and so on. When every ballot of the profile has been drawn, a uniformly random strict order of the candidates decides what is still open, in the same way. The order in which new ballots come up depends only on their shares. On strict rankings the first voter decides everything, and this is the tie-breaker of Proposition 6.

Maximal lotteries with this tie-breaker satisfy 2′, by Proposition 8. In the computed cases they satisfy 1′: on 502 random profiles with three and four candidates in which some ballot distinguishes every outsider from the cloned candidate, the rule is independent of clones; in the remaining 48 profiles cloning changes the shares in 21, as Proposition 9 requires when the candidates concerned receive probability. In all computed cases what the voters leave open is only the division of probability among candidates that no ballot distinguishes, which the last step divides equally. *(2′ proved; 1′ and the last statement computed, part 5, not proved.)*

*Reading.* The two exceptions are of one kind. Opposite voters cancel each other, and candidates that no ballot distinguishes cannot be told apart: in both cases the ballots say nothing about the choice that remains, and what is left to count is the candidates. With strict rankings only the first occurs. *(Interpretation.)*

**The definition.** The two restated conditions are the criterion. They can be stated for ballots of any kind for which three operations are defined: renaming the candidates, reversing a ballot, and removing a candidate from a ballot. Strict rankings, rankings with equal ranks, approval ballots and score ballots are of this kind.

- A profile is *balanced* if every ballot occurs as often as its reverse. A profile p is *settled* for a rule L if L(p + Q) = L(p) for every balanced profile Q, and a *tie* otherwise.
- A set X of candidates is a *set of clones* in a profile if removing all members of X but one gives the same profile whichever member is kept, up to its name. For strict rankings these are candidates adjacent on every ballot; for rankings with equal ranks it is the wider sense above. L is *independent of clones* for X if X receives in total the probability its remaining member has in the smaller profile, and every other candidate keeps its probability.
- Two candidates are *indistinguishable* in a profile if exchanging them leaves every ballot unchanged.

**Definition (EC-VA).** An anonymous and neutral rule L that depends only on the shares of the ballots satisfies **equality of voters and alternatives** if:

1′. **Equal alternatives, except for candidates no ballot distinguishes.** L is independent of clones for every set of clones none of whose members is indistinguishable from a candidate outside the set.

2′. **Equal voters, except at ties within a fraction of a vote.** For every tie p there are a number k ≥ 1 and a ballot r such that k copies of p together with r form a settled profile.

For rankings with equal ranks, a candidate outside a set of clones is indistinguishable from a member exactly when it is ranked equal to the set on every ballot, so 1′ is the condition stated above. For strict rankings no two candidates are indistinguishable and 1′ is condition 1, so a rule on strict rankings that depends only on shares and satisfies the first form of Section 3 satisfies the definition. Proposition 9 holds for ballots of any kind, with "indistinguishable" in place of "ranked equal on every ballot" and the same proof.

The kind of ballot is part of what is judged. Ballots that name a single candidate have no reverses among them, and a ballot naming a candidate has no counterpart naming two clones, so neither condition can be stated for a rule on such ballots. As a rule on rankings, plurality fails both (Section 4).

## 7. Approval and scores

A score ballot gives every candidate a score from 0 to K; an approval ballot is the case K = 1. The reverse of a ballot gives K minus the score, and removing a candidate leaves the other scores as they are. A set of clones is then a set of candidates with the same score on every ballot, and two candidates are indistinguishable when they have the same score on every ballot. Score voting elects the candidates with the largest total. Ties are broken as in Section 6: voters are drawn at random one after another, each narrows the tied candidates to those the voter scores highest among them, and when every ballot has been drawn the remaining candidates share the probability equally.

**Proposition 10.** Score voting with any range, approval voting included, with ties broken by random voters in turn, satisfies EC-VA.

*Proof.* The rule depends only on the shares of the ballots. *2′.* A ballot and its reverse add K to every total, so a profile with a single winner is settled. At a tie, one more ballot that gives K to one of the tied candidates and 0 to the others leaves a single winner; k = 1 suffices. *1′.* Clones have equal totals, so after x is replaced by X the winners are the same, with X in place of x. Every voter scores the members of X alike, so each step of the tie-breaker treats X as it treated x. When every ballot has been drawn, the remaining candidates have the same score on every ballot. If a member of X remains together with an outsider, the two are indistinguishable, which the exception excludes. Otherwise X receives in total what x received. ∎

*(Proved; computed for K = 1, 2, 5 on random profiles with three and four candidates: every profile with a single winner is settled, every tie is within one vote, and the rule is independent of clones in all cases outside the exception, `scripts/symmetry/equality_approval_score.py`, parts 1 to 3.)*

Three limits of this result:

- **The usual tie-breaker fails.** With the uniform lottery over the tied winners, two tied candidates that some ballot separates have one half each, and cloning one of them gives its clones two thirds. Approval and score voting pass with ties broken by the voters, not with ties broken by lot among the candidates. *(Computed, part 3.)*
- **Clones follow what the ballot records.** If candidates that are only adjacent in the order of every ballot counted as clones, as they do for rankings, score voting would not be independent of them. Three voters score a 5 and x 1, two score x 5 and a 0: a wins with 15 to 13. Add x′ next to x on every ballot, with 4 from the first three and 5 from the other two: x′ wins with 22. Under the definition x and x′ are not clones here, since removing one or the other leaves different profiles. A ranking cannot record how far apart adjacent candidates are; a score ballot does, and candidates it sets apart are not interchangeable. *(Computed, part 4; the last sentence interpretation.)*
- **STAR fails.** STAR voting takes the two candidates with the largest totals and elects the one preferred by more voters. Three voters score a 1 and x 0, two score x 5 and a 0, and a third candidate scores less than both. The runoff is between x and a, and a wins three to two. With x replaced by two clones, the runoff is between the clones. Away from its ties STAR satisfies EC-V, since a ballot and its reverse add K to every total and cancel in every runoff (Wolk, Quinn and Ogren 2023), and it fails 1′. *(Computed, part 5.)*

| Rule | Independent of clones, outside the exception | A ballot and its reverse cancel, away from the rule's own ties | Each of the rule's ties is within a fraction of a vote | EC-VA |
|---|---|---|---|---|
| Approval or score voting, ties broken by random voters in turn | yes (Proposition 10) | yes | yes, within one vote | **yes** |
| Approval or score voting, ties broken by the uniform lottery over the tied winners | no | yes | yes | no |
| STAR | no | yes (Wolk, Quinn and Ogren 2023) | not checked | no |
| Maximal lotteries on rankings with equal ranks, ties broken by random voters in turn and a random order of the candidates (Section 6) | yes in the computed cases; not proved | yes, depends on margins only | yes (Proposition 8) | **yes**, with 1′ computed |

## 8. Open questions

1. Which tie-breakers keep maximal lotteries independent of clones, beyond the one of Proposition 6, and whether one of them can be characterised by proportionality to the voters.
2. Whether the undecided set of maximal lotteries is always the join of the outcomes of the neighbouring decided regions, and which odd sets of candidates meet at a surface Pf(G_S) = 0.
3. The Schulze method with its tie-breaking against independence of clones at ties; further rules for the table.
4. With equal rankings: a proof that maximal lotteries with the tie-breaker of Section 6 satisfy 1′, and that what the voters leave open is always a division among candidates no ballot distinguishes.
5. Ranked pairs and the Schulze method with equal rankings; further rules on score ballots.
6. How EC-VA relates to the Strategic Information thread, where opposite voters cast complementary approval ballots.

## References

- Brandl, F., Brandt, F. and Seedig, H. G. (2016). Consistent probabilistic social choice. *Econometrica* 84, 1839–1880.
- Fishburn, P. C. (1984). Probabilistic social choice based on simple voting comparisons. *Review of Economic Studies* 51, 683–692.
- Laffond, G., Laslier, J.-F. and Le Breton, M. (1997). A theorem on symmetric two-player zero-sum games. *Journal of Economic Theory* 72, 426–431.
- McGarvey, D. C. (1953). A theorem on the construction of voting paradoxes. *Econometrica* 21, 608–610.
- Schulze, M. (2011). A new monotonic, clone-independent, reversal symmetric, and Condorcet-consistent single-winner election method. *Social Choice and Welfare* 36, 267–303.
- Tideman, T. N. (1987). Independence of clones as a criterion for voting rules. *Social Choice and Welfare* 4, 185–206.
- Wolk, S., Quinn, J. and Ogren, M. (2023). STAR Voting, equality of voice, and voter satisfaction: considerations for voting method reform. *Constitutional Political Economy* 34, 310–334.
- Zavist, T. M. and Tideman, T. N. (1989). Complete independence of clones in the ranked pairs rule. *Social Choice and Welfare* 6, 167–173.
- *The Equality Criterion and Reversal*, *A Ladder of Lost Properties* (working notes), in this repository.
