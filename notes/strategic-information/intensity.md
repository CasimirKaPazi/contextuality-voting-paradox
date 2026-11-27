# Intensities and the Utilitarian Target

*Working note, part of [Strategic Information](README.md), first draft. The ladder of [Bounds from Criteria](bounds.md) concerns the majority target. This note gives the counterpart for the utilitarian target, for methods that count totals. A ballot can reveal a voter's utilities only up to their scale, and what it reveals of the rest is fixed by the shape of the ballot polytope: each such method adds up the voters' utilities after a normalisation of its own. A ballot with corners reveals a finite choice, and a round one would reveal the intensities. The majority target and the utilitarian target ask for different shapes, so a count of totals cannot serve both. Everything is proved, for the linear regime where stated; nothing is computed. Conventions as in the README and in [The Ballot Polytope](ballot-polytope.md).*

## 1. Scale is never revealed

**Proposition 1.** Under every method and at every belief, a voter's best replies are the same for utilities u and for λu + c, with λ > 0 and c a number added to the utility of every candidate.

*Proof.* The value of a ballot is u · P(b) for a lottery P(b) (*What a Ballot Reveals*, Proposition 1), and the order of these values is unchanged by λ and c. ∎ *(Proved; exact.)*

So no method holds the sum of the voters' utilities, the utilitarian target as the README, Section 3, states it. A voter for whom much is at stake and one for whom little is cast the same ballot if their utilities differ by a scale. What a method can hold is a sum of utilities that have been brought to a common scale, voter by voter, and the question is which scale. *(Interpretation. Methods in which votes are paid for, such as quadratic voting, escape this by adding a cost to the value of a ballot; they are outside these notes.)*

## 2. Every count of totals is a normalisation

Let a method count totals, and let K be its ballot polytope, in the space of score vectors up to a number added to all scores. More generally K may be any bounded convex set of permitted score vectors. In the linear regime a voter with coefficients c(x) (*The Common Rationale*, Section 2) casts the ballot of K that is furthest in the direction of the vector c. Write N_K(c) for that ballot.

**Proposition 2.** In the linear regime the totals are the sum of the vectors N_K(c) over the voters. At the belief in which all pairwise ties are equally likely, c is the voter's utility vector with its mean subtracted, and the method elects the candidate with the largest sum of *normalised utilities* N_K(u):

- for approval and score, N_K(u) marks the candidates above the voter's mean utility;
- for Borda, N_K(u) is the voter's ranking, as points m − 1, …, 0;
- for plurality and cumulative voting, N_K(u) marks the voter's favourite;
- if K is a ball (score vectors with a fixed sum of squared deviations from their mean), N_K(u) is the utility vector with mean zero and variance one.

*Proof.* The value of a ballot s is Σ_x s(x) c(x), which is largest at the point of K furthest in the direction c. With all ties equally likely, c(x) is proportional to u_x minus the mean of u. The four cases are the furthest points of a cube, a permutohedron, a simplex and a ball. ∎ *(Proved, linear regime. For approval the first case is the known best ballot of a voter without information about the race.)*

So the methods that count totals are all sums of utilities, and differ in how each voter's utilities are reduced before they are added: to a set, to a ranking, to a single name, or, with a round set of ballots, only to a common mean and spread. Away from the symmetric belief the same holds with the coefficients c in place of the utilities: the voter reveals N_K of what the ballot is worth to them in each candidate's races.

## 3. Corners and roundness

What a voter reveals by casting N_K(c) is the set of all directions c for which that ballot is the furthest point of K.

**Proposition 3.** If K is a polytope with V vertices, the ballot reveals one of V sets of directions, at most log₂ V bits. A ballot reveals the direction of c itself, which at the symmetric belief is the whole utility vector up to Proposition 1, exactly when no two directions have the same furthest point: when the boundary of K has no corners. No method with finitely many ballots does this, and adding ballots between the vertices of K, such as intermediate scores, changes nothing (*The Ballot Polytope*, Proposition 3).

*Proof.* The directions with a given furthest point form its normal cone; at a vertex of a polytope the cone has an inside, and at a point where the boundary is smooth it is a single direction. ∎ *(Proved.)*

Two consequences.

- *Finer scores do not approach the utilitarian target.* Score voting is often described as utilitarian because a sincere score is an intensity. Under the common rationale in a large electorate its voters use the vertices of the cube, and the count is that of approval, whatever the number of score levels. What stands between a count of totals and the normalised utilitarian sum is the corners of the ballot polytope, not the fineness of the scale.
- *A round ballot would.* If the permitted score vectors are those with a fixed sum of squared deviations from their mean, the voter's best ballot is proportional to c, and at the symmetric belief the totals are the sum of the voters' utilities, each with mean zero and variance one. Call such a method one with *round ballots*. *(Term introduced here. Its kinship with quadratic voting is that a squared quantity limits the ballot; there it is a price, here a budget.)* Its ballot polytope is centrally symmetric, so it keeps opposite voters equal at every poll (*The Ballot Polytope*, Proposition 4).

## 4. The two targets ask for different shapes

**Proposition 4.** A method that counts totals and certifies its leader at a poll (*Bounds from Criteria*, Section 1) has voters whose ballots depend on their utilities only through the set of candidates they prefer to the leader. Such a method reveals no intensity at that poll. A method whose ballots reveal the direction of c at a poll does not certify its leader there, for three or more candidates.

*Proof.* By *Bounds from Criteria*, Proposition 3, the row space of the strategic count is spanned by the m − 1 margins μ_x, and it has no more than m − 1 dimensions. So the strategic count is an invertible linear function of the margins and the size of the electorate, and what one voter adds to it is determined by what that voter adds to the margins, which is the set of candidates the voter prefers to the leader. For the second statement, a ballot that varies with the direction of c inside the set of voters who prefer the same candidates to the leader is not of this kind. ∎ *(Proved.)*

Among counts of totals, then, the majority target and the utilitarian target pull the ballot polytope apart. The first wants the corners of the cube, on which a voter says of each candidate only on which side of the leader it stands; this is approval in its corner, the most such a count can hold of the majority relation. The second wants no corners at all. A count of m − 1 numbers has room for the leader's row or for the normalised sums, and not for both. This is a trade-off in the sense of the README, Section 1: neither end is below the other, and which is better depends on the target.

It matches what the smooth model shows for three candidates (*The Smooth Model across Methods*, Section 3): approval and Borda, which count totals, come to rest more often at the utilitarian winner than instant runoff and BTR-plurality do, and approval moves from the Condorcet winner towards the utilitarian winner as beliefs widen from the corner towards the symmetric belief of Proposition 2. *(Interpretation.)*

## 5. Open questions

1. Round ballots under the common rationale: self-confirming polls, and how close the outcome is to the normalised utilitarian winner away from the symmetric belief, where the voters reveal c and not u.
2. Which normalisation the utilitarian target should use. Proposition 1 leaves it open, and every shape of K is an answer to it; mean and variance (the ball) and range (the cube, if voters used its inside) are the usual candidates.
3. How well a polytope with V vertices approximates the ball, as a bound on what a method with finitely many ballots can hold of the normalised sum.
4. Methods that count more than totals: what a ranked ballot reveals of intensities at beliefs away from its corner. In the smooth model both the plurality ballot and the ranked ballots depend on intensities (*Instant Runoff and Plurality*, Section 7).
