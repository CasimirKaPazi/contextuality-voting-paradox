# The Global Form: Arrow's Theorem as a Degree

*Working note for thread B of the roadmap. It writes Arrow's theorem as an obstruction along loops: every voter gets a degree, the winding of the social ranking while that voter's ranking goes once around the circle of rankings. Unanimity makes the degrees sum to one. Independence of irrelevant alternatives makes them integers in {−1, 0, 1} and rigid. For lotteries the degree becomes a real number, and the uniform weights 1/n that anonymity demands exist only there. The integer part is in substance Baryshnikov's homological proof, written here with a hexagon instead of a nerve; the real degrees, their failure for rules with only pairwise independence, the place of reversal, and the same construction for strategy-proof rules, where negative real degrees detect contextuality, are added. Proved statements, computed checks and interpretation are marked. Checks:* `scripts/topology/voter_degrees.py`, `scripts/strategy/gs_degrees.py`.

## 1. Voter loops

Take three alternatives a, b, c. The six strict rankings form a hexagon, two rankings being adjacent when they differ in one comparison: abc, bac, bca, cba, cab, acb and back to abc. Going once around flips each of the three comparisons twice, once in each direction. This is the Condorcet loop of one ballot. Reversal of a ranking is the half rotation of the hexagon.

A rule F sends each profile of n rankings to a ranking. Fix all voters but one, voter i, at some context c, and let voter i walk once around the hexagon. Each step changes voter i's comparison on one pair and nothing else in the profile. If F satisfies independence of irrelevant alternatives (IIA), the social ranking can change only on that pair, and two rankings that differ on exactly one pair are adjacent. So the social ranking also walks on the hexagon, standing still or moving to a neighbour at each step, and its walk closes when voter i returns. Its winding number is the **degree** of voter i at context c, written deg_i(c).

Without IIA the walk can jump between rankings that are not adjacent, and then it has no winding number. *(Computed: for Borda, Copeland and plurality with a fixed tie-break, the social ranking jumps on a third or more of random voter loops, and where the winding is defined it is 0 at some contexts and 1 at others.)*

## 2. Three alternatives

**Lemma 1 (invariance).** Under IIA, deg_i(c) does not depend on the context c, nor on where voter i starts. *(Proved.)* Starting elsewhere on the same loop gives the same closed walk. Let another voter j take one step. The two loops of voter i, before and after, are joined by squares, each made of one step of i and one step of j. Around a square the social ranking takes at most four steps on a hexagon, which cannot go around it, so each square has winding 0 and the two loops have equal winding. Any context is reached from any other by such steps.

**Lemma 2 (sum).** Let all voters stand at the same ranking and move together once around (the diagonal loop). Under IIA its winding is the sum of the degrees. *(Proved.)* Replace each joint step by the voters' steps one after another. Each of these flips the same pair, so the social ranking stays on one edge meanwhile and ends where the joint step ends. The result is a staircase loop. Swapping two adjacent steps of different voters is a square, so the staircase deforms into the loops of voter 1, then voter 2, and so on, whose windings add. By Lemma 1 each is deg_i.

Under unanimity the social ranking on the diagonal loop is the common ranking itself, which winds once. So

  deg_1 + … + deg_n = 1.

**Lemma 3 (rigidity).** Under IIA every degree is −1, 0 or 1, and a voter with non-zero degree is pivotal on every pair at every context. *(Proved.)* A loop has six steps and the social ranking moves at most one position per step, so |deg_i| ≤ 1. Winding ±1 needs all six steps in the same direction, so the social comparison flips every time voter i flips one. By Lemma 1 this holds at every context. Hence on each pair e the social comparison is voter i's comparison, exclusive-or a function g_e of the other voters' comparisons on e.

**Lemma 4 (no mask).** If F_e = x_i ⊕ g_e on every pair and the output is always a ranking, then all g_e are equal and constant. *(Proved.)* For a fixed context, g = (g_ab, g_bc, g_ca) is a mask applied to voter i's ranking, and voter i can hold any of the six rankings. Flipping only the comparison between the top and the bottom of a ranking makes a cycle, and so does flipping only the other two. Every pair is the top–bottom pair of some ranking, so the only masks that keep all six rankings transitive are "flip nothing" and "flip everything". Hence g_ab(c_ab) = g_bc(c_bc) for all columns. Any two pairs' columns can be chosen independently (each combination of two comparisons occurs in some ranking), so both are constant.

**Proposition 1.** For three alternatives and any number of voters, an IIA rule into rankings either gives every voter degree 0, or gives exactly one voter degree 1 and is that voter's dictatorship or anti-dictatorship (the reverse of the voter's ranking). With unanimity it is a dictatorship. *(Proved, from Lemmas 1–4; the second part is Arrow's theorem.)* By Lemmas 3 and 4, a voter with non-zero degree is a dictator (g = 0) or an anti-dictator (g = 1), and then every other voter is irrelevant. Both have degree 1, because reversal is a rotation of the hexagon and keeps its orientation. Under unanimity the degrees sum to 1, so some degree is non-zero, and the anti-dictatorship is excluded.

*(Computed: all IIA rules into rankings for two voters, 94 rules, and three voters, 1536 rules. In every one the degree is the same at all contexts, the diagonal winding is the sum, and non-zero degree occurs exactly for the n dictatorships and n anti-dictatorships. All the other rules have degree 0; most of them impose a fixed top or bottom alternative and decide the remaining pair arbitrarily.)*

The degree separates the dictatorial and anti-dictatorial rules of Wilson's theorem on IIA without the Pareto condition from all other rules. Unanimity is used only once, to make the degrees sum to one.

## 3. More alternatives

With m alternatives, IIA lets the rule be restricted to any triple. By Proposition 1, under unanimity every triple has a dictator. Two triples that share a pair have the same dictator, because the dictator decides that pair. Any triple can be reached from any other by exchanging one alternative at a time, so there is one dictator for all. *(Proved; this is the usual reduction, as in Rajsbaum and Raventós-Pujol, Lemma 7.)*

Seen globally, the rankings of m alternatives form a sphere of dimension m − 2: utility vectors up to positive affine maps, divided into the chambers of the strict orders (*Cycles and Twists*, Proposition 6, where it appears as the complex of strict orders). For m ≥ 4 every loop on it contracts, so the degree is no longer a winding. It appears in two places:
- **On triples.** A loop of rankings on a triple is the Condorcet loop of that triple, and IIA is what makes these loops enough. The obstruction is a class on the cover by triples, glued along shared pairs. In the sheaf picture of thread A, the cover is by subsets of alternatives.
- **On the whole sphere.** Here it is a degree in dimension m − 2, as in Baryshnikov's computation, where the profile complex has the homology of a product of n spheres in that dimension (Baryshnikov and Root, Theorem 3).

Reversal is the antipodal map of the sphere, with degree (−1)^(m−1), so it preserves orientation exactly for odd m (*Cycles and Twists*, Section 5). For three alternatives it preserves orientation, which is why the anti-dictator has degree +1. For four alternatives it reverses orientation of the 2-sphere, and an anti-dictator has degree −1 there, while each triple still sees +1. *(Proved for the antipodal map; the reading of the anti-dictator's top degree is immediate from it.)* For m ≥ 4 the quotient by reversal is RP^(m−2), whose loops are counted only mod 2. The integer degree lives on the triples and on the top class. The loop that survives in the quotient is the pivotal half turn of Section 6, seen there only as a parity. This is the relation between the Condorcet cycle and the Liar in *Cycles and Twists* and *Loops of Relations*.

## 4. Real degrees

For a rule whose outcome is a lottery over rankings, the social ranking along a voter loop is random, and the degree becomes an expected winding.

Call a step of the loop **compatible** if the lotteries before and after it give the same joint law to the two comparisons that the step leaves alone. This is full compatibility in the sense of *Four Levels* on that pair of profiles. Then the social rankings can be drawn jointly so that each step changes at most the comparison the voter changes, and for any such joint draw the expected displacement of the step is fixed by the two lotteries. The rankings pair up as y and y′, where y′ is y with the flipped comparison (two rankings have no partner, since flipping would make a cycle). Only the net flow of probability between partners is determined, but that is enough, because the move from y′ to y has the opposite displacement of the move from y to y′. So

  deg_i(c) = (1/6) × Σ over the six steps of Σ over partner pairs {y, y′} of σ(y → y′) · (P_before(y) − P_after(y)),

where σ(y → y′) = ±1 is the direction of that edge on the hexagon. This is the **real degree** of voter i at c. It is defined whenever every step of the loop is compatible. *(Proved; computed by linear programming over all joint draws along the loop.)*

**Proposition 2.** For a mixture of dictatorships and anti-dictatorships, the real degree of voter i is the total weight of voter i's dictatorship and anti-dictatorship, at every context. For a fully compatible unanimous rule (an empirical model of *Four Levels*), the real degrees are the weights λ_i of the mixture of dictatorships, they sum to 1, and they do not depend on the context. *(Proved: only the components that follow voter i move along its loop, each by one full turn. The second part follows with Theorems 5 and 5′ of* Four Levels*. Computed for 200 random mixtures; the lotteries alone fix the expected winding.)*

So the two cases of the roadmap separate here. With integer degrees and anonymity, all degrees are equal and n · deg = 1 has no solution. With real degrees, deg_i = 1/n is the solution, and it is random dictatorship, the only anonymous mixture of dictatorships and so, by Theorems 5 and 5′, the only anonymous empirical model. The forced break is the absence of an integer point on the line Σ deg_i = 1 that is fixed by permuting the voters. The fixed point is the real point (1/n, …, 1/n). *(Interpretation of Propositions 1 and 2.)*

**Pairwise independence is not enough.** The coin rule of *Contextuality and Symmetry* follows unanimity on a pair and otherwise gives the pair probability ½. It satisfies Barberà and Sonnenschein's pairwise independence, but signals across pairs. Along a single voter loop it has compatible lotteries and joint draws, but its real degree depends on the context, whatever compatible lotteries with its marginals are chosen: with three voters it is ½ when the other two voters agree, 0 when they are two steps apart on the hexagon, and anywhere in [0, ½] at one step apart and in [0, 1] when they hold opposite rankings. *(Computed, all 216 profiles.)* Because the rule cannot be made fully compatible (*Contextuality and Symmetry*), no choice of its lotteries works for all loops at once, and its degree is not a class. Full independence is what makes the real degree a class. This is the same line that separates the mixtures of dictatorships from the coin rule in *Four Levels*. *(Interpretation.)*

## 5. Continuous rules

For continuous maps from n circles to the circle, Lemmas 1 and 2 hold with ordinary degrees, and unanimity gives Σ deg_i = 1. Anonymity gives n · deg = 1, Chichilnisky's impossibility for the circle. There is no rigidity: (x, y) ↦ x²y⁻¹, in complex notation on the unit circle, is unanimous with degrees (2, −1). IIA is what bounds the degrees and turns a non-zero degree into a dictator. Continuity and IIA are two forms of locality, and only the discrete one is rigid. *(Proved; the example is standard.)*

## 6. Reversal and the pivotal path

The pivotal-voter path of *Cycles and Twists*, Section 5, runs from a unanimous profile at x to the unanimous profile at its reverse, each voter making a half turn in turn. It is half of the diagonal loop, and in the quotient by reversal of the whole profile and the outcome it closes. For three alternatives the quotient of the hexagon by the half rotation is again a circle, the core of the Möbius strip in *Cycles and Twists*, Section 5. The half turn goes once around it, and a voter's full loop, the Condorcet loop, goes twice. So the Condorcet cycle is twice the pivotal path. *(Proved.)*

For a mixture of dictatorships, the probability that moves during voter k's switch is the weight λ_k, which is the real degree. The path therefore reads off the degrees with n half turns instead of n full loops. This is why the twist crosses the even mixture of x and its reverse at the weighted median of the switching order. *(Proved; computed in* `scripts/topology/pivotal_path.py`*.)*

For a general rule the shares of the half path are taken at different contexts for different voters, and Lemma 1 makes only the closed loop invariant. Pivotal arguments use the half path because unanimity fixes both of its ends. The topological arguments use the closed loop because only it carries a class. *(Interpretation.)*

## 7. Strategy-proofness

The same construction works for Gibbard–Satterthwaite. A rule now sends each profile to one alternative, and it is strategy-proof (SP) if no voter gains by misreporting. Unanimity is taken in the weak form that identical ballots give their common top. The outcomes a, b, c form a triangle, oriented a → b → c → a. Any two outcomes are adjacent, so the walk of the outcome along a voter loop always has a winding number. What strategy-proofness adds is the direction of each step.

**Swap lemma.** If a voter swaps two adjacent alternatives in their ballot, raising y over x, an SP rule can change the outcome only from x to y. For a lottery-valued rule that is strategy-proof in the sense of stochastic dominance (SD-SP), the swap moves probability only from x to y, and leaves every other probability unchanged. *(Proved; standard. Strategy-proofness for both ballots leaves only the pair {x, y} where the two ballots disagree. For lotteries, the upper contour sets of the two ballots coincide except for the one cut between x and y. This is Gibbard's (1977) localisation and monotonicity.)*

Along the loop abc → bac → bca → cba → cab → acb → abc, the six swaps raise b over a, c over a, c over b, a over b, a over c and b over c. The permitted moves of the outcome are therefore a → b, a → c, b → c, b → a, c → a and c → b. They go alternately forward and backward on the triangle.

**Lemma 5 (invariance and sum).** For an SP rule, the degree of a voter does not depend on the context, and the degrees sum to the winding of the diagonal staircase. Under unanimity the sum is 1. *(Proved.)*
- **Squares.** In a square of one step of voter i and one of voter j, the two steps of each voter swap the same pair in opposite directions, so their permitted moves go in opposite senses. At most two of the four moves go the same way. A closed walk on the triangle with net displacement at most 2 has winding 0.
- **Staircase.** Successive swaps of the same pair by different voters can move the outcome at most once, from x to y, never back. So the staircase follows the tops of the diagonal rankings. The map that sends a ranking to its top takes the hexagon once around the triangle.

**Lemma 6 (rigidity).** For an SP rule the degree is 0 or 1. It is 1 exactly when the outcome is the voter's top at every step of the loop. *(Proved.)* Winding 1 needs the three forward moves (at the first, third and fifth step) and no backward one, which places the outcome at the voter's top throughout. Winding −1 needs the three backward moves. That is impossible: after the backward move a → c at the second step, the outcome cannot be at b before the fourth step, because the only permitted move in between is b → c.

**Proposition 3.** For three alternatives, an SP rule either gives every voter degree 0, or is the dictatorship of the one voter with degree 1. With unanimity it is a dictatorship. *(Proved, from Lemmas 5 and 6; the second part is the Gibbard–Satterthwaite theorem for three alternatives. Computed: all SP rules for one voter, 7 rules, and two voters, 17 rules.)* Unlike Arrow's case, no anti-dictator appears. Strategy-proofness fixes the direction in which the outcome may follow the voter, and IIA does not.

**More alternatives.** The degree is used only on triples. The usual steps lead from there to all alternatives. *(Proved; standard.)*
1. Strategy-proofness implies monotonicity: if y wins and no voter lowers y below anything, y still wins.
2. Monotonicity with unanimity gives the Pareto condition: move x to the top and y to second for everyone.
3. For a triple T, the rule restricted to profiles in which every voter ranks T in the top three, over fixed tails, is SP and unanimous on T. So it has a dictator.
4. Changing the tails swaps only alternatives outside T, which cannot change an outcome in T, so the dictator does not depend on the tails.
5. Triples sharing two alternatives have the same dictator: pass from one to the other by swapping the third alternatives below the shared pair.
6. Monotonicity extends the dictator to all profiles: lift the dictator's top and the claimed winner to the top two places.

**Real degrees.** For an SD-SP lottery the real degree is the expected winding, (1/3) times the sum over the six steps of the signed probability moved. By the swap lemma this is defined for every SD-SP rule. These are exactly the empirical models of *Gibbard–Satterthwaite as a Scenario* (Proposition 1 there), so no compatibility condition is needed, unlike Arrow's case. In a square, the two voters move probability along the directions e_y − e_x and e_v − e_u in the plane of lotteries, and the lottery returns to where it started. If the pairs differ, the directions are independent, so each voter's forward and backward moves cancel. If the pairs coincide, the displacements cancel directly. So the real degree is a class for every SD-SP rule, and the degrees sum to the staircase winding, which is 1 under unanimity. *(Proved. Computed by linear programming over all SD-SP rules for two and three voters: deviation below 10⁻¹⁵.)*

What values occur:
- **With unanimity**, by Gibbard (1977) the rule is a mixture of dictatorships, and the degrees are its weights, in [0, 1], summing to 1 (the linear programs give the same range). Anonymity makes them 1/n, random dictatorship, as in Section 4.
- **Without unanimity, degrees can be negative.** The random top two (the voter's first or second choice, probability ½ each) has degree −½. At each backward step half of the probability moves backward, and the forward steps move nothing. This is the minimum over all SD-SP rules for one, two and three voters. *(Computed.)*

**Proposition 4.** Every deterministic SP rule has degrees 0 or 1, so every mixture of them has degrees in [0, 1]. A negative degree therefore shows that a model is contextual. For one voter the converse holds: an SD-SP lottery is a mixture of deterministic SP rules exactly when its degree is non-negative. *(Proved for one voter; computed for two and three voters, where the polytope of SD-SP rules with all degrees non-negative has the same support function as the hull of the 17 and 60 deterministic SP rules in random directions.)*

The one-voter proof uses the flows along the loop. Let α₁, …, α₆ be the probabilities moved at the six steps. Conservation of probability forces α₁ − α₄ = α₃ − α₆ = α₅ − α₂, and this common value D is the degree. If D ≥ 0, take:
- the dictatorship with weight D;
- the three rules "the voter's better of two", with weights α₄, α₆ and α₂, each moving once forward and once backward along its edge;
- constants for the remaining probability, which is non-negative because each alternative can lose at most the probability it holds.

So the contextuality of the random top two, which *Gibbard–Satterthwaite as a Scenario* shows by a linear program, is seen here as a degree outside the hull of the deterministic degrees. In Arrow's scenario the failure takes another form: the coin rule, which is not fully compatible, has no class at all. In the Gibbard–Satterthwaite scenario every model is compatible, and the obstruction is the sign of the degree. *(Interpretation.)*

## 8. Relation to the literature

- **Baryshnikov (1993)**: Arrow's theorem by the homology of a nerve. Baryshnikov and Root describe his computation as showing that the profile complex has, in dimension m − 2, the homology of a product of n spheres, and they reprove it. They obtain Gibbard–Satterthwaite through Muller–Satterthwaite: a monotone unanimous rule induces a simplicial map, and the pairing of each voter's class with the outcome class is 1 for a dictator and 0 otherwise.
- **Okura (2024)**: the same structure with the relation "sum of the voters' maps on homology equals the diagonal". Lemma 2 is this relation for three alternatives.
- **Rajsbaum and Raventós-Pujol**: an elementary proof by the index lemma on a colored triangulation, with pivotal voters as bivalent paths, and a characterisation of domain restrictions for two voters and three alternatives. **Lara, Rajsbaum and Raventós-Pujol** generalise this.

Sections 1–3, and the deterministic part of Section 7, are therefore not new in substance; Baryshnikov and Root reach Gibbard–Satterthwaite by the same kind of class, through monotonicity. They are a short form of the homological proof, with the hexagon and the triangle as the spaces and the rigidity of Lemmas 3, 4 and 6 in place of the injectivity arguments. None of these papers treats lotteries, real coefficients or reversal (checked for Baryshnikov–Root, Okura and Rajsbaum–Raventós-Pujol; Baryshnikov's paper itself was not accessible here). Sections 4, 6 and the lottery part of Section 7 are the additions: the real degree, its identification with the weights of Theorems 5 and 5′ and of Gibbard (1977), the coin rule as a rule without a class, negative degrees as witnesses of contextuality for strategy-proof lotteries, and the pivotal path as half of the loop.

## 9. What the global form still needs

- **Strategy-proof lotteries.** Proposition 4 for two or more voters, and for more alternatives, by proof; a direct proof that unanimity makes the real degrees non-negative, without Gibbard (1977); the meaning of the negative degree of the random top two, whose lottery turns against the direction of the voter's own loop.
- **An equivariant statement.** Degrees are a homomorphism from the voters' classes to the outcome class. Permuting the voters acts on the first, and reversal acts on both, with sign (−1)^(m−1) on the top class. The trichotomy of *Where the Symmetry Goes* should read as: an equivariant integer homomorphism exists (no obstruction), only a real one exists (a lottery), or none exists. This is not yet worked out beyond the voters' permutations.
- **Degree for the electorate direction.** Young–Levenglick and the no-show theorem are agreement-type obstructions (thread A). Whether they carry a degree, or only a local inconsistency, is open.
- Lemmas 1–6 are finite and elementary for each n, and a candidate for a Lean check.

## References

- Barberà, S. and Sonnenschein, H. (1978). Preference aggregation with randomized social orderings. *Journal of Economic Theory* 18, 244–254.
- Baryshnikov, Y. (1993). Unifying impossibility theorems: a topological approach. *Advances in Applied Mathematics* 14, 404–415.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Lara, I., Rajsbaum, S. and Raventós-Pujol, A. (2024). A generalization of Arrow's impossibility theorem through combinatorial topology. arXiv:2402.06024.
- Okura, T. (2024). A topological proof of Terao's generalized Arrow's impossibility theorem. arXiv:2408.14263.
- Rajsbaum, S. and Raventós-Pujol, A. (2022). A combinatorial topology approach to Arrow's impossibility theorem. PODC 2022; extended version MPRA paper 120023.
- Wilson, R. (1972). Social choice theory without the Pareto principle. *Journal of Economic Theory* 5, 478–486.
- *Four Levels of Obstruction in Social Choice*, *Cycles and Twists* (drafts); *Contextuality and Symmetry*, *Loops of Relations*, *Where the Symmetry Goes*, *Gibbard–Satterthwaite as a Scenario* (working notes), all in this repository.
