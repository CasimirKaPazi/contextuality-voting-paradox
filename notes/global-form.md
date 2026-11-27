# The Global Form: Arrow's Theorem as a Degree

*Working note for thread B of the roadmap. It writes Arrow's theorem as an obstruction along loops: every voter gets a degree, the winding of the social ranking while that voter's ranking goes once around the circle of rankings. Unanimity makes the degrees sum to one. Independence of irrelevant alternatives makes them integers in {−1, 0, 1} and rigid. For lotteries the degree becomes a real number, and the uniform weights 1/n that anonymity demands exist only there. The integer part is in substance Baryshnikov's homological proof, written here with a hexagon instead of a nerve; the real degrees, their failure for rules with only pairwise independence, the place of reversal, and the same construction for strategy-proof rules, where the negative parts of the real degrees measure contextuality, are added. Proved statements, computed checks and interpretation are marked. Checks:* `scripts/topology/voter_degrees.py`, `scripts/strategy/gs_degrees.py`, `scripts/strategy/degree_tower.py`, `scripts/topology/candidate_simplex.py`. *Lemmas 1–6 and Propositions 1 and 3 are checked in Lean:* `lean/GlobalForm.lean`, `lean/GlobalFormSP.lean`.

## 1. Voter loops

Take three alternatives a, b, c. The six strict rankings form a hexagon, two rankings being adjacent when they differ in one comparison: abc, bac, bca, cba, cab, acb and back to abc. Going once around flips each of the three comparisons twice, once in each direction. This is the Condorcet loop of one ballot. Reversal of a ranking is the half rotation of the hexagon.

A rule F sends each profile of n rankings to a ranking. Fix all voters but one, voter i, at some context c, and let voter i walk once around the hexagon. Each step changes voter i's comparison on one pair and nothing else in the profile. If F satisfies independence of irrelevant alternatives (IIA), the social ranking can change only on that pair, and two rankings that differ on exactly one pair are adjacent. So the social ranking also walks on the hexagon, standing still or moving to a neighbour at each step, and its walk closes when voter i returns. Its winding number is the **degree** of voter i at context c, written deg_i(c).

Without IIA the walk can jump between rankings that are not adjacent, and then it has no winding number. *(Computed: for Borda, Copeland and plurality with a fixed tie-break, the social ranking jumps on a third or more of random voter loops, and where the winding is defined it is 0 at some contexts and 1 at others.)*

## 2. Three alternatives

**Lemma 1 (invariance).** Under IIA, deg_i(c) does not depend on the context c, nor on where voter i starts. *(Proved; checked in Lean for any finite set of voters, `lean/GlobalForm.lean`.)* Starting elsewhere on the same loop gives the same closed walk. Let another voter j take one step. The two loops of voter i, before and after, are joined by squares, each made of one step of i and one step of j. Around a square the social ranking takes at most four steps on a hexagon, which cannot go around it, so each square has winding 0 and the two loops have equal winding. Any context is reached from any other by such steps.

**Lemma 2 (sum).** Let all voters stand at the same ranking and move together once around (the diagonal loop). Under IIA its winding is the sum of the degrees. *(Proved; checked in Lean for any finite set of voters, `lean/GlobalForm.lean`.)* Replace each joint step by the voters' steps one after another. Each of these flips the same pair, so the social ranking stays on one edge meanwhile and ends where the joint step ends. The result is a staircase loop. Swapping two adjacent steps of different voters is a square, so the staircase deforms into the loops of voter 1, then voter 2, and so on, whose windings add. By Lemma 1 each is deg_i.

Under unanimity the social ranking on the diagonal loop is the common ranking itself, which winds once. So

  deg_1 + … + deg_n = 1.

**Lemma 3 (rigidity).** Under IIA every degree is −1, 0 or 1, and a voter with non-zero degree is pivotal on every pair at every context. *(Proved; checked in Lean for any finite set of voters, `lean/GlobalForm.lean`, in the sharper form that the degree is 0 or 1: for rules into rankings −1 does not occur, as also follows from Lemma 4 and Proposition 1.)* A loop has six steps and the social ranking moves at most one position per step, so |deg_i| ≤ 1. Winding ±1 needs all six steps in the same direction, so the social comparison flips every time voter i flips one. By Lemma 1 this holds at every context. Hence on each pair e the social comparison is voter i's comparison, exclusive-or a function g_e of the other voters' comparisons on e.

**Lemma 4 (no mask).** If F_e = x_i ⊕ g_e on every pair and the output is always a ranking, then all g_e are equal and constant. *(Proved; checked in Lean for any finite set of voters, `lean/GlobalForm.lean`.)* For a fixed context, g = (g_ab, g_bc, g_ca) is a mask applied to voter i's ranking, and voter i can hold any of the six rankings. Flipping only the comparison between the top and the bottom of a ranking makes a cycle, and so does flipping only the other two. Every pair is the top–bottom pair of some ranking, so the only masks that keep all six rankings transitive are "flip nothing" and "flip everything". Hence g_ab(c_ab) = g_bc(c_bc) for all columns. Any two pairs' columns can be chosen independently (each combination of two comparisons occurs in some ranking), so both are constant.

**Proposition 1.** For three alternatives and any number of voters, an IIA rule into rankings either gives every voter degree 0, or gives exactly one voter degree 1 and is that voter's dictatorship or anti-dictatorship (the reverse of the voter's ranking). With unanimity it is a dictatorship. *(Proved, from Lemmas 1–4; the second part is Arrow's theorem. Checked in Lean for any finite set of voters, `lean/GlobalForm.lean`.)* By Lemmas 3 and 4, a voter with non-zero degree is a dictator (g = 0) or an anti-dictator (g = 1), and then every other voter is irrelevant. Both have degree 1, because reversal is a rotation of the hexagon and keeps its orientation. Under unanimity the degrees sum to 1, so some degree is non-zero, and the anti-dictatorship is excluded.

*(Computed: all IIA rules into rankings for two voters, 94 rules, and three voters, 1536 rules. In every one the degree is the same at all contexts, the diagonal winding is the sum, and non-zero degree occurs exactly for the n dictatorships and n anti-dictatorships. All the other rules have degree 0; most of them impose a fixed top or bottom alternative and decide the remaining pair arbitrarily.)*

The degree separates the dictatorial and anti-dictatorial rules of Wilson's theorem on IIA without the Pareto condition from all other rules. Unanimity is used only once, to make the degrees sum to one.

## 3. More alternatives

With m alternatives, IIA lets the rule be restricted to any triple. By Proposition 1, under unanimity every triple has a dictator. Two triples that share a pair have the same dictator, because the dictator decides that pair. Any triple can be reached from any other by exchanging one alternative at a time, so there is one dictator for all. *(Proved; this is the usual reduction, as in Rajsbaum and Raventós-Pujol, Lemma 7.)*

Seen globally, the rankings of m alternatives form a sphere of dimension m − 2: utility vectors up to positive affine maps, divided into the chambers of the strict orders (*Cycles and Twists*, Proposition 6, where it appears as the complex of strict orders). For m ≥ 4 every loop on it contracts, so the degree is no longer a winding. It appears in two places:
- **On triples.** A loop of rankings on a triple is the Condorcet loop of that triple, and IIA is what makes these loops enough. The obstruction is a class on the cover by triples, glued along shared pairs. In the sheaf picture of thread A, the cover is by subsets of alternatives.
- **On the whole sphere.** Here it is a degree in dimension m − 2, as in Baryshnikov's computation, where the profile complex has the homology of a product of n spheres in that dimension (Baryshnikov and Root, Theorem 3).

Reversal is the antipodal map of the sphere, with degree (−1)^(m−1), so it preserves orientation exactly for odd m (*Cycles and Twists*, Section 5). For three alternatives it preserves orientation, which is why the anti-dictator has degree +1. For four alternatives it reverses orientation of the 2-sphere, and an anti-dictator has degree −1 there, while each triple still sees +1. *(Proved for the antipodal map; the reading of the anti-dictator's top degree is immediate from it.)* For m ≥ 4 the quotient by reversal is RP^(m−2), whose loops are counted only mod 2. The integer degree lives on the triples and on the top class. The loop that survives in the quotient is the pivotal half turn of Section 6, seen there only as a parity. This is the relation between the Condorcet cycle and the Liar in *Cycles and Twists* and *Loops of Relations*.

## 3a. The sphere of rankings and the simplex of candidates

*The facts in this section are standard; the readings are marked. Checks:* `scripts/topology/candidate_simplex.py`.

The sphere of rankings of Section 3, the simplex whose vertices are the candidates, and the space of pairwise comparisons are related by three maps. All three commute with renaming the candidates.

**Rankings as flags.** Write a ballot as a utility vector u with coordinate sum zero, and let Δ be the simplex spanned by the centred unit vectors of the m candidates. For every nonempty proper set S of candidates, let v_S be the direction of the centred indicator vector of S: the ballot that puts S on top, tied, and the rest below, tied. Every ballot is a non-negative combination of the v_S of its top sets,

  u = Σ_{k=1}^{m−1} (u_(k) − u_(k+1)) · (centred indicator of the top k candidates),

where u_(1) ≥ … ≥ u_(m) are its coordinates in decreasing order. So the chamber of a ranking is the cone over the chain top-1 ⊂ top-2 ⊂ … ⊂ top-(m−1), a maximal chain of faces of Δ. The cell complex of the sphere of rankings is therefore the **barycentric subdivision of the boundary of Δ**. Its vertices are the faces of Δ, which are the ballots with two levels, and its cells are chains of faces, which are the weak orders. *(Proved by the identity; checked for m ≤ 6.)*

**The hexagon.** For three candidates the sphere is the circle of Section 1. Its six vertices are the three corners and the three edge midpoints of the triangle, and the ranking abc is the half-edge from the corner a to the midpoint of ab. The steps of the voter loop alternate between keeping the top pair, around a midpoint (abc to bac around ab), and keeping the top candidate, around a corner (bac to bca around b). So the voter loop of Section 1 is the boundary of the triangle of candidates, traversed once, and the degree of a voter is a winding around that triangle. Reversal sends the vertex of S to the vertex of its complement, a corner to the midpoint of the opposite edge, which is the half rotation of Section 1. *(Checked.)*

**The permutohedron** is the dual picture. It is the convex hull of the permutations of (0, 1, …, m − 1), and it is the simplex Δ with all its faces cut off. Its vertices are the rankings, its faces the weak orders, its centre complete indifference, and its edges the swaps of two adjacent candidates. For three candidates it is a hexagon again, with the rankings as corners rather than sides. For four it is the truncated octahedron.

**Radial projection.** Projecting from the centre of Δ identifies its boundary with the sphere of rankings. In coordinates, the ray in direction u leaves Δ at

  p_x = (u_x − min u) / Σ_y (u_y − min u),

and the face spanned by S goes to v_S. Since Δ, shifted back, is the simplex of lotteries over the candidates, the map can be read as sending a ballot to the lottery proportional to each candidate's utility above the worst. *(The formula is checked for m ≤ 6; the reading is interpretation.)*

**Comparisons as edges.** The permutohedron is also the Minkowski sum of the edges of Δ, one segment for each pair of candidates (a zonotope). A tournament picks one endpoint of each segment, the winner of that pair, and the sum of the chosen endpoints is the tournament's score vector, the number of wins of each candidate. By Landau's theorem, through Rado's characterisation of the permutohedron by majorisation, the score vectors of tournaments are exactly the lattice points of the permutohedron. Each ranking is the only tournament at its vertex. *(Cited; checked for m ≤ 6.)*

Cyclic tournaments go inside. For three candidates both Condorcet cycles go to the centre (1, 1, 1), the point fixed by every renaming. In terms of margins, the map is the divergence: summing row x of the margin matrix gives 2B(x) − (m − 1), with B(x) the Borda score. The divergence is the adjoint of the gradient u ↦ (u_x − u_y), and its kernel is the cyclic part of the pairwise data, of dimension (m − 1)(m − 2)/2 (Hodge and Saari decompositions). *(Checked for m ≤ 5.)* So the score map is Borda's: each voter's ranking is a vertex, the profile goes to the average of the vertices, and the cyclic part goes to the centre. This is observation 5 of *Where the Symmetry Goes* in geometric form: the cycle lands on the fixed point. It is also why the meeting point of Borda's winning regions in Section 10 lies on the cyclic axis. *(Interpretation.)*

**The sphere of pairwise data.** The gradient map embeds the sphere of rankings, of dimension m − 2, into the sphere of pairwise data, of dimension m(m − 1)/2 − 1. That sphere is the boundary of the cross-polytope with one axis for each pair of candidates, that is, for each edge of Δ. Its vertices are the ordered pairs "x above y", its facets the tournaments, and the rankings are some of the facets (*Cycles and Twists*, Proposition 6). For three candidates it is the octahedron. Its six transitive faces form a band around the equator, the hexagon of rankings, and the two cyclic faces are caps around the poles, which are the purely cyclic directions orthogonal to the plane of gradients. Livson, Pritam and Prokopenko build their complex as a nerve whose vertices are the ordered pairs and whose triangles are the strict orders. It is this band, an annulus whose two boundary circles are the two cycles.

**Summary.** Three spaces carry the problem. The simplex of candidates has the candidates as vertices and the pairs as edges. The sphere of rankings is its subdivided boundary, dual to the permutohedron, with flags of faces as rankings. The cross-polytope of comparisons has one axis per edge of the simplex and the tournaments as facets. Radial projection, the score map (divergence) and the gradient connect them. The degree of Sections 1 to 3 is the winding of the social ranking around the boundary of the simplex. The score map shows where the cyclic part goes when a rule reads positions instead of comparisons. *(Interpretation; the maps themselves are standard.)*

## 4. Real degrees

For a rule whose outcome is a lottery over rankings, the social ranking along a voter loop is random, and the degree becomes an expected winding.

Call a step of the loop **compatible** if the lotteries before and after it give the same joint law to the two comparisons that the step leaves alone. This is full compatibility in the sense of *Four Levels* on that pair of profiles. Then the social rankings can be drawn jointly so that each step changes at most the comparison the voter changes, and for any such joint draw the expected displacement of the step is fixed by the two lotteries. The rankings pair up as y and y′, where y′ is y with the flipped comparison (two rankings have no partner, since flipping would make a cycle). Only the net flow of probability between partners is determined, but that is enough, because the move from y′ to y has the opposite displacement of the move from y to y′. So

  deg_i(c) = (1/6) × Σ over the six steps of Σ over partner pairs {y, y′} of σ(y → y′) · (P_before(y) − P_after(y)),

where σ(y → y′) = ±1 is the direction of that edge on the hexagon. This is the **real degree** of voter i at c. It is defined whenever every step of the loop is compatible. *(Proved; computed by linear programming over all joint draws along the loop.)*

**Proposition 2.** For a mixture of dictatorships and anti-dictatorships, the real degree of voter i is the total weight of voter i's dictatorship and anti-dictatorship, at every context. For a fully compatible unanimous rule (an empirical model of *Four Levels*), the real degrees are the weights λ_i of the mixture of dictatorships, they sum to 1, and they do not depend on the context. *(Proved: only the components that follow voter i move along its loop, each by one full turn. The second part follows with Theorems 5 and 5′ of* Four Levels*. Computed for 200 random mixtures; the lotteries alone fix the expected winding.)*

So the two cases of the roadmap separate here. With integer degrees and anonymity, all degrees are equal and n · deg = 1 has no solution. With real degrees, deg_i = 1/n is the solution, and it is random dictatorship, the only anonymous mixture of dictatorships and so, by Theorems 5 and 5′, the only anonymous empirical model. The forced break is the absence of an integer point on the line Σ deg_i = 1 that is fixed by permuting the voters. The fixed point is the real point (1/n, …, 1/n). *(Interpretation of Propositions 1 and 2.)*

**Pairwise independence is not enough.** The coin rule of *Contextuality and Symmetry* follows unanimity on a pair and otherwise gives the pair probability ½. It satisfies Barberà and Sonnenschein's pairwise independence, but signals across pairs. Along a single voter loop it has compatible lotteries and joint draws, but its real degree depends on the context, whatever compatible lotteries with its marginals are chosen: with three voters it is ½ when the other two voters agree, 0 when they are two steps apart on the hexagon, and anywhere in [0, ½] at one step apart and in [0, 1] when they hold opposite rankings. *(Computed, all 216 profiles.)* Because the rule cannot be made fully compatible (*Contextuality and Symmetry*), no choice of its lotteries works for all loops at once, and its degree is not a class. Full independence is what makes the real degree a class. This is the same line that separates the mixtures of dictatorships from the coin rule in *Four Levels*. *(Interpretation.)*

## 5. Continuous rules

For continuous maps from n circles to the circle, Lemmas 1 and 2 hold with ordinary degrees, and unanimity gives Σ deg_i = 1. Anonymity gives n · deg = 1, Chichilnisky's impossibility for the circle. Without a Pareto condition the degrees are not bounded: (x, y) ↦ x²y⁻¹, in complex notation on the unit circle, is unanimous with degrees (2, −1). *(Proved; the example is standard.)* With Pareto they are. Chichilnisky (1982), as Baryshnikov (1993) states it: continuous rules on spheres of linear preferences that respect unanimity on every comparison have exactly one "manipulator", a voter who can produce any social preference. So continuity with Pareto gives degrees 0 or 1. The discrete counterpart, for rules that are only local, is the pinning lemma of *Equivariant Obstructions*. What IIA adds is that the voter of degree 1 is a dictator and not merely a manipulator.

## 6. Reversal and the pivotal path

The pivotal-voter path of *Cycles and Twists*, Section 5, runs from a unanimous profile at x to the unanimous profile at its reverse, each voter making a half turn in turn. It is half of the diagonal loop, and in the quotient by reversal of the whole profile and the outcome it closes. For three alternatives the quotient of the hexagon by the half rotation is again a circle, the core of the Möbius strip in *Cycles and Twists*, Section 5. The half turn goes once around it, and a voter's full loop, the Condorcet loop, goes twice. So the Condorcet cycle is twice the pivotal path. *(Proved.)*

For a mixture of dictatorships, the probability that moves during voter k's switch is the weight λ_k, which is the real degree. The path therefore reads off the degrees with n half turns instead of n full loops. This is why the twist crosses the even mixture of x and its reverse at the weighted median of the switching order. *(Proved; computed in* `scripts/topology/pivotal_path.py`*.)*

For a general rule the shares of the half path are taken at different contexts for different voters, and Lemma 1 makes only the closed loop invariant. Pivotal arguments use the half path because unanimity fixes both of its ends. The topological arguments use the closed loop because only it carries a class. *(Interpretation.)*

## 7. Strategy-proofness

The same construction works for Gibbard–Satterthwaite. A rule now sends each profile to one alternative, and it is strategy-proof (SP) if no voter gains by misreporting. Unanimity is taken in the weak form that identical ballots give their common top. The outcomes a, b, c form a triangle, oriented a → b → c → a. Any two outcomes are adjacent, so the walk of the outcome along a voter loop always has a winding number. What strategy-proofness adds is the direction of each step.

**Swap lemma.** If a voter swaps two adjacent alternatives in their ballot, raising y over x, an SP rule can change the outcome only from x to y. For a lottery-valued rule that is strategy-proof in the sense of stochastic dominance (SD-SP), the swap moves probability only from x to y, and leaves every other probability unchanged. *(Proved; standard; the deterministic part, for three alternatives, is checked in Lean, `lean/GlobalFormSP.lean`. Strategy-proofness for both ballots leaves only the pair {x, y} where the two ballots disagree. For lotteries, the upper contour sets of the two ballots coincide except for the one cut between x and y. This is Gibbard's (1977) localisation and monotonicity.)*

Along the loop abc → bac → bca → cba → cab → acb → abc, the six swaps raise b over a, c over a, c over b, a over b, a over c and b over c. The permitted moves of the outcome are therefore a → b, a → c, b → c, b → a, c → a and c → b. They go alternately forward and backward on the triangle.

**Lemma 5 (invariance and sum).** For an SP rule, the degree of a voter does not depend on the context, and the degrees sum to the winding of the diagonal staircase. Under unanimity the sum is 1. *(Proved; checked in Lean for any finite set of voters, `lean/GlobalFormSP.lean`.)*
- **Squares.** In a square of one step of voter i and one of voter j, the two steps of each voter swap the same pair in opposite directions, so their permitted moves go in opposite senses. At most two of the four moves go the same way. A closed walk on the triangle with net displacement at most 2 has winding 0.
- **Staircase.** Successive swaps of the same pair by different voters can move the outcome at most once, from x to y, never back. So the staircase follows the tops of the diagonal rankings. The map that sends a ranking to its top takes the hexagon once around the triangle.

**Lemma 6 (rigidity).** For an SP rule the degree is 0 or 1. It is 1 exactly when the outcome is the voter's top at every step of the loop. *(Proved; checked in Lean for any finite set of voters, `lean/GlobalFormSP.lean`.)* Winding 1 needs the three forward moves (at the first, third and fifth step) and no backward one, which places the outcome at the voter's top throughout. Winding −1 needs the three backward moves. That is impossible: after the backward move a → c at the second step, the outcome cannot be at b before the fourth step, because the only permitted move in between is b → c.

**Proposition 3.** For three alternatives, an SP rule either gives every voter degree 0, or is the dictatorship of the one voter with degree 1. With unanimity it is a dictatorship. *(Proved, from Lemmas 5 and 6; the second part is the Gibbard–Satterthwaite theorem for three alternatives. Checked in Lean for any finite set of voters, `lean/GlobalFormSP.lean`. Computed: all SP rules for one voter, 7 rules, and two voters, 17 rules.)* Unlike Arrow's case, no anti-dictator appears. Strategy-proofness fixes the direction in which the outcome may follow the voter, and IIA does not.

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
- **Without unanimity, degrees can be negative.** The random top two (the voter's first or second choice, probability ½ each) has degree −½. At each backward step half of the probability moves backward, and the forward steps move nothing. This is the minimum over all SD-SP rules, for any number of voters. *(Computed for one, two and three voters; proved in Propositions 4 and 5.)*

Every deterministic SP rule has degrees 0 or 1 (Lemma 6), so every mixture of them has degrees in [0, 1]. A negative degree therefore shows that a model is contextual. The converse holds, and the degree measures how far a model is from the mixtures.

**Proposition 4 (one voter).** For one voter and three alternatives, the SD-SP lotteries are exactly the mixtures of the seven deterministic SP rules and the random top two. The deterministic rules are the constants, the three rules "the better of a fixed pair" and the dictatorship. The degree D is at least −½. In every such mixture the random top two has weight at least −2D, and this bound is attained. *(Proved; computed: the vertices found by linear programs in random directions are these eight. Checked in Lean, `lean/GlobalFormLottery.lean`, with the weights of the proof below.)*

The proof uses the flows along the loop. Let α₁, …, α₆ ≥ 0 be the probabilities moved at the six steps. Conservation of probability forces α₁ − α₄ = α₃ − α₆ = α₅ − α₂, and this common value is D.
- **If D ≥ 0**, take the dictatorship with weight D; the three "better of two" rules with weights α₄, α₆ and α₂, each moving once forward and once backward along its edge; and constants for the remaining probability. The constants get non-negative weight because each alternative can lose at most the probability it holds.
- **If D < 0**, subtract the random top two with weight −2D. It moves ½ at each backward step and nothing at the forward ones. The backward flows suffice, since α₄ = α₁ − D ≥ −D and likewise α₆, α₂. The lotteries stay non-negative: at each ranking the top and the second each carry at least −D. The top still has to give up a backward flow before it can gain anything. The second has either just received a backward flow or is about to give one up. The remainder has degree 0 and falls under the first case. The same two observations bound the top and the second together by 1 at each ranking, so D ≥ −½.

**Proposition 5 (any number of voters).** For three alternatives and any number of voters, the SD-SP lotteries are exactly the mixtures of the deterministic SP rules and the n random top twos, one per voter. A lottery rule is non-contextual, a mixture of deterministic SP rules, exactly when no degree is negative. Its contextual fraction is

  CF = 2 × Σ_i max(0, −deg_i).

The contextual fraction is the least weight of a contextual part in a decomposition into a non-contextual model and another model of the scenario (Abramsky, Barbosa and Mansfield). *(Proved, from Gibbard 1977 and Proposition 4. Computed: vertices for one and two voters; the fraction by linear programming on random mixtures for one, two and three voters. Checked in Lean, `lean/ContextualFraction.lean`, with Gibbard's theorem as a hypothesis that includes SD-SP components, and with non-contextual taken as a mixture of deterministic SP rules.)*

Proof:
- **The mixtures.** By Gibbard, an SD-SP rule is a mixture of SP unilateral and SP duple rules.
  - A duple on {x, y} gives x a probability that depends only on which voters prefer x to y, and does not decrease when more do. This follows from localisation and monotonicity. Such a function is a mixture of monotone yes-or-no functions, by thresholds, so the duple is a mixture of deterministic SP duples, each of degree 0.
  - Grouping the unilateral components by voter gives one one-voter SD-SP rule per voter, weighted. A unilateral rule of one voter has degree 0 for every other voter.
  - Proposition 4 then gives the mixtures. In such a mixture, voter i's degree is the weight of i's dictatorship minus half the weight of i's random top two.
- **The fraction.** Take a decomposition into a non-contextual part, weight 1 − λ, and any model, weight λ. On the voters with negative degree, the degrees of the non-contextual part are non-negative. Those of any model sum to at least −½, because each vertex is negative for at most one voter, by ½. Hence λ ≥ 2 Σ_i max(0, −deg_i). Taking the random top twos with weights −2 deg_i for these voters attains the bound.

The random top two is the average of two positional rules: the voter's top, of degree 1, and the voter's second choice, of degree −2. The voter's bottom has degree 1 again. The three degrees sum to 0, as they must, since the three positions together give every alternative once. Strategy-proofness admits the second choice only in this average, and the average is the one contextual vertex. *(Computed degrees; interpretation.)*

So the contextuality of the random top two, which *Gibbard–Satterthwaite as a Scenario* shows by a linear program, is seen here as a degree outside the hull of the deterministic degrees, and its amount is measured by the degree. In Arrow's scenario the failure takes another form: the coin rule, which is not fully compatible, has no class at all. In the Gibbard–Satterthwaite scenario every model is compatible, and the obstruction is the sign of the degree. *(Interpretation.)*

## 8. The stack of degrees (one voter)

*A first look, to be revisited.* For one voter the degree of Section 7 is the top layer of a stack of degrees, one for each dimension of the faces of the permutohedron, and the stack gives coordinates for the rule. The deterministic SP rules for one voter are the 2^m − 1 rules "best of S", the voter's best alternative in a fixed non-empty set S.
- **Coordinates.** Every SD-SP lottery is an affine combination of the rules "best of S", with unique coefficients c_S, and it is a mixture of deterministic SP rules exactly when every c_S is non-negative. *(Proved for three alternatives, Proposition 4. Computed by exact linear programs for four: the 15 rules are affinely independent and the SD-SP lotteries lie in their affine hull.)*
- **The coefficients are degrees.** c_S is the degree of the lottery on the face of the permutohedron where S occupies the bottom block, the other alternatives above it in any fixed order. That face is a sphere of dimension |S| − 2, so the layers are:
  - for |S| = 1, the probability of the bottom alternative;
  - for |S| = 2, the flow when the voter swaps the bottom pair;
  - for |S| = 3, the winding on the bottom hexagon;
  - for |S| = m, the top degree.

  *(Proved, given the affine combination: on such a face, "best of S′" has degree 1 if S′ = S and 0 otherwise, since it is constant when S′ meets the alternatives above, and misses part of the simplex when S′ is a proper subset of S. Computed for three and four alternatives on random vertices.)*
- **Where contextuality sits.** The probabilities are never negative, and strategy-proofness makes the flows non-negative. Contextuality can only appear from dimension 2 up. With three alternatives that is the one degree of Propositions 4 and 5. With four there are two independent layers. The random top two of a block is negative at a hexagon. The neutral lottery with weights (⅔, ⅓, 0, 0) has non-negative hexagons but top degree −⅓. *(Computed.)*
- **Neutral lotteries.** For a neutral lottery, with weights w₁ ≥ … ≥ w_m on the voter's positions, the stack is the table of finite differences of w. The first differences are the flows, the second the hexagon windings, and the last the top degree. The lottery is a mixture of deterministic rules exactly when the whole table is non-negative. This is Hausdorff's complete monotonicity for finite sequences. *(Proved. A neutral mixture of deterministic rules is a mixture of the rules "best of a random j-set", with weights C(m − i, j − 1)/C(m, j), whose differences are all non-negative. By Newton's forward formula the coefficient of each "best of S" with |S| = j is the (j − 1)-th difference of w at the bottom end, which is the degree on the bottom face. So non-negative differences at the bottom end already give a mixture. Computed for three to six alternatives.)*
- **Positional rules.** The rule "the voter's k-th choice" has top degree (−1)^(k−1) C(m − 1, k − 1): 1, −2, 1 for three alternatives and 1, −3, 3, −1 for four. These are the last row of the difference table of a unit weight. The bottom choice has sign (−1)^(m−1), as reversal, the antipodal map, requires. *(Proved for the neutral table; counted on the faces of the permutohedron for four alternatives.)*

By Gibbard's decomposition (Proposition 5), every SD-SP rule for any number of voters is then described by a duple part, which is non-contextual of degree 0, and one stack of degrees per voter. Still open: the affine hull beyond four alternatives, the meaning of the inversion over the lattice of subsets, and any counterpart for rules into rankings (Sections 1–4). *(Interpretation.)* Checks: `scripts/strategy/degree_tower.py`.

## 9. The three placements along loops

*Where the Symmetry Goes* sorts the impossibility theorems by where a leftover symmetry goes: (i) into the output, as a paradox; (ii) into the rule, as a dictator or tie-break; (iii) into a lottery, a fixed point. Its isotropy lemma gives the pointwise form, and the end of its Section 7 already reads (ii) and (iii) as the integer and the real solutions of N·d = 1. Added here, for three alternatives: that neutrality and reversal put no condition on the degrees, so that anonymity is the whole of the constraint, and that (i) is the third way out of the same equation.

**How the symmetries act.**
- **Permuting the alternatives.** On the hexagon of rankings and on the triangle of outcomes alike, a 3-cycle of a, b, c is a rotation and a transposition is a reflection. The two signs always agree. So for a neutral rule, F∘π = π∘F, both sides of the degree change sign together, and neutrality puts no condition on the degrees.
- **Reversal.** Reversal of all ballots is the half rotation of the hexagon. It keeps the orientation, so a rule into rankings that commutes with reversal is not restricted either. For rules into single outcomes reversal does not act on the outcome.
- **Permuting the voters.** This permutes the degree vector, and anonymity makes all degrees equal.

*(Proved; the signs are checked by enumeration.)*

**Proposition 6.** For three alternatives, the only one of anonymity, neutrality and (for rules into rankings) reversal symmetry that constrains the degrees of an IIA rule into rankings, or of an SP rule into outcomes, is anonymity. With unanimity it requires n · d = 1, which has no integer solution for n ≥ 2. *(Proved, from Sections 2, 4 and 7.)*

The three placements are the three ways out of this equation.
- **(ii) Leave the diagonal.** Drop anonymity and keep integer degrees. The solution is a unit vector, one voter with degree 1: Arrow's and Gibbard–Satterthwaite's dictator.
- **(iii) Leave the integers.** Allow lotteries. With full independence, or with SD-strategy-proofness, the degrees become real and keep their meaning (Propositions 2 and 5), and d = 1/n is random dictatorship.
- **(i) Leave the circle.** Change the outcome space so that the voter's loop has nothing to wind around. Pairwise majority is anonymous, neutral, unanimous and IIA, but its outcomes include the two Condorcet cycles. In *Cycles and Twists* these are the caps that close the band of rankings into a sphere, on which the loop contracts. Outcomes with ties do the same: the weak orders fill the hexagon, with total indifference at its centre. For choice functions, outcomes that are sets fill the triangle. In each case the degree is not defined, and the symmetry shows up as a cycle or a tie in the output.

*(Interpretation of Proposition 6, with the facts about the outcome spaces proved.)*

The pointwise and the global layer are two parts of one equivariant problem.
- **The pointwise layer** is the isotropy lemma: an equivariant rule sends each fixed profile to a fixed output. At the Condorcet profile the 3-cycle rotates the hexagon without a fixed point, so neutrality and anonymity together already fail, for numbers of voters divisible by three.
- **The global layer** is the degree: anonymity, unanimity and locality fail together for every n ≥ 2, without neutrality.
- **How the placements resolve each layer.** A lottery resolves both: the centre of the simplex is fixed, and real degrees allow 1/n. A dictator resolves both by breaking the symmetry. A paradox resolves both by enlarging the outcome space.

An equivariant obstruction theory in the usual sense places the isotropy condition at the fixed-point sets and the degree as the next obstruction class. For three alternatives this is worked out in the working note *Equivariant Obstructions*: the degree is the last obstruction, a torsion class of order n (of order g, the gcd of the orbit sizes, for partial anonymity), and two layers outside homotopy theory follow, positivity and rigidity.

**More alternatives.** On the triples, Proposition 6 applies to each triple separately. On the whole sphere of rankings the same holds:
- **Alternatives.** A permutation π acts on the sum-zero hyperplane of utility vectors with determinant sign(π). This hyperplane carries both the sphere of rankings and the boundary of the simplex of outcomes, so π has degree sign(π) on both.
- **Reversal.** Reversal is the antipodal map, of degree (−1)^(m−1), on rankings as input and as output.

Neutrality and reversal symmetry therefore again put no condition on the top degrees, and anonymity is the whole constraint for every m. *(Proved; the determinants are checked for m ≤ 6.)*

## 10. The electorate direction

*Consistency as an Extension Problem* asks whether the obstruction of Young–Levenglick is an invariant of how the Condorcet regions sit around the cycle region: "the winding again". For three candidates the winding is there:
- **The winding.** In the coordinates of the pairwise margins (m_ab, m_bc, m_ca), the cycle region is the pair of opposite orthants +++ and −−−, two cones with a common axis, the purely cyclic margins.
- **Around the axis.** The six orthants between the cones have the Condorcet winners a, a, c, c, b, b, in this order around the axis. The partial assignment of Condorcet winners winds once around the triangle of candidates, in opposite senses seen from the two cones.
- **Forced meeting place.** Any extension with convex winning regions, which consistency requires, must have a point where all three regions meet, since a loop that winds once cannot bound a disc on which only two regions meet. Such a point lies outside the open Condorcet regions, so in the closure of the cycle region or on a tie.

*(The order of the regions is read off the sign patterns; the meeting point follows from the winding.)*

But the winding is not the obstruction:
- **Borda.** Borda's three winning regions are convex and meet exactly where the Borda scores are equal, which in margin coordinates is the purely cyclic axis. Borda realises the winding consistently, placing the meeting point on the axis of the hole. It pays by not being a Condorcet extension. *(Proved: the Borda scores are differences of margins, equal exactly when the margins are equal.)*
- **The blocking lemma.** This lemma of *A Map of Voting Paradoxes* excludes every point of the cycle region on its own. At a profile p there, any candidate x is beaten by some c, and mixing p with a suitable profile where x is the Condorcet winner passes through a profile where c is. So p cannot go to x, for every x, without looking at any loop.

The obstruction of Young–Levenglick is therefore pointwise. At each point of the hole the relation "beats" is a map of the candidates into themselves without a fixed point: the Lawvere form, at a point. The theorems with a dictator are the opposite case. Every single profile has admissible outcomes, and the obstruction appears only along loops, as a degree. This matches the levels of *Four Levels*: Young–Levenglick read for joint draws is a failure of local consistency (level 1), Arrow's and Gibbard–Satterthwaite's scenarios are symmetry breaking (level 3). The winding of the Condorcet regions around the hole is the direction of the cycle. It is visible in both cases, but only in the second does it carry the obstruction. *(Interpretation.)*

## 11. Relation to the literature

- **Baryshnikov (1993)**: Arrow's theorem by the homology of a nerve. The nerve of the cover of strict orders by the sets "x above y" is a homotopy sphere of dimension m − 2 (Theorem 1). The nerve of profiles has the cohomology of a product of n such spheres up to dimension m − 2 (Propositions 4 and 5). An IIA rule is a simplicial map of the nerves, the diagonal embedding sums the voters' classes (Lemma 3), and a voter's class pairs to 1 with the outcome class for a dictator and to 0 otherwise (Proposition 7). His Theorem 2 abstracts this as "purely separated data" and treats Chichilnisky's theorem in the same frame. He also shows that IIA with Pareto excludes ties at profiles of strict orders (Lemma 1), and suggests that domain restrictions should be those that kill the homology of the complex of orders, which for three alternatives is single-peakedness (Section 7.2). Baryshnikov and Root reprove the computation. They obtain Gibbard–Satterthwaite through Muller–Satterthwaite: a monotone unanimous rule induces a simplicial map, and the pairing of each voter's class with the outcome class is 1 for a dictator and 0 otherwise.
- **Okura (2024)**: the same structure with the relation "sum of the voters' maps on homology equals the diagonal". Lemma 2 is this relation for three alternatives.
- **Rajsbaum and Raventós-Pujol**: an elementary proof by the index lemma on a colored triangulation, with pivotal voters as bivalent paths, and a characterisation of domain restrictions for two voters and three alternatives. **Lara, Rajsbaum and Raventós-Pujol** generalise this.

Sections 1–3, and the deterministic part of Section 7, are therefore not new in substance; Baryshnikov and Root reach Gibbard–Satterthwaite by the same kind of class, through monotonicity. They are a short form of the homological proof, with the hexagon and the triangle as the spaces and the rigidity of Lemmas 3, 4 and 6 in place of the injectivity arguments. None of these papers treats lotteries, real coefficients or reversal (checked for all four; Baryshnikov works with integer coefficients throughout). On the continuous side, symmetry beyond full anonymity is treated by Chichilnisky (1996, the permutations of one block of voters, under a full-range condition on that block) and by Juárez-Anguiano (2024, a group acting on the preferences, with full anonymity); the combination, with elements that permute voters and rename at once, is the subject of *Equivariant Obstructions*, Section 6. Sections 4, 6 and the lottery part of Section 7 are the additions: the real degree, its identification with the weights of Theorems 5 and 5′ and of Gibbard (1977), the coin rule as a rule without a class, negative degrees as the exact measure of contextuality for strategy-proof lotteries (the contextual fraction), and the pivotal path as half of the loop. Sections 8 and 9 are first looks: the stack of degrees for one voter, and the three placements as ways out of n · d = 1. Section 10 answers a question of *Consistency as an Extension Problem* in the negative: the winding is there but is not the obstruction. Section 3a collects standard facts about the permutohedron, the barycentric subdivision of the simplex and the score vectors of tournaments (Landau, Rado) that relate the spaces used here.

## 12. What the global form still needs

- **Strategy-proof lotteries.** Propositions 4 and 5 for more than three alternatives, along the stack of degrees of Section 8. The direct proof that unanimity makes the real degrees non-negative, without Gibbard (1977), is given for three alternatives in *Equivariant Obstructions*, Proposition 4.
- **The equivariant statement.** Section 9 gives the three placements as three ways out of n · d = 1 for three alternatives. For more alternatives the symmetries act with equal signs on both sides, so the conclusion is the same. The obstruction theory with the isotropy condition and the degree as successive obstructions is in *Equivariant Obstructions* for three alternatives, and for the top stage with more. Still open: the lower stages for more alternatives.
- **The electorate direction.** Section 10 finds Young–Levenglick pointwise: the Condorcet regions wind around the cycle region, but every point of it is blocked separately. Still open: the same for the no-show theorem, and for more candidates, where the cycle region has more components.
- Lemmas 1–6 and Propositions 1 and 3 are checked in Lean for any finite set of voters (`lean/GlobalForm.lean`, `lean/GlobalFormSP.lean`). The squares become finite statements about tables of social comparisons, for IIA, and about the permitted moves of the swap lemma, for strategy-proofness. Propositions 2, 4 and 5, on real degrees and lotteries, are not checked there.

## References

- Abramsky, S., Barbosa, R. S. and Mansfield, S. (2017). Contextual fraction as a measure of contextuality. *Physical Review Letters* 119, 050504.
- Barberà, S. and Sonnenschein, H. (1978). Preference aggregation with randomized social orderings. *Journal of Economic Theory* 18, 244–254.
- Baryshnikov, Y. (1993). Unifying impossibility theorems: a topological approach. *Advances in Applied Mathematics* 14, 404–415.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Chichilnisky, G. (1982). The topological equivalence of the Pareto condition and the existence of a dictator. *Journal of Mathematical Economics* 9, 223–233. (Cited through Baryshnikov 1993 and Lauwers 2000.)
- Chichilnisky, G. (1996). Actions of symmetry groups. *Social Choice and Welfare* 13, 357–364.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Juárez-Anguiano, H. (2024). Social choice models and topological dynamics. *Boletín de la Sociedad Matemática Mexicana* 30, article 62.
- Landau, H. G. (1953). On dominance relations and the structure of animal societies: III. The condition for a score structure. *Bulletin of Mathematical Biophysics* 15, 143–148.
- Lara, I., Rajsbaum, S. and Raventós-Pujol, A. (2024). A generalization of Arrow's impossibility theorem through combinatorial topology. arXiv:2402.06024.
- Lauwers, L. (2000). Topological social choice. *Mathematical Social Sciences* 40, 1–39.
- Livson, O., Pritam, S. and Prokopenko, M. (2026). The non-orientable topology of Condorcet's paradox. arXiv:2601.07283.
- Okura, T. (2024). A topological proof of Terao's generalized Arrow's impossibility theorem. arXiv:2408.14263.
- Rado, R. (1952). An inequality. *Journal of the London Mathematical Society* 27, 1–6.†
- Rajsbaum, S. and Raventós-Pujol, A. (2025). A combinatorial topology approach to Arrow's impossibility theorem. *Social Choice and Welfare*. doi:10.1007/s00355-025-01609-7. Conference version in PODC 2022; preprint MPRA Paper 120023.
- Wilson, R. (1972). Social choice theory without the Pareto principle. *Journal of Economic Theory* 5, 478–486.

The reference marked † was cited from memory and has not yet been checked against the original.

- *Four Levels of Obstruction in Social Choice*, *Cycles and Twists* (drafts); *Contextuality and Symmetry*, *Loops of Relations*, *Where the Symmetry Goes*, *Gibbard–Satterthwaite as a Scenario* (working notes), all in this repository.
