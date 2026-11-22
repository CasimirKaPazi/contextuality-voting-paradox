# Cycles and Twists

## The topology of a Condorcet cycle

*Draft, November 2026.*

## Abstract

A Condorcet cycle is often compared with the Liar paradox. We make the comparison precise and mark where it fails. Treated as a local-to-global problem in the sense of sheaf-theoretic contextuality, a cycle has no valid model when alternatives are placed on a bounded line, is consistent on a circle, and is contextual only on an unbounded line. That contextuality is possibilistic: no probabilistic model realises a cycle on the line, because probabilities see the line through a bounded function. On the circle exactly the locally transitive tournaments can be placed, so with four alternatives a candidate beating all members of a cycle is contextual there, now also probabilistically. The obstruction of a cycle is an integer winding number, where the Liar's is a parity. The parity appears when direction is forgotten: on the three-alternative Klein bottle of Livson, Pritam and Prokopenko, orientation reverses exactly at the seam formed by the Condorcet cycle, where the two directions of winding are identified. Their projective plane arises from identifying every strict order with its reverse, not, as their definition states, from identifying only the cycles. Built on all comparisons of n alternatives at once, the same construction gives a projective space of dimension n(n − 1)/2 − 1. Reversal remains a free involution, so the parity persists for every n, but the space is orientable for four and five alternatives. Non-orientability is the form the parity takes when the number of comparisons is odd. The results are elementary. Propositions 1–5, remark (d) and the easy direction of the circle characterisation are checked in the Lean proof assistant, except for the classification of surfaces, which is used to name the surfaces.

## 1. Introduction

It is often suggested that the impossibility theorems of social choice (Arrow, Gibbard–Satterthwaite) belong to the same family as the Liar paradox, Gödel's incompleteness and the halting problem. Livson and Prokopenko formalise a correspondence between Arrow and Gödel in which profiles aggregating to complete Condorcet cycles play the role of Gödel sentences; they show that such cycles are forced whenever Arrow's other conditions hold; and, with Pritam, that the contradiction corresponds to the non-orientability of a surface. Abramsky gives a categorical form of Arrow's theorem and, with Barbosa, Kishida, Lal and Mansfield, a general theory of contextuality in which the Liar cycle appears as a discrete Möbius strip. Penrose described the impossible staircase by a cohomology class with coefficients in the positive reals and a ring of Schröder staircases by one with coefficients mod 2. The comparison made here has that form.

One mismatch stands in the way of the comparison. A Condorcet cycle does not look like the Liar: the Liar flips a truth value, while a cycle climbs an order. This paper shows how the two relate.

- **The obstruction of a Condorcet cycle is a winding number** (Sections 3–4). It is integer-valued and requires an unbounded order. It is not detected by the finite machinery of contextuality.
- **The parity obstruction arises by forgetting direction** (Section 5). Identifying a cycle with its reverse turns the integer into a parity, and this is where non-orientability sits. For more alternatives the parity persists, while orientability depends on whether the number of comparisons is odd.

A second mismatch is that Arrow's theorem concerns finite objects, while incompleteness concerns undecidability. The companion paper *Walls and Strategy* shows that undecidability enters with strategy, not with aggregation. The companion paper *Four Levels of Obstruction in Social Choice* uses the three value spaces of Section 3 as the template for a hierarchy of obstructions.

We distinguish throughout between cited theorems, statements proved here, statements verified by computation, and interpretation.

## 2. Setting

**Alternatives and preferences.** Let X be a finite set of at least three alternatives. A *strict preference* is a linear order on X. A *tournament* on X assigns to each pair {x, y} one of x ≻ y or y ≻ x. A tournament is *transitive* if it is a linear order; otherwise it contains a 3-cycle. For three alternatives there are eight tournaments: six linear orders and two cycles.

**Profiles and majority.** A profile is a list of strict preferences, one per voter. The *majority tournament* of a profile (with an odd number of voters) puts x ≻ y when more voters rank x above y than the reverse. A profile has a *Condorcet cycle* if its majority tournament is not transitive.

**Local-to-global language.** Following Abramsky and Brandenburger, a *scenario* consists of a set of variables, a set O of possible values, and a family of *contexts*, each a set of variables considered together. A (possibilistic) *model* assigns to each context C a non-empty set S(C) of allowed joint values of the variables in C. The model is *compatible* (no-signalling) if, whenever two contexts share a variable, they allow the same set of values for it. A *global section* is an assignment of values to all variables whose restriction to every context C lies in S(C). A compatible model with no global section is *strongly contextual*.

**Encoding a tournament.** Given a tournament T on X and a value set O with a binary relation "x is placed above y", written x ▷ y, take the alternatives as variables and the pairs {x, y} as contexts. A model *realises T* if, for every pair with x ≻ y in T, S({x, y}) is a non-empty set of value pairs (u, v) with u ▷ v. A global section is then a placement of all alternatives in O that respects T.

Three value spaces are considered:

- the **bounded line**: O totally ordered with u ▷ v iff u > v, where every non-empty subset used has a maximum (in particular, any finite chain);
- the **circle**: O = ℝ/ℤ with u ▷ v iff u − v, reduced to (−½, ½], lies in (0, ½) — "u is less than half a turn ahead of v";
- the **unbounded line**: O = ℝ (or ℤ) with u ▷ v iff u > v.

## 3. The value space decides the nature of the obstruction

Let T contain a directed cycle a₁ ≻ a₂ ≻ … ≻ aₙ ≻ a₁, n ≥ 3. Proposition 1 needs less: a set C of alternatives in which every member is beaten in T by some member.

**Proposition 1 (bounded line).** If every alternative in a non-empty set C is beaten in T by some alternative in C, no compatible model on a bounded line realises T on C.

*Proof.* Suppose one does. For a ∈ C choose a′ ∈ C with a′ ≻ a in T. By compatibility each alternative a in C has a well-defined non-empty set M_a of allowed values. Let m be the maximum of the union of these sets, attained in M_a. In the context {a′, a}, since m ∈ M_a, some allowed pair has a at m, and then a′ is at a value strictly above m, which belongs to M_a′. This contradicts maximality. ∎

For a finite set C the hypothesis is the same as containing a cycle, but the proof never uses that the cycle closes up: only that the map a ↦ a′ exists. The formal proof (`lean/ValueSpaces.lean`) is stated in this form, for any set of alternatives and any finite chain of values.

So on a bounded line the cycle is not "locally fine, globally impossible": the local pieces already fail to agree on their overlaps. Whatever occupies the top must be beaten by something higher.

**Proposition 2 (circle).** On the circle, T restricted to the cycle has a global section.

*Proof.* Place aᵢ at −i/n. Then aᵢ − aᵢ₊₁ = 1/n ∈ (0, ½) for n ≥ 3, including the closing step from aₙ to a₁. ∎

This is the rock–paper–scissors arrangement. On a circle there is nothing paradoxical about a cycle.

**Which tournaments fit on the circle.** A tournament has a placement on the circle exactly when it is *locally transitive*: the alternatives each one beats, and those beating it, are transitively ordered. One direction is immediate. Everything an alternative beats lies within half a turn behind it, and on an open half circle "placed above" is a linear order. The converse is known in another form. A placement is a family of vectors in the plane with x above y when the turn from y to x is positive and less than half, which is the sign of a skew-symmetric matrix of rank 2. Rajkumar, Veerathu and Mir show that the tournaments induced by such matrices are exactly the locally transitive ones (their Theorem 6). Locally transitive tournaments are also the *round* ones of Brouwer, whose alternatives admit a cyclic order in which each beats a block of those immediately behind it. An exhaustive linear-programming check of all round tournaments up to eight alternatives agrees (`scripts/topology/circle_tournaments.py`).

So the circle is the consistent space for a single cycle, not for every tournament. With four alternatives, let d beat each member of a cycle a ≻ b ≻ c ≻ a. The model allowing in each context all pairs of placements less than half a turn apart, in the required direction, is compatible and has no global section. Unlike the model of Proposition 3, it is also the support of a probabilistic model, in which every alternative is placed uniformly and each winner a uniformly random distance of less than half a turn ahead of its loser. The circle is therefore strongly contextual for this tournament in the probabilistic sense as well. Tournaments that need a skew-symmetric matrix of higher rank need correspondingly more room; which value space plays the role of the circle for every tournament is open problem 3.

**Proposition 3 (unbounded line).** On the unbounded line, the model with S({x, y}) = {(u, v) : u > v} for every pair with x ≻ y is compatible and has no global section. It is strongly contextual.

*Proof.* Every alternative is allowed every value in every context containing it, so the model is compatible. A global section would give real numbers with u₁ > u₂ > … > uₙ > u₁. ∎

**Remarks.**

(a) *Finite methods do not see the obstruction.* The cohomological invariants of contextuality, logical Bell inequalities and the completeness theorem for the non-contextual polytope are formulated for finite outcome sets. Barbosa, Douce, Emeriau, Kashefi and Mansfield extend the framework to measurable outcome spaces with probability measures, but by remark (d) no probabilistic model realises a cycle on the line. By Proposition 1, any finite linear value set gives no model at all. Encodings with binary outcomes fare no better: recording for each pair only which alternative wins gives a single global assignment that violates transitivity, which is a constraint violation and not contextuality; recording for each menu which alternatives are chosen makes transitive and cyclic choice patterns alike fail to glue. The Condorcet obstruction becomes contextuality only when transitivity is built into the geometry of an unbounded value space.

(b) *A classical bound.* For three alternatives and any profile, the fractions of voters satisfy p(a ≻ b) + p(b ≻ c) + p(c ≻ a) ≤ 2, since each linear order satisfies at most two of the three statements. This is an instance of Boole's conditions of possible experience (a logical Bell inequality). The profile {abc, bca, cab} attains the bound with 2/3 on each pair. Majority rounds each 2/3 to 1 and so produces the value 3. The profile itself is a consistent global object — a distribution over linear orders. The contradiction is created by deciding each pair separately and deterministically.

(c) *Reading through Lawvere.* Lawvere's theorem implies that self-application into a space is obstructed when the space has a self-map without fixed points. On the unbounded line, "one step up" has none. On a bounded line, "one step up, stopping at the top" always has one. Proposition 1 is that fixed point, and in the general form above its hypothesis is exactly a map a ↦ a′ of the alternatives into themselves without a fixed point. The same hypothesis, "everything is beaten by something", is all that the incompatibility of consistency with the Condorcet principle uses (*Consistency as an Extension Problem*; `lean/Consistency.lean`). *(Interpretation.)*

(d) *The contextuality of Proposition 3 is possibilistic only.* If every alternative in a finite set C is beaten in T by some alternative in C, no family of probability distributions on the unbounded line realises T on C, even if only the marginals of single alternatives are required to agree between contexts.

*Proof.* Let μ_a be the distribution of a's placement and g = arctan, a bounded strictly increasing function. If a′ beats a, the context {a′, a} places a′ above a almost surely, so g(placement of a′) − g(placement of a) is positive almost surely and bounded, and its expectation is positive: ∫g dμ_a′ > ∫g dμ_a. An alternative of C at which ∫g dμ_a is largest is beaten by one with a larger value. ∎

A probability distribution sees the line only through bounded functions, and through g the line is a bounded interval, where Proposition 1 applies. The possibilistic model of Proposition 3 would be the support of a translation-invariant measure, which on the line cannot be normalised. The probabilistic counterpart of Proposition 3 is the circle with a tournament that is not locally transitive (after Proposition 2).

## 4. The winding number

The unbounded line covers the circle: the map ℝ → ℝ/ℤ wraps the line around the circle like a spiral staircase over its ground plan. A placement on the circle *lifts* if it is the image of a placement on the line that realises the same tournament.

Let alternatives a, b, c be placed on the circle so that all three pairs are comparable. For each step of the closed walk a → b → c → a, let d be the difference (current minus next), reduced to (−½, ½). Define

  w = d(a,b) + d(b,c) + d(c,a).

Since the walk closes, w is an integer.

**Proposition 4.** For three alternatives, w = 0 if the realised tournament is transitive, and w = +1 or −1 if it is one of the two cycles. A circle placement lifts to the line if and only if w = 0.

*Proof.* If the tournament is the cycle a ≻ b ≻ c ≻ a, all three differences lie in (0, ½), so w ∈ (0, 3/2) and hence w = 1; the reverse cycle gives −1. If the tournament is transitive, two differences have one sign and the third the other, so w lies strictly between −1 and 1 and hence w = 0. A lift exists exactly when the three lifted steps sum to zero on the line, which is w = 0. ∎

So a ranking exists exactly when a loop that closes on the circle also closes on the staircase. A Condorcet cycle returns one floor higher. The obstruction is an element of the first cohomology of the triangle with integer coefficients.

This is the integer, combinatorial counterpart of a known decomposition. Jiang, Lim, Yao and Ye decompose real-valued pairwise comparison data on a graph orthogonally into a gradient part (a consistent ranking; on complete data, the Borda count), a curl part (cycles on triangles) and a harmonic part (cycles not visible on any triangle). Saari's profile coordinates separate, for three candidates, the components on which all methods agree from the reversal components, which distinguish positional rules, and the Condorcet components, which carry the cycles. The winding number is the sign-level shadow of the curl and harmonic parts: it records whether the cyclic part of the pairwise data dominates on a triangle.

**Comparison with the Liar.** The Liar cycle x₁ = x₂, …, xₙ₋₁ = xₙ, xₙ = ¬x₁ is obstructed in the same way with a different cover: a two-sheeted cover with a half twist. Going around once exchanges true and false; twice restores them. Its obstruction lies in cohomology with coefficients mod 2.

| | Liar cycle | Condorcet cycle |
|---|---|---|
| Going around once | flips the value | climbs one level |
| Obstruction | parity (ℤ/2) | winding number (ℤ) |
| Values needed | two | an unbounded order |
| Fixed-point-free map | negation, of order two | shift, of infinite order |
| Finite contextuality tools | apply | do not apply |

The two are loops of the same kind over different covers. Section 5 shows how one becomes the other.

**Impossible figures.** The pair has a visual precedent. Penrose described the impossible tribar and staircase by a class in the first cohomology of an annulus with coefficients in the multiplicative group of positive reals, the ambiguity of depth, and a ring of Schröder staircases by a class with coefficients mod 2. The staircase that returns to its starting point while climbing at every step is the Condorcet cycle of the table, and the bistable staircase is the Liar. Ghrist and Cooperband treat such figures as torsors and compute their holonomy for several groups, among them ℤ, ℤ/2 and ℤ ⋊ ℤ/2, the group generated by a shift and a reflection; Ghrist and Ghrist continue this for bistable figures. The shift and the reflection are the two operations of this paper: one step around a cycle, and reversal of every preference. Livson, Pritam and Prokopenko mention Penrose's analysis and a hypothesised cohomological obstruction for preference cycles by Ghrist.

**Counting.** Over n alternatives, the triples with non-zero winding are the cyclic triads of Kendall and Babington Smith, whose number is C(n, 3) − Σᵢ C(sᵢ, 2) for the numbers of wins s₁, …, sₙ.

**The point at infinity.** The line is also the circle with one point removed. In that view a cycle must pass through the missing point: one of its steps leaves at +∞ and returns at −∞, and w counts these passages with sign. Choosing where to cut the circle open decides which step of a cycle is broken, and so who wins; in voting this is the power of an agenda or a tie-breaking order. A cut is an absolute frame of reference imposed on the alternatives from outside the profile. *(Interpretation.)*

## 5. Where non-orientability sits

Livson, Pritam and Prokopenko model strict preferences on three alternatives by a simplicial complex: the six vertices are the strict comparisons x ≺ y, and three comparisons span a triangle when a single strict order contains them. The six orders give six triangles forming an annulus. Its two boundary circles are the two Condorcet cycles, the triples of comparisons with winding +1 and −1. They then treat a cycle as one contradictory object, in which every alternative is preferred to itself, and identify it with its reverse. Gluing the two boundary circles along their reference orientations gives a Klein bottle (their Theorem 4); with the cycles realised as faces the result is the real projective plane (their Theorem 5; see the remark on the realised case below). Numbers refer to the published version; in the second arXiv version these are Theorems 3.9 and 3.10, and their Definition 5 is Definition 3.8. Given Arrow's other conditions, they show that non-dictatorship corresponds to non-orientability.

We ask where on this surface orientation is lost.

**Proposition 5.** The annulus is orientable. Of the six ways of identifying its two boundary circles by a bijection of vertices, three yield a torus and three a Klein bottle. Fix an orientation of the annulus. In each Klein bottle gluing, every edge of the seam joins two triangles whose orientations disagree; in each torus gluing, none does.

*Verification.* Exhaustive computation on the six-triangle complex, in Python (`scripts/topology/`) and as a proof by computation in Lean (`lean/Nerve.lean`). ∎

**Corollary.** On the Klein bottle, a closed path of strict orders reverses orientation exactly when it crosses the seam an odd number of times.

The seam is the Condorcet cycle, and it is the place where winding +1 and winding −1 have been declared the same. Reversing every preference sends w to −w; a surface on which a cycle equals its reverse has no consistent distinction between up and down on the staircase of Section 4. What survives of an integer when its sign is forgotten along a loop is its parity. The group generated by one step up and by reversal is the infinite dihedral group ℤ ⋊ ℤ/2, in which a step followed by reversal has order two. In this sense the parity obstruction of the Liar and the non-orientability of the preference surface are the integer obstruction of Section 4 with the direction of winding forgotten.

Two remarks support this reading.

(a) *Transitivity is "not all equal".* Read the three comparisons around the triangle as bits. The six orders are exactly the triples that are not constant; the two cycles are 000 and 111. For n alternatives the same holds on every triple, since a tournament is transitive exactly when it has no 3-cycle. The not-all-equal constraint is invariant under flipping all bits, that is, under reversing all preferences, and the two forbidden triples form one orbit. Identifying a cycle with its reverse is dividing by a symmetry the constraint already has. It is also not a linear constraint mod 2, unlike the equations of a Liar cycle, which is a further reason the standard cohomological tools for contextuality do not transfer directly. A tool that does fit is the index lemma used by Rajsbaum and Raventós-Pujol: recolouring each comparison by its position around the triangle plus its sign, mod 3, makes exactly the two cycles three-coloured, and the lemma, an integer and oriented count, then applies (Section 6).

(b) *The gluing reverses composition.* Reversing each comparison separately (x ≺ y to y ≺ x) is one of the three torus gluings. The Klein bottle arises when reversal also reverses the order in which comparisons are chained, as reversal acts in an opposite category: the chain 1 ≺ 2 ≺ 3 read as (12, 23) is matched with (32, 21). We reconstructed the gluing from the worked example in Livson et al.; it coincides with one of the three Klein bottle gluings.

The statement "non-orientability is winding mod 2" should not be read as an identity of invariants: winding belongs to a single tournament, orientation to a loop of them. The corollary is the correct form.

**The realised case.** Filling both cycles in as faces turns the annulus into a closed surface with six vertices, twelve edges and eight triangles, of Euler characteristic 2: a sphere. Reversing every preference (x ≺ y to y ≺ x) maps this sphere to itself, fixes no vertex, edge or triangle, and reverses orientation. The quotient is therefore a closed non-orientable surface of Euler characteristic 1, the real projective plane. This is the identification used in the proof of Livson, Pritam and Prokopenko's Theorem 5, which identifies antipodal points of the sphere. Their definition states less: it identifies only the subspaces that represent the cycles. Identifying only the two cycle faces, by any of the six bijections, does not give a surface, since each glued edge then lies in three triangles. The coordinate formulas in their appendix do not describe a free involution as printed: equation (A1), q(θ, t) = (−θ, |t|) (equation (6) in the second arXiv version), folds the cylinder onto itself, and the fibres described in the proof, (θ, b) ↔ (−θ, −b), have fixed points. The antipodal identification described in words corresponds to (θ, b) ↦ (θ + π, −b). We read this as a gap in the statement of the construction, not in the result. It is present in the published version.

The two theorems thus use different identifications. Behind the Klein bottle is the gluing of the two boundary circles along their reference orientations; behind the projective plane is the reversal of every preference on the whole sphere. Reversal applied only to the two boundary circles gives a torus.

The facts in this remark and in Proposition 5 are checked combinatorially in `lean/Nerve.lean`. Two steps rest on standard topology outside the formal check: that a coherent orientation of the triangles is the same as orientability, and the classification of surfaces, which names a closed non-orientable surface of Euler characteristic 0 a Klein bottle and one of Euler characteristic 1 a projective plane.

The same reduction is visible in the homology of the surfaces. The annulus has first homology ℤ: one integer hole, around which the winding is counted. Gluing the two Condorcet cycles orientably gives the torus, with first homology ℤ ⊕ ℤ; gluing them along their reference orientations gives the Klein bottle, with ℤ ⊕ ℤ/2, so that one of the two integer classes has become a class of order two. In the realised case, the sphere obtained by filling in both cycles has no first homology, and its quotient by preference reversal, the real projective plane, has first homology ℤ/2: a loop in it is a path from a strict order to its reverse, and only its parity survives. No integer class remains. Unlike the torus, neither the Klein bottle nor the projective plane has a second integral homology class; neither bounds an inside.

**The identification as a choice of viewpoint.** Livson, Pritam and Prokopenko justify identifying the cycles by an argument of the form ex falso quodlibet: in a contradictory cycle every strict preference holds, so a cycle carries no information beyond being a contradiction, and all cycles are one object. This is a decision about what counts as the same, not a fact about any election, and the surfaces record the possible decisions. The annulus keeps the two contradictions apart; the torus identifies each with its reverse comparison by comparison; the Klein bottle identifies them along their reference orientations; the projective plane fills them in and divides everything by reversal. Treating a contradiction as having no direction is what turns the integer winding of the annulus into the parity of the Klein bottle and the projective plane. It is the step from the Condorcet cycle of Section 4 to the Liar, a contradiction read the way logic reads one. *(Interpretation.)*

**Where the twist sits along a profile.** Orientability cannot change along a continuous family of closed surfaces, so a passage from an orientable to a non-orientable picture has to be concentrated somewhere. On the path used in pivotal-voter proofs of Arrow's theorem it is concentrated at the pivotal voter. Let every voter rank r, and let the voters switch to the reverse −r one at a time, each through the three adjacent transpositions that lead half way around the hexagon of strict orders. By unanimity the social ranking goes from r to −r as well.

- A dictatorship keeps r until the dictator switches and then follows the dictator: the whole half turn happens during that one voter's switch. In the quotient by reversal, where r and −r are one point, the half turn closes into a loop, and its lift joins antipodal points of the sphere, so it is the loop that reverses orientation and generates the first homology ℤ/2 of the projective plane.
- A mixture of dictatorships, an empirical model of Arrow's scenario (*Four Levels of Obstruction in Social Choice*, Theorems 5 and 5′), moves continuously instead. The probability of each comparison is the weight of the voters who still hold it. It falls from 1 to 0, and all three comparisons pass ½ during the switch of the same voter, the weighted median of the switching order. There the lottery is, up to that voter's weight, the even mixture of r and −r, which reversal fixes. The space of lotteries is convex and reversal acts on it linearly, so its quotient is contractible: the path runs through the fixed point instead of around the twist.

A dictatorship puts all the weight at one place in the switching order, and there the twist is a jump; a lottery spreads the weight, and its median is where the path crosses the fixed point of reversal. This is the switch "adding values" of *The Switch Between Fixed Point and No Fixed Point*, located on a path. The path has to start from a unanimous profile: from other profiles the three comparisons pass ½ at different voters, as they did in 456 of 500 random profiles with equal weights. *(The facts about the path are elementary and checked in `scripts/topology/pivotal_path.py`; reading the pivotal voter as the place of the twist is interpretation.)*

**More alternatives.** Livson, Pritam and Prokopenko treat larger sets of alternatives triple by triple. By independence of irrelevant alternatives a social welfare function restricts to every triple, and the surfaces are those of three alternatives. The space can also be built on all comparisons at once. For n alternatives, let K_n be the complex whose simplices are the sets of comparisons contained in one strict order, and P_n the complex of all sets of comparisons that contain no comparison together with its reverse. For three alternatives these are the annulus and the sphere of the realised case. Write N = n(n − 1)/2 for the number of pairs.

**Proposition 6.** (a) P_n is the boundary of the N-dimensional cross-polytope, a sphere of dimension N − 1, and reversing every preference is its antipodal map. The quotient by reversal is the real projective space ℝP^(N−1). It is non-orientable exactly when N is odd, that is, when n leaves remainder 2 or 3 on division by 4.

(b) K_n is homotopy equivalent to a sphere of dimension n − 2, by a map under which reversal corresponds to the antipodal map. The quotient of K_n by reversal is homotopy equivalent to ℝP^(n−2).

*Proof.* (a) Give each pair {x, y} a coordinate, with x ≻ y the positive and y ≻ x the negative unit vector. A set of comparisons without a reversed pair is then a set of these vectors containing no vector together with its negative, which is a face of the cross-polytope. Reversal is multiplication by −1. On ℝ^N it preserves orientation exactly when N is even, and ℝP^(N−1) is orientable exactly when the antipodal map of its covering sphere preserves orientation.

(b) Placements u ∈ ℝⁿ of the alternatives, not all equal, taken up to adding a constant and multiplying by a positive number, form a sphere of dimension n − 2. The open sets U_xy = {u : u_x > u_y} cover it. A family of them has a common point exactly when its comparisons lie in one strict order, so the nerve of the cover is K_n. Every non-empty intersection is the trace of an open convex cone and is contractible, so by the nerve theorem the map that gives u the barycentric weights max(u_x − u_y, 0), normalised, on the vertices x ≻ y is a homotopy equivalence onto K_n. Replacing u by −u gives each comparison the weight of its reverse, so the map takes the antipodal map to reversal. Both involutions are free, and an equivariant homotopy equivalence of free actions induces one of the quotients. ∎

The two complexes come from one construction applied to two spaces. P_n is the nerve of the cover of the unit sphere of all pairwise data z ∈ ℝ^N by the open half-spaces z_xy > 0 and z_xy < 0. K_n is the nerve of the restriction of this cover to the gradient flows z_xy = u_x − u_y, a subspace of dimension n − 1. The homotopy type in (b) is due to Björner and Welker, and in a more general form to Hultman; the cover by open half-spaces, for the root system of type A, is described by Ayzenberg, Beketov and Magai. The homology of K_n and of its quotient, over the fields with 2, 3 and 1 000 003 elements, agrees with Proposition 6 for n ≤ 5, and that of P_n for n ≤ 4 (`scripts/topology/comparison_complexes.py`).

For three alternatives Proposition 6 gives a picture of the realised case. The pairwise data of three alternatives fill a space of dimension three. In it, the differences u_a − u_b, u_b − u_c, u_c − u_a of placements fill a plane, the gradient part of Section 4, and the cyclic flow, one unit around the triangle, spans the line orthogonal to the plane. The plane meets the open orthants of the six strict orders. Only the line meets the orthants of the two Condorcet cycles. On the octahedron, the annulus is therefore the band around the circle of rankings, and the two cycle faces are the caps at the poles, where the cyclic flow points one way or the other. Reversal exchanges the caps. Divided by reversal alone, the annulus becomes a Möbius strip, whose core is the circle of rankings with each ranking identified with its reverse (checked by the same script). The two cycle faces become one disc, which closes the Möbius strip into the projective plane.

For more alternatives two invariants separate that coincide for three. The first is the parity. Reversal is free on both complexes for every n, so a path from a strict order to its reverse becomes a loop in the quotient that does not contract; for n ≥ 4 it generates the fundamental group of both quotients, which has order two. This is the parity described above, the class of order two in the homology of the projective plane, and it is present for every number of alternatives. The second is orientability. For four and five alternatives the realised quotients are ℝP⁵ and ℝP⁹, which are orientable; non-orientability returns for six and seven. Reversing every preference reverses each of the N coordinates, and reversing an odd number of coordinates reverses orientation. In terms of characteristic classes, the first Stiefel–Whitney class of ℝP^(N−1) is N times the generator of its first cohomology mod 2: the orientation character is the parity class taken once for every comparison. For three alternatives there are three comparisons, and the two coincide. The non-orientability found by Livson, Pritam and Prokopenko is the form the parity takes for three alternatives, and their treatment of larger sets triple by triple keeps that form.

Two further differences appear at n ≥ 4. First, K_n is then not a manifold, not even in the sense of homology. The link of the set of comparisons in which one alternative beats all others is a copy of K_(n−1). That is a homotopy sphere of dimension n − 3, while a manifold of the dimension of K_n would need a sphere or a ball of dimension (n − 1)(n − 2)/2 − 1 there. For four alternatives these eight sets are exactly where the test fails. So for n ≥ 4 there are no boundary circles to glue, and Proposition 5 has no direct counterpart. The question of orientability of K_n divided by reversal becomes the question whether reversal preserves the orientation of the sphere of rankings, which holds exactly for odd n. For n = 3 this already differs from the surface: reversal turns the circle of rankings by half a turn, preserving its orientation, but flips the annulus across it, which is why the quotient is a Möbius strip. Orientability of a surface is not a property of its homotopy type. Second, the contradictory objects are not only cycles on triples. The minimal sets of comparisons that lie in no strict order are the directed cycles of every length from two to n, a cycle of length two being a comparison with its reverse. The comparisons a ≻ b, b ≻ c, c ≻ d, d ≻ a form one, and none of their three-element subsets does. A complete tournament with a cycle always contains a cycle of length three, which is why the reduction to triples works for social welfare functions, whose values are complete. Adding as simplices all sets that contain such cycles but no reversed pair turns K_n into P_n.

## 6. Relation to other work

*Arrow and Gödel.* Livson and Prokopenko's Self-Reference Systems relate Arrow's theorem to incompleteness through diagonalisation; their sequel shows that total cycles are forced; the paper with Pritam gives the orientability formulation. Sections 4 and 5 add the distinction between integer and parity obstructions and the location of the orientation reversal. Jiang, Lim, Yao and Ye's combinatorial Hodge decomposition and Saari's profile coordinates are the real-valued, established forms of the decomposition behind Section 4. Tanaka relates Arrow's theorem to Brouwer's; Baryshnikov and Chichilnisky give topological proofs and obstructions of a different kind; Baryshnikov and Root (2024) give a topological proof of the Gibbard–Satterthwaite theorem, in which each voter carries one oriented cycle of the profile space and the dictator is the one voter of degree one. Rajsbaum and Raventós-Pujol prove Arrow's theorem with the index lemma, a discrete form of the winding number. Their output complex is the annulus of Section 5 with the two Condorcet cycles left as holes; the integer obstruction of Section 4 appears as a balance of windings over the boundary circles of the profile complex; and their version of the pivotal-voter argument closes a cycle of weak inequalities between pivotal voters, the counterpart of Proposition 1 with ≤ in place of <. They also show that contractibility of the space of profiles is not the reason for the impossibility, that the labels of the complex are essential, and they place Arrow's theorem with the symmetry-breaking tasks of distributed computing rather than with the agreement tasks. Chichilnisky's obstruction, by contrast, concerns the non-existence of a continuous symmetric aggregation; it depends on the number of voters and is distinct from the one here. Candeal and Induráin reduce a special case of it to the fact that a Möbius strip does not retract onto its boundary.

*Complexes of comparisons.* The complex K_n of Section 5 is the complex of acyclic directed graphs on n vertices. Björner and Welker determined its homotopy type, Hultman extended this to acyclic subgraphs of any directed graph, and Ayzenberg, Beketov and Magai describe it as the nerve of the cover of a sphere by open hemispheres. Proposition 6 adds the reversal of all comparisons, which is the antipodal map, and reads the inclusion of K_n in P_n as that of gradient flows in all pairwise data.

*Tournaments and impossible figures.* The characterisation of the tournaments that fit on the circle is due, in two forms, to Brouwer and to Rajkumar, Veerathu and Mir (after Proposition 2). Penrose's cohomology of impossible figures and its development by Ghrist and co-authors are the closest precedent for the comparison of Section 4 (see there).

*Contextuality.* Abramsky and Brandenburger's framework, the cohomological invariants of Abramsky, Mansfield, Barbosa and of Carù, the general theory of disagreement of Abramsky and Carù, and the logical Bell inequalities of Abramsky and Hardy are all formulated for finite outcome sets. Abramsky's categorical account of Arrow's theorem notes a common structure with contextuality without a reduction; Section 3 explains part of the distance. Zeng and Zahn apply the framework to individual choice. Abramsky, Barbosa, Kishida, Lal and Mansfield connect contextuality to Liar cycles and show that all-versus-nothing arguments are cohomological; Kishida recasts contextuality as a semantics of logical paradoxes, which is the natural place to look for a common frame. Barbosa, Douce, Emeriau, Kashefi and Mansfield extend the framework to continuous outcomes; remark (d) of Section 3 shows why the cycle on the line falls outside its probabilistic form.

*Companion papers.* *Walls and Strategy* treats strategic voting: the walls between the regions of profile space on which the winding number is constant, and the computability of best replies. *Four Levels of Obstruction in Social Choice* places the three value spaces of Section 3 in a hierarchy of obstructions, local inconsistency, contextuality, symmetry breaking and consistency, and places Young–Levenglick, the no-show theorem and Arrow's theorem in it.

## 7. Status and open problems

The Lean files and scripts cited are in the repository github.com/CasimirKaPazi/contextuality-voting-paradox, under `lean/` and `scripts/`; paths are given relative to it.

| Statement | Status | Lean |
|---|---|---|
| Propositions 1–4 (value spaces, winding) | proved here, elementary; Proposition 1 in the general form "everything is beaten" | `ValueSpaces.lean`, any length of cycle |
| Circle placements are exactly the locally transitive tournaments | cited (Brouwer; Rajkumar, Veerathu and Mir); easy direction proved here; checked up to eight alternatives | `CircleTournaments.lean`: the easy direction, and the four-alternative example with no placement but a probabilistic model (discretised to seven points) |
| Remark (d): no probabilistic model of a cycle on the line | proved here | `ProbLine.lean`, for any finite set in which every alternative is beaten, with only single-alternative marginals required to agree |
| Proposition 5 and corollary (seam) | proved combinatorially, three alternatives | `Nerve.lean` |
| Realised case (sphere, its quotient by reversal; gluing only the cycle faces gives no surface) | proved combinatorially | `Nerve.lean` |
| Proposition 6 (more alternatives: projective spaces, parity and orientability) | proved here, using the nerve theorem and the homotopy type of Björner and Welker; homology checked for n ≤ 5 (K_n) and n ≤ 4 (P_n); the annulus divided by reversal is a Möbius strip; K_4 is not a homology manifold | — |

The two topological steps outside the formal checks are those named in Section 5: that a coherent orientation of the triangles is orientability, and the classification of surfaces.

**Open problems.**

1. *More alternatives.* Proposition 6 settles the homotopy picture: the parity persists for every n, orientability does not, and the contradictory objects are the directed cycles of every length. What remains open is a counterpart of Proposition 5. For n ≥ 4 the complex K_n is not a manifold and has no boundary circles to glue. For three alternatives the two Condorcet cycles are the two points of the unit sphere of cyclic flows, the line orthogonal to the gradient plane. For n alternatives the cyclic flows, the curl and harmonic parts of Section 4, form a space of dimension N − n + 1. Is there a gluing along its unit sphere that plays the role of the Klein bottle, with orientation reversal located there?
2. *One statement for both loops.* Find a formulation, presumably of Lawvere type, of which the Liar (negation, parity) and the Condorcet cycle (shift, integers) are instances, with reduction mod 2 as a map between them. The repository note *The Switch Between Fixed Point and No Fixed Point* collects the literature on how such switches happen. A first answer is in the note *Loops of Relations*: both are loops whose holonomy lies in a group, of order two for the Liar and of infinite order for the Condorcet cycle, and reduction mod 2 is a homomorphism between them. On finite value sets every contextual loop closes on a finite cover, which is why the infinite-order case needs an unbounded value space.
3. *Room for every tournament.* The circle fits exactly the tournaments of skew-symmetric sign rank 2. Is there, for each rank, a value space with a symmetry playing the role of the circle, so that every tournament is placed consistently in a space of the right dimension?

## References

- Abramsky, S. (2014). Arrow's theorem by arrow theory. arXiv:1401.4585.
- Abramsky, S. (2017). Contextuality: at the borders of paradox. In *Categories for the Working Philosopher*, Oxford University Press. arXiv:2011.04899.
- Abramsky, S. (2020). Classical logic, classical probability, and quantum mechanics. arXiv:2010.13326.
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Abramsky, S. and Carù, G. (2019). Non-locality, contextuality and valuation algebras: a general theory of disagreement. *Phil. Trans. R. Soc. A* 377, 20190036.
- Abramsky, S. and Hardy, L. (2012). Logical Bell inequalities. *Physical Review A* 85, 062114.
- Abramsky, S., Barbosa, R. S., Kishida, K., Lal, R. and Mansfield, S. (2015). Contextuality, cohomology and paradox. CSL 2015, LIPIcs 41, 211–228. arXiv:1502.03097.
- Abramsky, S., Mansfield, S. and Barbosa, R. S. (2012). The cohomology of non-locality and contextuality. QPL 2011, EPTCS 95.
- Arrow, K. J. (1963). *Social Choice and Individual Values*, 2nd ed. Yale University Press.
- Ayzenberg, A., Beketov, M. and Magai, G. (2023). Coverings by open and closed hemispheres. arXiv:2310.02827.
- Barbosa, R. S., Douce, T., Emeriau, P.-E., Kashefi, E. and Mansfield, S. (2022). Continuous-variable nonlocality and contextuality. *Communications in Mathematical Physics*. doi:10.1007/s00220-021-04285-7. arXiv:1905.08267.
- Baryshnikov, Y. (1993). Unifying impossibility theorems: a topological approach. *Advances in Applied Mathematics* 14, 404–415.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Björner, A. and Welker, V. (1999). Complexes of directed graphs. *SIAM Journal on Discrete Mathematics* 12, 413–424.
- Brouwer, A. E. (1980). The enumeration of locally transitive tournaments. Mathematisch Centrum, Amsterdam, Report ZW 138/80.
- Candeal, J. C. and Induráin, E. (1994). The Moebius strip and a social choice paradox. *Economics Letters* 45, 407–412.
- Carù, G. (2017). On the cohomology of contextuality. QPL 2016, EPTCS 236.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Ghrist, L. and Ghrist, R. (2026). Impossible by degrees: cohomology and bistable visual paradox. arXiv:2602.09313.
- Ghrist, R. and Cooperband, Z. (2025). Obstructions to reality: torsors and visual paradox. arXiv:2507.01226.
- Hultman, A. (2004). Directed subgraph complexes. *Electronic Journal of Combinatorics* 11, R75.
- Jiang, X., Lim, L.-H., Yao, Y. and Ye, Y. (2011). Statistical ranking and combinatorial Hodge theory. *Mathematical Programming* 127, 203–244.
- Kendall, M. G. and Babington Smith, B. (1940). On the method of paired comparisons. *Biometrika* 31, 324–345.
- Kishida, K. (2023). Gödel, Escher, Bell: contextual semantics of logical paradoxes. In *Samson Abramsky on Logic and Structure in Computer Science and Beyond*, Springer.
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- Livson, O. and Prokopenko, M. (2025). Arrow's impossibility theorem as a generalisation of Condorcet's paradox. arXiv:2510.09076.
- Livson, O. and Prokopenko, M. (2025). Comparing and contrasting Arrow's impossibility theorem and Gödel's incompleteness theorem. arXiv:2504.06589.
- Livson, O., Pritam, S. and Prokopenko, M. (2026). The non-orientable topology of Condorcet's paradox. *Mathematics* 14, 2127. doi:10.3390/math14122127. arXiv:2601.07283 (first version titled "Condorcet's paradox as non-orientability").
- Penrose, R. (1991). On the cohomology of impossible figures. *Structural Topology* 17, 11–16; reprinted in *Leonardo* 25 (1992), 245–247.
- Rajkumar, A., Veerathu, V. and Mir, A. B. (2021). A theory of tournament representations. arXiv:2110.05188.
- Rajsbaum, S. and Raventós-Pujol, A. (2025). A combinatorial topology approach to Arrow's impossibility theorem. *Social Choice and Welfare*. doi:10.1007/s00355-025-01609-7. Conference version in PODC 2022; preprint MPRA Paper 113858.
- Saari, D. G. (2011). Geometry of voting. In *Handbook of Social Choice and Welfare* II, ch. 27, Elsevier.
- Tanaka, Y. (2006). On the equivalence of the Arrow impossibility theorem and the Brouwer fixed point theorem. *Applied Mathematics and Computation* 172. doi:10.1016/j.amc.2005.02.054.
- Zeng, W. and Zahn, P. (2015). Contextuality and the weak axiom in the theory of choice. arXiv:1512.02668.
- *Walls and Strategy*; *Four Levels of Obstruction in Social Choice* (companion drafts, this repository).
