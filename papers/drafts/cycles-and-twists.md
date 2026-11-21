# Cycles and Twists

## The topology of a Condorcet cycle

*Draft, November 2026.*

## Abstract

A Condorcet cycle is often compared with the Liar paradox. We make the comparison precise and mark where it fails. Treated as a local-to-global problem in the sense of sheaf-theoretic contextuality, a cycle has no valid model when alternatives are placed on a bounded line, is consistent on a circle, and is contextual only on an unbounded line. That contextuality is possibilistic: no probabilistic model realises a cycle on the line, because probabilities see the line through a bounded function. On the circle exactly the locally transitive tournaments can be placed, so with four alternatives a candidate beating all members of a cycle is contextual there, now also probabilistically. The obstruction of a cycle is an integer winding number, where the Liar's is a parity. The parity appears when direction is forgotten: on the three-alternative Klein bottle of Livson, Pritam and Prokopenko, orientation reverses exactly at the seam formed by the Condorcet cycle, where the two directions of winding are identified. Their projective plane arises from identifying every strict order with its reverse, not, as their definition states, from identifying only the cycles. The results are elementary. Propositions 1–5 are checked in the Lean proof assistant, except for the classification of surfaces, which is used to name the surfaces.

## 1. Introduction

It is often suggested that the impossibility theorems of social choice (Arrow, Gibbard–Satterthwaite) belong to the same family as the Liar paradox, Gödel's incompleteness and the halting problem. Livson and Prokopenko formalise a correspondence between Arrow and Gödel in which profiles aggregating to complete Condorcet cycles play the role of Gödel sentences; they show that such cycles are forced whenever Arrow's other conditions hold; and, with Pritam, that the contradiction corresponds to the non-orientability of a surface. Abramsky gives a categorical form of Arrow's theorem and, with Barbosa, Kishida, Lal and Mansfield, a general theory of contextuality in which the Liar cycle appears as a discrete Möbius strip. Penrose described the impossible staircase by a cohomology class with coefficients in the positive reals and a ring of Schröder staircases by one with coefficients mod 2. The comparison made here has that form.

One mismatch stands in the way of the comparison. A Condorcet cycle does not look like the Liar: the Liar flips a truth value, while a cycle climbs an order. This paper shows how the two relate.

- **The obstruction of a Condorcet cycle is a winding number** (Sections 3–4). It is integer-valued and requires an unbounded order. It is not detected by the finite machinery of contextuality.
- **The parity obstruction arises by forgetting direction** (Section 5). Identifying a cycle with its reverse turns the integer into a parity, and this is where non-orientability sits.

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

## 6. Relation to other work

*Arrow and Gödel.* Livson and Prokopenko's Self-Reference Systems relate Arrow's theorem to incompleteness through diagonalisation; their sequel shows that total cycles are forced; the paper with Pritam gives the orientability formulation. Sections 4 and 5 add the distinction between integer and parity obstructions and the location of the orientation reversal. Jiang, Lim, Yao and Ye's combinatorial Hodge decomposition and Saari's profile coordinates are the real-valued, established forms of the decomposition behind Section 4. Tanaka relates Arrow's theorem to Brouwer's; Baryshnikov and Chichilnisky give topological proofs and obstructions of a different kind; Baryshnikov and Root (2024) give a topological proof of the Gibbard–Satterthwaite theorem, in which each voter carries one oriented cycle of the profile space and the dictator is the one voter of degree one. Rajsbaum and Raventós-Pujol prove Arrow's theorem with the index lemma, a discrete form of the winding number. Their output complex is the annulus of Section 5 with the two Condorcet cycles left as holes; the integer obstruction of Section 4 appears as a balance of windings over the boundary circles of the profile complex; and their version of the pivotal-voter argument closes a cycle of weak inequalities between pivotal voters, the counterpart of Proposition 1 with ≤ in place of <. They also show that contractibility of the space of profiles is not the reason for the impossibility, that the labels of the complex are essential, and they place Arrow's theorem with the symmetry-breaking tasks of distributed computing rather than with the agreement tasks. Chichilnisky's obstruction, by contrast, concerns the non-existence of a continuous symmetric aggregation; it depends on the number of voters and is distinct from the one here. Candeal and Induráin reduce a special case of it to the fact that a Möbius strip does not retract onto its boundary.

*Tournaments and impossible figures.* The characterisation of the tournaments that fit on the circle is due, in two forms, to Brouwer and to Rajkumar, Veerathu and Mir (after Proposition 2). Penrose's cohomology of impossible figures and its development by Ghrist and co-authors are the closest precedent for the comparison of Section 4 (see there).

*Contextuality.* Abramsky and Brandenburger's framework, the cohomological invariants of Abramsky, Mansfield, Barbosa and of Carù, the general theory of disagreement of Abramsky and Carù, and the logical Bell inequalities of Abramsky and Hardy are all formulated for finite outcome sets. Abramsky's categorical account of Arrow's theorem notes a common structure with contextuality without a reduction; Section 3 explains part of the distance. Zeng and Zahn apply the framework to individual choice. Abramsky, Barbosa, Kishida, Lal and Mansfield connect contextuality to Liar cycles and show that all-versus-nothing arguments are cohomological; Kishida recasts contextuality as a semantics of logical paradoxes, which is the natural place to look for a common frame. Barbosa, Douce, Emeriau, Kashefi and Mansfield extend the framework to continuous outcomes; remark (d) of Section 3 shows why the cycle on the line falls outside its probabilistic form.

*Companion papers.* *Walls and Strategy* treats strategic voting: the walls between the regions of profile space on which the winding number is constant, and the computability of best replies. *Four Levels of Obstruction in Social Choice* places the three value spaces of Section 3 in a hierarchy of obstructions, local inconsistency, contextuality, symmetry breaking and consistency, and places Young–Levenglick, the no-show theorem and Arrow's theorem in it.

## 7. Status and open problems

| Statement | Status | Lean |
|---|---|---|
| Propositions 1–4 (value spaces, winding) | proved here, elementary; Proposition 1 in the general form "everything is beaten" | `ValueSpaces.lean`, any length of cycle |
| Circle placements are exactly the locally transitive tournaments | cited (Brouwer; Rajkumar, Veerathu and Mir); easy direction proved here; checked up to eight alternatives | — |
| Remark (d): no probabilistic model of a cycle on the line | proved here | — |
| Proposition 5 and corollary (seam) | proved combinatorially, three alternatives | `Nerve.lean` |
| Realised case (sphere, its quotient by reversal; gluing only the cycle faces gives no surface) | proved combinatorially | `Nerve.lean` |

The two topological steps outside the formal checks are those named in Section 5: that a coherent orientation of the triangles is orientability, and the classification of surfaces.

**Open problems.**

1. *More alternatives.* For n > 3, is orientation reversal on the surfaces of Livson, Pritam and Prokopenko again located exactly at the contradictory objects, and how do cycles on sub-triples enter?
2. *One statement for both loops.* Find a formulation, presumably of Lawvere type, of which the Liar (negation, parity) and the Condorcet cycle (shift, integers) are instances, with reduction mod 2 as a map between them. The repository note *The Switch Between Fixed Point and No Fixed Point* collects the literature on how such switches happen.
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
- Barbosa, R. S., Douce, T., Emeriau, P.-E., Kashefi, E. and Mansfield, S. (2022). Continuous-variable nonlocality and contextuality. *Communications in Mathematical Physics*. doi:10.1007/s00220-021-04285-7. arXiv:1905.08267.
- Baryshnikov, Y. (1993). Unifying impossibility theorems: a topological approach. *Advances in Applied Mathematics* 14, 404–415.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Brouwer, A. E. (1980). The enumeration of locally transitive tournaments. Mathematisch Centrum, Amsterdam, Report ZW 138/80.
- Candeal, J. C. and Induráin, E. (1994). The Moebius strip and a social choice paradox. *Economics Letters* 45, 407–412.
- Carù, G. (2017). On the cohomology of contextuality. QPL 2016, EPTCS 236.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Ghrist, L. and Ghrist, R. (2026). Impossible by degrees: cohomology and bistable visual paradox. arXiv:2602.09313.
- Ghrist, R. and Cooperband, Z. (2025). Obstructions to reality: torsors and visual paradox. arXiv:2507.01226.
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
