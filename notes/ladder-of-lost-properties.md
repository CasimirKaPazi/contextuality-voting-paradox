# A Ladder of Lost Properties

*Exploratory note. It records an analogy between the normed division algebras and successive breakdowns in collective choice, and the questions it raises. Part of it is now precise: the dimensions of the algebras appear in the sphere of rankings, and Adams' theorem decides there which continuous rules exist (Section "The dimensions in the sphere of rankings", from* Equivariant Obstructions*, Section 6). The rest is offered as a guide to where structure might be found. Cited facts, proved statements and interpretation are marked.*

## The algebraic ladder

The normed division algebras are the reals (dimension 1), complex numbers (2), quaternions (4) and octonions (8), and by Hurwitz's theorem there are no others. Each step gives up one algebraic property:

- reals → complex numbers: the **ordering** is lost, and rotation appears;
- complex numbers → quaternions: **commutativity** is lost; unit quaternions are the double cover of rotations in three dimensions (spinors);
- quaternions → octonions: **associativity** is lost; the symmetry of Spin(8) acquires **triality**, an outer symmetry permuting three eight-dimensional representations, none of them privileged;
- beyond the octonions (sedenions): **division** is lost; there are non-zero elements whose product is zero.

The same four cases appear as the Hopf fibrations and, through Adams' theorem, as the only spheres that are parallelisable or carry a continuous multiplication with a two-sided unit: S⁰, S¹, S³ and S⁷, the unit elements of the four algebras.

## Organising picture: holes and the symmetry around them

*Candidate framing, not established.*

Each normed division algebra comes with a Hopf fibration: its unit elements form the fibre, its projective line the base. Real: a two-point fibre over a circle (the double cover). Complex: a circle over the 2-sphere. Quaternionic: a 3-sphere over the 4-sphere. Octonionic: a 7-sphere over the 8-sphere. None of these bundles has a global section. A consistent choice of a point in every fibre is impossible, which is the same form as contextuality and the paradoxes: locally possible, globally obstructed. In this picture the fibre, the unit elements of the algebra, is the symmetry, and the obstruction to a global section is the paradox or hole. Adams' theorem limits such structures to these four.

The first two rungs match the two obstructions of *Cycles and Twists*:

- **Real:** the double cover of the circle. Going around once exchanges the two sheets; the class lies in ℤ/2. This is the shape of the Liar.
- **Complex:** circle bundles over the 2-sphere are classified by an integer, obtained by gluing two discs along the equator with a map of given winding number. The winding number of a Condorcet cycle is of this kind, with the cycle as the equator.

The Hopf fibrations themselves have not appeared as spaces of profiles or of rules. What has appeared is the theorem that limits them, through the unit spheres of the algebras (next section).

## The dimensions in the sphere of rankings

Write a ballot on m alternatives as a utility vector with coordinate sum zero, normalised to length one. These vectors form the unit sphere of a space V of dimension m − 1; a strict ranking is an open chamber of this sphere, and ballots with ties lie on its walls (*The Global Form*, Section 3; *Equivariant Obstructions*, Section 6). So the sphere of rankings has dimension m − 2, and for four numbers of alternatives it is the sphere of unit elements of a normed division algebra:

| Alternatives | Space of ballots V | Sphere of rankings | Unit elements of |
|---|---|---|---|
| 2 | ℝ | S⁰, the two rankings | the reals, the group {±1} |
| 3 | ℝ² | S¹, the hexagon of rankings | the complex numbers |
| 5 | ℝ⁴ | S³ | the quaternions |
| 9 | ℝ⁸ | S⁷ | the octonions |

This answers part of question 4 of the earlier version of this note, why the social choice side did not seem to respect the dimensions 1, 2, 4, 8: they are the dimensions of the space of ballots, at two, three, five and nine alternatives. *(The identification is elementary; its use below is from* Equivariant Obstructions*.)*

For continuous rules, a map F from n copies of the sphere of rankings to the sphere, each voter has a degree, and unanimity makes the degrees sum to 1 (*The Global Form*; *Equivariant Obstructions*, Proposition 1). Whether the sphere carries a multiplication then decides which degree vectors occur:

- **Even m, from four on.** The sphere has even dimension. The square of its generator in cohomology vanishes, and since classes of even degree commute, the square of the pulled-back class is 2 Σ_{i<j} dᵢdⱼ xᵢxⱼ, so all products dᵢdⱼ vanish. A unanimous continuous rule therefore has exactly one voter of degree 1, a homological dictator, without Pareto, neutrality or independence of irrelevant alternatives (*Equivariant Obstructions*, Proposition 5). This is the classical argument that even-dimensional spheres admit no multiplication, read as a statement about rules. *(Proved.)*
- **m = 3, 5, 9.** The sphere carries a multiplication, so products of powers of the ballots, x₁^{d₁} x₂^{d₂} ⋯ xₙ^{dₙ}, give unanimous continuous rules with any integer degree vector summing to 1. Unanimity holds because powers of a single element commute, and on the octonions associate, so x^{d₁} ⋯ x^{dₙ} = x. *(Proved; the octonionic case uses that the octonions are alternative.)*
- **Other odd m (7, 11, …).** The square vanishes for degree reasons, and the sphere carries no multiplication (Adams). Which degree vectors occur there is not settled here.

The cup square is the elementary case of the tool behind the Hopf fibrations: the Hopf invariant of a map S^{2k−1} → S^k is read off a cup square, and Adams' theorem, that Hopf invariant one occurs only for k = 2, 4, 8, is equivalent to the statement that S¹, S³ and S⁷ are the only spheres of positive dimension with a multiplication. So the obstruction that removes the even numbers of alternatives and the theorem that singles out three, five and nine are of the same kind as the one that limits the Hopf fibrations. *(Cited facts; the reading is interpretation.)*

**Scope.** This ladder concerns continuous rules on the space of utilities, the setting of Chichilnisky's theorem. For rules satisfying independence of irrelevant alternatives, Baryshnikov's rigidity makes every voter a homological dictator or irrelevant for every number of alternatives, so the multiplications do not help there (*Equivariant Obstructions*, Section 6).

## The ladder on the side of the voters

At the rungs where a multiplication exists, the property lost at each step appears in how the voters' ballots are combined.

- **ℝ → ℂ, two to three alternatives: ordering.** With two alternatives majority is well behaved (May's theorem). With three, the sphere of rankings becomes a circle and pairwise majority can cycle; the cycle has a winding number (*Cycles and Twists*). This is the first rung of the earlier table below, now attached to a definite number of alternatives.
- **ℂ → ℍ, three to five alternatives: commutativity.** On the circle a product of ballots does not depend on the order of the factors. That is why the map x₃x₄x₅ / (x₁x₂), for blocks of two and three voters, is symmetric within each block and neutral (*Equivariant Obstructions*, Section 6). On the unit quaternions the same expression depends on the order in which the voters are multiplied: it exists, with the same degrees, but it is not symmetric within the blocks. Whether any continuous unanimous map on five alternatives is symmetric under a group of voters without a fixed voter is open (*Equivariant Obstructions*, open question 1). *(The facts about the products are proved; the open question is stated there.)*
- **ℍ → 𝕆, five to nine alternatives: associativity.** On the unit octonions a product of three or more ballots also needs a bracketing, an order in which voters are combined into groups before the groups are combined. Different bracketings give different maps with the same degrees.
- **Beyond nine alternatives: no multiplication.** From then on the sphere of rankings carries no multiplication, as the sedenions carry no division.

*Interpretation.* Read this way, lost commutativity means that a rule built from the algebra needs an order on the voters, an agenda over people rather than over alternatives, and lost associativity means that it needs a tree of sub-electorates, a districting or a hierarchy of delegation. The earlier table placed agenda dependence and grouping dependence on the side of the alternatives; here they would come out of the algebra on the side of the voters. That every symmetric continuous rule at five alternatives must order the voters, or at nine must bracket them, is not proved. It is the conjecture that open question 1 of *Equivariant Obstructions* tests.

## The social choice ladder on the side of the alternatives

The first version of this note matched the sequence of lost properties with breakdowns in collective choice that concern the alternatives. The dimensions do not match there; what matches is the kind of property lost at each step.

| Step | Property lost | Social choice phenomenon | Status of the analogy |
|---|---|---|---|
| 1 | ordering | pairwise majorities need not form a ranking (Condorcet cycles); the obstruction is a winding number, a rotation | precise: see *Cycles and Twists*, and the first rung above |
| 2 | commutativity | **agenda dependence**: under sequential pairwise voting, the order in which comparisons are taken can determine the winner | qualitative; compare the order on voters above |
| 3 | associativity | **grouping dependence**: the majority of district majorities can differ from the overall majority and from the result of another grouping (Ostrogorski's and Anscombe's paradoxes; districting) | qualitative, promising; compare the bracketing of voters above |
| 4 | division | possibly: two non-trivial electorates whose union is exactly balanced, so that each cancels the other | speculative |

Step 3 is the most interesting. Non-associativity of aggregation is the structural core of representation — of delegating, districting, and building assemblies out of sub-assemblies — and so of the sortition and delegation rules developed in this project. If it has a clean topological form, as the Condorcet cycle has in the winding number, that form would bear directly on the design of representative bodies. The octonionic rung of the previous section is a candidate for it.

## Grouping dependence in more detail

An operation is associative if regrouping does not change the result: (x ∗ y) ∗ z = x ∗ (y ∗ z). Counting votes is associative: totals can be formed district by district, in any grouping, and add up to the same number. Majority is a threshold applied to a count, and a threshold applied at an intermediate stage is not. Nine voters, four of whom support A: grouped into districts with 2, 2 and 0 supporters, A carries two of three districts and wins, although it is a minority overall; regrouped as 1, 1 and 2, A carries one district and loses. The result depends on the bracketing, not only on the votes.

The mechanism is the one behind the Condorcet cycle. A cycle appears when a deterministic decision is taken for each pair separately; grouping dependence appears when a deterministic decision is taken for each group separately. In both cases the consistent object is the count, or the distribution of preferences, and the trouble is created by rounding before the end.

Randomisation repairs it in the same way. A lottery that selects a district with probability proportional to its size and then a voter uniformly within it selects every voter with equal probability, whatever the districting. Proportional lotteries compose associatively, by the law of total probability. This bears on sortition and delegation: drawing at random through any hierarchy of groups is equivalent to drawing directly, which no deterministic majority hierarchy achieves.

Two qualifications. First, grouping dependence does not require a cycle: it occurs with two alternatives. The social choice ladder on the side of the alternatives is therefore not a strict sequence in which each step presupposes the previous one, unlike the algebraic ladder. Agenda dependence (step 2), by contrast, arises only where majority has a cycle, since with a Condorcet winner every pairwise agenda selects it. Second, the octonions are not associative but *alternative*: any two elements generate an associative subalgebra (Artin's theorem). A sharper test of the analogy is whether some aggregation rule fails associativity in general while satisfying an analogue of this law, for example being insensitive to regrouping whenever only two distinct kinds of group are involved. On the octonionic rung of the ladder on the side of the voters the law holds literally: a product of ballots from only two distinct voters does not depend on the bracketing.

## Symmetry: S₃ and triality

The symmetries of three alternatives form the group S₃: the cyclic renamings, which rotate a Condorcet cycle, and the reversal, which the Klein bottle construction identifies with the cycle. S₃ is also the outer automorphism group of Spin(8), the group of triality. In the Dynkin diagram D₄, three legs are permuted around a central node, as three alternatives are permuted around the uniform lottery, the only point fixed by the cyclic renaming.

The match is less accidental than a bare coincidence of groups. Following Adams, Baez defines a *normed triality* as a trilinear map t: V₁ × V₂ × V₃ → ℝ with |t(v₁, v₂, v₃)| ≤ ‖v₁‖‖v₂‖‖v₃‖, the bound being attained in every slot and under cyclic permutation of the three spaces. Fixing unit vectors in two of the spaces turns a normed triality into a normed division algebra and conversely, so normed trialities exist exactly in dimensions 1, 2, 4 and 8 (Baez 2002, §2.4). Every normed division algebra is therefore at bottom a cyclically symmetric relation among three things: the multiplication xy = z read as the form t(x, y, z) = ⟨xy, z⟩. Only the octonionic triality has a symmetry permuting all three spaces: the outer automorphism group of Spin(8), the permutation group on three letters.

In the terms of this note: the cyclic part (ℤ/3, the rotation of a Condorcet cycle) is present at every rung as a feature of the definition; the full S₃, including the reversal that the Klein bottle construction identifies, is realised as a symmetry only at the top. A possible common root, offered as interpretation: a binary operation is a ternary relation, and a binary comparison becomes a constraint on triples as soon as it must compose consistently — transitivity is a condition on triangles. Both "threes" would then come from asking binary relations to close up.

**A shift in placement.** By the count of the sphere of rankings, three alternatives sit on the complex rung, not on the octonionic one; the octonionic rung is nine alternatives. So the S₃ of three alternatives and the S₃ of triality are not attached to the same rung. Both observations may stand, since the cyclic symmetry of a normed triality is present at every rung, but they are separate observations and should not be read as one. Whether the full S₃ of triality acts on anything in the problem with nine alternatives is not known.

A test that would make the link substantial: find an aggregation setting in which three *levels*, rather than three alternatives, are permuted by a symmetry that non-associativity breaks — for instance voters, districts and the whole electorate — and in which a fixed central object plays the role of the uniform lottery.

## Questions

1. Is there a topological invariant of grouping dependence? The natural candidate is a measure of how far a two-stage aggregation fails to commute with regrouping, by analogy with the associator of the octonions.
2. Does agenda dependence (step 2) have an exact counterpart of the double cover — a situation in which reversing an agenda twice, but not once, restores the outcome?
3. Is there a setting with an S₃ symmetry among levels of aggregation, as asked above?
4. *Answered in part.* The dimensions 1, 2, 4, 8 are those of the space of ballots at two, three, five and nine alternatives, and Adams' theorem decides there which continuous rules exist. Still open: which degree vectors occur for odd numbers of alternatives other than three, five and nine.
5. At five alternatives, must every continuous unanimous rule that is symmetric under a group of voters without a fixed voter fail to exist, so that lost commutativity forces an order on the voters? At nine, does lost associativity force a bracketing, and do alternative bracketings correspond to districtings?
6. Is there a counterpart of the Hopf fibrations themselves, as spaces of profiles or of rules, rather than only of the theorem that limits them?

## References

- Adams, J. F. (1960). On the non-existence of elements of Hopf invariant one. *Annals of Mathematics* 72, 20–104.
- Anscombe, G. E. M. (1976). On frustration of the majority by fulfilment of the majority's will. *Analysis* 36, 161–168.
- Baez, J. C. (2002). The octonions. *Bulletin of the AMS* 39, 145–205.
- Baryshnikov, Y. (1993). Unifying impossibility theorems: a topological approach. *Advances in Applied Mathematics* 14, 404–415.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Hopf, H. (1931). Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche. *Mathematische Annalen* 104, 637–665.†
- Hurwitz, A. (1898). Über die Composition der quadratischen Formen von beliebig vielen Variablen. *Nachr. Ges. Wiss. Göttingen*, 309–316.
- May, K. O. (1952). A set of independent necessary and sufficient conditions for simple majority decision. *Econometrica* 20, 680–684.
- Ostrogorski, M. (1902). *La démocratie et l'organisation des partis politiques*. Calmann-Lévy.
- Rae, D. W. and Daudt, H. (1976). The Ostrogorski paradox: a peculiarity of compound majority decision. *European Journal of Political Research* 4, 391–398.
