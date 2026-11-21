# A Ladder of Lost Properties

*Exploratory note. It records an analogy between the normed division algebras and successive breakdowns in collective choice, and the questions it raises. Nothing here is established beyond the cited facts; the analogy is offered as a guide to where structure might be found.*

## The algebraic ladder

The normed division algebras are the reals (dimension 1), complex numbers (2), quaternions (4) and octonions (8), and by Hurwitz's theorem there are no others. Each step gives up one algebraic property:

- reals → complex numbers: the **ordering** is lost, and rotation appears;
- complex numbers → quaternions: **commutativity** is lost; unit quaternions are the double cover of rotations in three dimensions (spinors);
- quaternions → octonions: **associativity** is lost; the symmetry of Spin(8) acquires **triality**, an outer symmetry permuting three eight-dimensional representations, none of them privileged;
- beyond the octonions (sedenions): **division** is lost; there are non-zero elements whose product is zero.

The same four cases appear as the Hopf fibrations and, through Adams' theorem, as the only spheres that are parallelisable or carry such fibrations. The note *The Shape of a Distinction* uses this list as an a priori constraint on how a relation can present itself.

## Organising picture: holes and the symmetry around them

*Candidate framing, not established.*

Each normed division algebra comes with a Hopf fibration: its unit elements form the fibre, its projective line the base. Real: a two-point fibre over a circle (the double cover). Complex: a circle over the 2-sphere. Quaternionic: a 3-sphere over the 4-sphere. Octonionic: a 7-sphere over the 8-sphere. None of these bundles has a global section. A consistent choice of a point in every fibre is impossible, which is the same form as contextuality and the paradoxes: locally possible, globally obstructed. In this picture the fibre, the unit elements of the algebra, is the symmetry, and the obstruction to a global section is the paradox or hole. Adams' theorem limits such structures to these four.

The first two rungs match the two obstructions of *Cycles and Twists*:

- **Real:** the double cover of the circle. Going around once exchanges the two sheets; the class lies in ℤ/2. This is the shape of the Liar.
- **Complex:** circle bundles over the 2-sphere are classified by an integer, obtained by gluing two discs along the equator with a map of given winding number. The winding number of a Condorcet cycle is of this kind, with the cycle as the equator.

What lies on the quaternionic and octonionic rungs in collective choice is unknown; the table below proposes candidates.

## The social choice ladder

Collective choice shows a sequence of breakdowns of the same kinds. The dimensions do not match: the space of strict preferences on n alternatives has dimension n − 1. What matches is the kind of property lost at each step.

| Step | Property lost | Social choice phenomenon | Status of the analogy |
|---|---|---|---|
| 1 | ordering | pairwise majorities need not form a ranking (Condorcet cycles); the obstruction is a winding number, a rotation | precise: see *Cycles and Twists* |
| 2 | commutativity | **agenda dependence**: under sequential pairwise voting, the order in which comparisons are taken can determine the winner | qualitative |
| 3 | associativity | **grouping dependence**: the majority of district majorities can differ from the overall majority and from the result of another grouping (Ostrogorski's and Anscombe's paradoxes; districting) | qualitative, promising |
| 4 | division | possibly: two non-trivial electorates whose union is exactly balanced, so that each cancels the other | speculative |

Step 3 is the most interesting. Non-associativity of aggregation is the structural core of representation — of delegating, districting, and building assemblies out of sub-assemblies — and so of the sortition and delegation rules developed in this project. If it has a clean topological form, as the Condorcet cycle has in the winding number, that form would bear directly on the design of representative bodies.

## Grouping dependence in more detail

An operation is associative if regrouping does not change the result: (x ∗ y) ∗ z = x ∗ (y ∗ z). Counting votes is associative: totals can be formed district by district, in any grouping, and add up to the same number. Majority is a threshold applied to a count, and a threshold applied at an intermediate stage is not. Nine voters, four of whom support A: grouped into districts with 2, 2 and 0 supporters, A carries two of three districts and wins, although it is a minority overall; regrouped as 1, 1 and 2, A carries one district and loses. The result depends on the bracketing, not only on the votes.

The mechanism is the one behind the Condorcet cycle. A cycle appears when a deterministic decision is taken for each pair separately; grouping dependence appears when a deterministic decision is taken for each group separately. In both cases the consistent object is the count, or the distribution of preferences, and the trouble is created by rounding before the end.

Randomisation repairs it in the same way. A lottery that selects a district with probability proportional to its size and then a voter uniformly within it selects every voter with equal probability, whatever the districting. Proportional lotteries compose associatively, by the law of total probability. This bears on sortition and delegation: drawing at random through any hierarchy of groups is equivalent to drawing directly, which no deterministic majority hierarchy achieves.

Two qualifications. First, grouping dependence does not require a cycle: it occurs with two alternatives. The social choice ladder is therefore not a strict sequence in which each step presupposes the previous one, unlike the algebraic ladder. Agenda dependence (step 2), by contrast, arises only where majority has a cycle, since with a Condorcet winner every pairwise agenda selects it. Second, the octonions are not associative but *alternative*: any two elements generate an associative subalgebra (Artin's theorem). A sharper test of the analogy is whether some aggregation rule fails associativity in general while satisfying an analogue of this law, for example being insensitive to regrouping whenever only two distinct kinds of group are involved.

## Symmetry: S₃ and triality

The symmetries of three alternatives form the group S₃: the cyclic renamings, which rotate a Condorcet cycle, and the reversal, which the Klein bottle construction identifies with the cycle. S₃ is also the outer automorphism group of Spin(8), the group of triality. In the Dynkin diagram D₄, three legs are permuted around a central node, as three alternatives are permuted around the uniform lottery, the only point fixed by the cyclic renaming.

The match is less accidental than a bare coincidence of groups. Following Adams, Baez defines a *normed triality* as a trilinear map t: V₁ × V₂ × V₃ → ℝ with |t(v₁, v₂, v₃)| ≤ ‖v₁‖‖v₂‖‖v₃‖, the bound being attained in every slot and under cyclic permutation of the three spaces. Fixing unit vectors in two of the spaces turns a normed triality into a normed division algebra and conversely, so normed trialities exist exactly in dimensions 1, 2, 4 and 8 (Baez 2002, §2.4). Every normed division algebra is therefore at bottom a cyclically symmetric relation among three things: the multiplication xy = z read as the form t(x, y, z) = ⟨xy, z⟩. Only the octonionic triality has a symmetry permuting all three spaces: the outer automorphism group of Spin(8), the permutation group on three letters.

In the terms of this note: the cyclic part (ℤ/3, the rotation of a Condorcet cycle) is present at every rung as a feature of the definition; the full S₃, including the reversal that the Klein bottle construction identifies, is realised as a symmetry only at the top. A possible common root, offered as interpretation: a binary operation is a ternary relation, and a binary comparison becomes a constraint on triples as soon as it must compose consistently — transitivity is a condition on triangles. Both "threes" would then come from asking binary relations to close up.

A test that would make the link substantial: find an aggregation setting in which three *levels*, rather than three alternatives, are permuted by a symmetry that non-associativity breaks — for instance voters, districts and the whole electorate — and in which a fixed central object plays the role of the uniform lottery.

## Questions

1. Is there a topological invariant of grouping dependence? The natural candidate is a measure of how far a two-stage aggregation fails to commute with regrouping, by analogy with the associator of the octonions.
2. Does agenda dependence (step 2) have an exact counterpart of the double cover — a situation in which reversing an agenda twice, but not once, restores the outcome?
3. Is there a setting with an S₃ symmetry among levels of aggregation, as asked above?
4. Why does the social choice side not respect the dimensions 1, 2, 4, 8? Either the analogy concerns only the sequence of lost properties, or the dimensions are hidden in a different space (for example the space of lotteries, or of strategies) and have not yet been found.

## References

- Adams, J. F. (1960). On the non-existence of elements of Hopf invariant one. *Annals of Mathematics* 72, 20–104.
- Anscombe, G. E. M. (1976). On frustration of the majority by fulfilment of the majority's will. *Analysis* 36, 161–168.
- Baez, J. C. (2002). The octonions. *Bulletin of the AMS* 39, 145–205.
- Hurwitz, A. (1898). Über die Composition der quadratischen Formen von beliebig vielen Variablen. *Nachr. Ges. Wiss. Göttingen*, 309–316.
- Ostrogorski, M. (1902). *La démocratie et l'organisation des partis politiques*. Calmann-Lévy.
- Rae, D. W. and Daudt, H. (1976). The Ostrogorski paradox: a peculiarity of compound majority decision. *European Journal of Political Research* 4, 391–398.
