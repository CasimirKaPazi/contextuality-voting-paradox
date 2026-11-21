# Roadmap: Impossibility, Self-Reference and Collective Choice

*Status overview of the work in progress, November 2026. It lists the threads that have emerged, the central claim of each, what is already in hand, and what a rigorous treatment would still require. All documents named here are drafts.*

## The overall picture

The impossibility theorems of social choice share a common form with the Liar paradox, incompleteness and the halting problem: local pieces that each make sense fail to fit into a consistent whole, and every attempt to force a fit either produces a contradiction, imposes an arbitrary choice, or introduces chance. In current form (*Contextuality and Symmetry*, Section 3a, and the draft *Four Levels of Obstruction in Social Choice*), the obstructions sort into four levels:
- local inconsistency: no locally consistent model at all, for instance Young–Levenglick read for joint draws of winners;
- contextuality: locally consistent models without a global one;
- symmetry breaking: global solutions exist but none is symmetric, as in Arrow's theorem;
- consistency.

These are the levels of sheaf-theoretic contextuality with symmetry breaking added, and they match the bounded line, unbounded line and circle of *Cycles and Twists*, with one qualification: the unbounded line is contextual only possibilistically, and the probabilistic second level appears on the circle for tournaments that are not locally transitive.

The threads below develop different parts of this picture. Two of them carry the general description; the others are applications, special cases or speculative extensions.

## Core threads

### A. Consistency as non-contextuality (the heart)

**Claim.** Aggregation is a local-to-global problem in the sense of sheaf-theoretic contextuality, with sub-electorates (and, separately, subsets of alternatives) as contexts. The consistency criterion of voting is a gluing condition; demanding it at the level of winners amounts to assuming non-contextuality. Young–Levenglick, Moulin's no-show theorem and Arrow's theorem are then obstructions to gluing of different kinds, and Kemeny's rule is the case in which gluing holds for full sections (rankings) but fails after projection to a winner.

**In hand.** An elementary proof, for vote shares and any number of candidates, that every Condorcet extension fails consistency at every profile without a Condorcet winner: electing any candidate is undone by mixing with a profile in which a candidate that beats it becomes the Condorcet winner. Consistency is convexity of winner regions. The map of paradoxes and its patterns; the Kemeny analysis; the plurality example in which a consistent rule elects a candidate on a profile where every pairwise comparison is tied; the observation that Condorcet cycles become contextual only on an unbounded value space, and there only possibilistically; the Hodge and Saari decompositions as the real-valued structure of pairwise data.

**In hand (joining A and B).** Aggregation written as a constraint network: variables are the social decisions on each pair for each column of voters' bits, contexts are profiles, independence of irrelevant alternatives is non-contextuality of these decisions. Integral solutions are the dictators; symmetric ones do not exist; the symmetric fractional solution is random dictatorship. Agreement-type obstructions (no solution at all: Young–Levenglick, no-show) are distinguished from symmetry-breaking ones (solutions exist, none symmetric: Arrow, Gibbard–Satterthwaite), as in distributed computing; by Kun et al., the symmetry can be kept integrally exactly when the local-consistency relaxation is exact. Empirical models on this scenario, in the sense of Abramsky and Brandenburger, are exactly the mixtures of dictatorships (proved for three alternatives and any number of voters, *Four Levels*, Theorem 5; four alternatives computed for up to three voters): the scenario is non-contextual, with the dictator as hidden variable, and becomes strongly contextual when divided by the voters' permutations. Random rules satisfying only Barberà and Sonnenschein's pairwise independence can go beyond the mixtures from three voters on (the coin rule), but only by signalling across pairs. See *Contextuality and Symmetry*.

**In hand (electorates).** Young–Levenglick written as a scenario with electorates in the contexts: read as a joint draw of winners, no rule that elects every Condorcet winner, deterministic or lottery-valued, is consistent; the obstruction is a failure of local consistency, not contextuality. Maximal lotteries are consistent only ex ante. The no-show theorem splits in the same way: SD-participation, which is participation for joint draws, fails for every Condorcet rule (Brandt, Geist and Peters), while maximal lotteries satisfy participation for independent draws (Brandl, Brandt and Hofbauer). See *Consistency as an Extension Problem*, Section 3b.

**Still required.** A sheaf formulation with sub-electorates as the cover that goes beyond the scenario of triples; a statement of Young–Levenglick as an obstruction in that formulation, ideally cohomological; the relation between the electorate-indexed and the alternative-indexed versions (consistency versus IIA), of which *Contextuality and Symmetry* gives a first reading (locality in the direction of alternatives, gluing in the direction of voters).

**Documents.** *Consistency as an Extension Problem* (the current formulation: consistency as convexity in vote-share space, the Condorcet winner as a partial assignment whose consistent extension across the cycle region is impossible, and a table of which combinations of symmetry, gluing and cycle sensitivity are possible, with maximal lotteries as the unique rule achieving all three); *A Map of Voting Paradoxes*; *Two Kinds of Loop*; Sections 3–4 of *Cycles and Twists*.

### B. Where the symmetry goes (the question that follows)

**Claim.** Aggregation into a rigid total order must dispose of a fixed-point-free symmetry of the profile. The symmetry ends up in the output (a paradox), in the rule (a dictator, tie-breaker or agenda), or in a fixed point that is not a single alternative (a lottery). Incompatible combinations of criteria are different decisions about where it goes.

**In hand.** The elementary observation at the Condorcet profile; the three placements and their mathematical backing (rigidity of finite orders, Lawvere, Brouwer, Kakutani, Scott); a classification of known theorems by placement (see the table in *Where the Symmetry Goes*); the recursion for voters who are themselves composed. The pointwise form of the trichotomy: by the isotropy lemma, a neutral rule must send each profile to an output fixed by its stabiliser, and the three placements are the cases "an admissible fixed output exists", "only an inadmissible one exists", "none exists". This recovers, by computation on small cases, the known existence conditions for anonymous and neutral rules (Moulin; Bubboloni and Gori).

**Still required.** The global form: the theorems with a dictator (Arrow, Gibbard–Satterthwaite, Chichilnisky) are obstructions along loops, not at points. An equivariant obstruction theory for rules with a locality condition, with the winding and the degrees as classes, and integer versus real classes separating a forced break from a fixed point.

**Documents.** *Where the Symmetry Goes*; *Contextuality and Symmetry*; Section 4 of *Walls and Strategy*; the draft *Four Levels of Obstruction in Social Choice*.

## Further threads

### C. Cycles and twists

The integer winding obstruction of Condorcet cycles versus the parity obstruction of the Liar; the location of non-orientability at the seam of the Klein bottle; the realised case as the sphere divided by preference reversal. Propositions 1–5 are checked in Lean. Still required: extension to more than three alternatives, one statement covering both loops and the diagonal of thread D (a loop of contexts with an edge map per context, and three cases: no fixed point, fixed points of the square only, a fixed point), review by a reader from topology or social choice. A first form of the common statement is in *Loops of Relations*: sections of a loop are fixed points of its monodromy; with group-valued edges the Liar has holonomy of order two and the Condorcet cycle of infinite order, related by reduction mod 2; on finite value sets every contextual loop closes on a finite cover; the strategic diagonal is the case of an edge chosen by an adversary, where the obstruction is the absence of universal fixed points (dominant or strict Nash strategies), not of existential ones. *Documents: Cycles and Twists; The Switch Between Fixed Point and No Fixed Point (literature for the common statement: acyclicity, odd and even loops through negation, alternating fixpoints, partiality); Loops of Relations.*

### D. Strategy as a halting problem

Walls in profile space; the dichotomy between dictatorship and non-computable best replies (Gibbard 1973 with a diagonal lemma, Theorem 3, checked in Lean from Gibbard's definitions), its lottery version (Gibbard 1978, Theorem 6, in Lean with Gibbard's Corollary 2 assumed), the rational-opponent diagonal (verified on small cases, with Lean certificates for four rules), and the boundary set by sequential moves with visible votes. The diagonal lemma is in substance Canning (1992), Theorem 3, and the rational diagonal is the absence of a strict Nash strategy in the sense of his Theorem 5. For two players, every form that is not tight admits a rational diagonal (Proposition 5, in Lean), so the open case is the tight forms. Still required: a proof for tight forms, the case of randomised strategists, and the case of sequential voting in random order with private preferences. *Document: Walls and Strategy.*

### E. A ladder of lost properties

The normed division algebras and the Hopf fibrations as a frame for successive breakdowns: ordering (cycles), commutativity (agenda dependence), associativity (grouping dependence); triality and the symmetric group on three alternatives. Speculative, except for one elementary fact of independent use: proportional lotteries compose consistently across any grouping, which no deterministic majority hierarchy does. *Document: A Ladder of Lost Properties.*

### F. Applied: rules weighted by measured inconsistency

A voting rule combining a gradient signal (score differences) with pairwise margins, weighted by the measured local inconsistency of the pairwise data (curl on triangles). To be tested by simulation; independent of the theoretical threads.

### G. Positioning consensus with a random fallback

Theorem 6 of *Walls and Strategy* gives a formal frame: the random fallback avoids the strategic regress at the cost of ex ante efficiency; deliberation recovers efficiency and carries the regress. This positions the CORE mechanism relative to Gibbard's theorems and to the proportional consensus of Heitzig, Simmons and Constantino.

## Suggested order

1. Formal checks of the newer results, after the current work on tight game forms: Theorem 5 of *Four Levels*, Propositions 1–3 of *Loops of Relations*, remark (d) of *Cycles and Twists* and the easy direction of its circle characterisation. All are short and use only finite sets and elementary probability.
2. Theorem 5 for four or more alternatives: whether full compatibility forces the joint lottery once every triple is a mixture of dictatorships. Computed for four alternatives and up to three voters; a proof needs to explain how the joint lottery of two disjoint pairs is forced. Five alternatives exceed the memory of the computation.
3. Bring C to submission. D follows once the tight forms move.
4. Thread A: one scenario with electorates as contexts, in which consistency and participation are both constraints, as a step towards the sheaf formulation with sub-electorates as the cover.
5. G (the bridge to CORE), then E and F.

Thread B runs alongside, as questions from the other threads land there (holonomy sets, the equivariant obstruction theory).

## Related project documents

*The Shape of a Distinction* (minimal-relational-structure-4.md) places the social choice results in the wider framework of perspectives, boundaries and self-reference.
