# Roadmap: Impossibility, Self-Reference and Collective Choice

*Status overview of the work in progress, November 2026. It lists the threads that have emerged, the central claim of each, what is already in hand, and what a rigorous treatment would still require. All documents named here are drafts.*

## The overall picture

The impossibility theorems of social choice share a common form with the Liar paradox, incompleteness and the halting problem: local pieces that each make sense fail to fit into a consistent whole, and every attempt to force a fit either produces a contradiction, imposes an arbitrary choice, or introduces chance. The threads below develop different parts of this picture. Two of them carry the general description; the others are applications, special cases or speculative extensions.

## Core threads

### A. Consistency as non-contextuality (the heart)

**Claim.** Aggregation is a local-to-global problem in the sense of sheaf-theoretic contextuality, with sub-electorates (and, separately, subsets of alternatives) as contexts. The consistency criterion of voting is a gluing condition; demanding it at the level of winners amounts to assuming non-contextuality. Young–Levenglick, Moulin's no-show theorem and Arrow's theorem are then obstructions to gluing of different kinds, and Kemeny's rule is the case in which gluing holds for full sections (rankings) but fails after projection to a winner.

**In hand.** An elementary proof, for vote shares and any number of candidates, that every Condorcet extension fails consistency at every profile without a Condorcet winner: electing any candidate is undone by mixing with a profile in which a candidate that beats it becomes the Condorcet winner. Consistency is convexity of winner regions. The map of paradoxes and its patterns; the Kemeny analysis; the plurality example in which a consistent rule elects a candidate on a profile where every pairwise comparison is tied; the observation that Condorcet cycles become contextual only on an unbounded value space; the Hodge and Saari decompositions as the real-valued structure of pairwise data.

**In hand (joining A and B).** Aggregation written as a constraint network: variables are the social decisions on each pair for each column of voters' bits, contexts are profiles, independence of irrelevant alternatives is non-contextuality of these decisions. Integral solutions are the dictators; symmetric ones do not exist; the symmetric fractional solution is random dictatorship. Agreement-type obstructions (no solution at all: Young–Levenglick, no-show) are distinguished from symmetry-breaking ones (solutions exist, none symmetric: Arrow, Gibbard–Satterthwaite), as in distributed computing; by Kun et al., the symmetry can be kept integrally exactly when the local-consistency relaxation is exact. Random rules with probabilistic independence are empirical models in the sense of Abramsky and Brandenburger; the non-contextual ones are the mixtures of dictatorships, and from three voters on there are contextual ones (the coin rule), matching the gap between subadditive and additive power in Barberà and Sonnenschein. See *Contextuality and Symmetry*.

**In hand (electorates).** Young–Levenglick written as a scenario with electorates in the contexts: read as a joint draw of winners, no rule that elects every Condorcet winner, deterministic or lottery-valued, is consistent; the obstruction is a failure of local consistency, not contextuality. Maximal lotteries are consistent only ex ante. See *Consistency as an Extension Problem*, Section 3b.

**Still required.** A sheaf formulation with sub-electorates as the cover that goes beyond the scenario of triples; a statement of Young–Levenglick as an obstruction in that formulation, ideally cohomological; the relation between the electorate-indexed and the alternative-indexed versions (consistency versus IIA), of which *Contextuality and Symmetry* gives a first reading (locality in the direction of alternatives, gluing in the direction of voters).

**Documents.** *Consistency as an Extension Problem* (the current formulation: consistency as convexity in vote-share space, the Condorcet winner as a partial assignment whose consistent extension across the cycle region is impossible, and a table of which combinations of symmetry, gluing and cycle sensitivity are possible, with maximal lotteries as the unique rule achieving all three); *A Map of Voting Paradoxes*; *Two Kinds of Loop*; Sections 3–4 of *Cycles, Twists and Walls*.

### B. Where the symmetry goes (the question that follows)

**Claim.** Aggregation into a rigid total order must dispose of a fixed-point-free symmetry of the profile. The symmetry ends up in the output (a paradox), in the rule (a dictator, tie-breaker or agenda), or in a fixed point that is not a single alternative (a lottery). Incompatible combinations of criteria are different decisions about where it goes.

**In hand.** The elementary observation at the Condorcet profile; the three placements and their mathematical backing (rigidity of finite orders, Lawvere, Brouwer, Kakutani, Scott); a classification of known theorems by placement (see the table in *Where the Symmetry Goes*); the recursion for voters who are themselves composed. The pointwise form of the trichotomy: by the isotropy lemma, a neutral rule must send each profile to an output fixed by its stabiliser, and the three placements are the cases "an admissible fixed output exists", "only an inadmissible one exists", "none exists". This recovers, by computation on small cases, the known existence conditions for anonymous and neutral rules (Moulin; Bubboloni and Gori).

**Still required.** The global form: the theorems with a dictator (Arrow, Gibbard–Satterthwaite, Chichilnisky) are obstructions along loops, not at points. An equivariant obstruction theory for rules with a locality condition, with the winding and the degrees as classes, and integer versus real classes separating a forced break from a fixed point.

**Documents.** *Where the Symmetry Goes*; *Contextuality and Symmetry*; Section 8 of *Cycles, Twists and Walls*.

## Further threads

### C. Cycles, twists and walls

The integer winding obstruction of Condorcet cycles versus the parity obstruction of the Liar; the location of non-orientability at the seam of the Klein bottle; walls in profile space; the dichotomy between dictatorship and non-computable best replies (Gibbard 1973 with a diagonal lemma), and its lottery version (Gibbard 1978). The most complete draft. Still required: reference check, extension to more than three alternatives, review by a reader from social choice. *Document: Cycles, Twists and Walls.*

### D. Strategy as a halting problem

Could be separated from C as a game-theory and computability paper: Theorems 8 and 10, the rational-opponent diagonal (verified on small cases), and the boundary set by sequential moves with visible votes. Still required: a general proof of the rational-opponent version, the case of randomised strategists, and the case of sequential voting in random order with private preferences.

### E. A ladder of lost properties

The normed division algebras and the Hopf fibrations as a frame for successive breakdowns: ordering (cycles), commutativity (agenda dependence), associativity (grouping dependence); triality and the symmetric group on three alternatives. Speculative, except for one elementary fact of independent use: proportional lotteries compose consistently across any grouping, which no deterministic majority hierarchy does. *Document: A Ladder of Lost Properties.*

### F. Applied: rules weighted by measured inconsistency

A voting rule combining a gradient signal (score differences) with pairwise margins, weighted by the measured local inconsistency of the pairwise data (curl on triangles). To be tested by simulation; independent of the theoretical threads.

### G. Positioning consensus with a random fallback

Theorem 10 of C gives a formal frame: the random fallback avoids the strategic regress at the cost of ex ante efficiency; deliberation recovers efficiency and carries the regress. This positions the CORE mechanism relative to Gibbard's theorems and to the proportional consensus of Heitzig, Simmons and Constantino.

## Suggested order

1. Sharpen A conceptually: the sheaf formulation with sub-electorates as contexts.
2. Ask B on top of A: where does the symmetry go when gluing fails?
3. Bring C and D to a reviewable state, as they are the most complete.
4. E, F and G as time allows.

## Related project documents

*The Shape of a Distinction* (minimal-relational-structure-4.md) places the social choice results in the wider framework of perspectives, boundaries and self-reference.
