# Towards a Mathematics of Alignment: Roadmap

*Working note. It states which part of the alignment question this repository can make precise, what is already in hand, and which threads of theory and formalisation are realistic next steps. It refers to the other notes for every result and adds none of its own. The essays that first set out the picture (Hiveism 2025a, 2025b) were written to point in a direction, not as claims for a paper; where the formal work has since corrected them, Section 5 says so.*

## 1. The question, and what the social-choice side can say about it

Alignment is usually posed as the choice of a goal: which goal should an agent be given so that it stays aligned with us. The view taken here is that no such goal can be conclusively defined. Alignment is the ongoing relation between many goals, each valid in its own context: where they work together they are aligned, where they conflict they are not. The reason is not that there is nothing to agree on, but that every agreement is local to those who reach it, and local agreements need not combine into one.

This has the form of a local-to-global problem, and social choice is the part of mathematics in which it can be stated exactly. Perspectives become participants, goals become their preferences or ballots, a shared goal becomes an aggregation rule, and a local agreement becomes an agreement within a group. In this language the repository can say three kinds of thing:

1. **Negative statements**: no rule that combines given perspectives into one outcome satisfies given conditions, and which way it fails (Section 3, the four levels).
2. **Constructive statements**: mechanisms that place the unavoidable obstruction where it does least harm, in a fair lottery or in a process without fixed end, with guarantees that hold regardless of what the participants want.
3. **Statements about scale and time**: how agreements behave when groups are joined, extended or nested, and when the process runs on.

A mathematics of alignment in this sense is not a theorem that states the right goal. It consists of theorems of the first two kinds, and success means that both are sharp: the negative ones say exactly what cannot be had, the constructive ones exactly what can.

## 2. What lies outside this repository

Three parts of the wider picture are not questions of social choice, and the work here will not close them on its own. They are recorded as gaps.

**From goals to mechanisms.** Every statement below concerns rules or procedures over reported perspectives. That a goal shared by everyone would have to take this form, so that the theorems about mechanisms apply to it, is a claim about what goals and perspectives are. It belongs to the physics and philosophy of mind behind the project and is assumed here, not derived.

**The inverse attractor.** The essays describe alignment as an attractor, and also as an inverse or anti-attractor: not a point to approach but the letting go of any fixed goal, so that what is approached is the open space between attractors. This is meant as a pointer, not as a dynamical claim, and it has no formal counterpart here. At most a dynamic or evolutionary argument might show that what holds on to nothing is the most stable over time. The formal results bear on it only indirectly. Incompleteness, undefinability and undecidability recur throughout them, and an orientation towards what cannot be defined or reached cannot itself become a fixed goal. Whether this can be made precise is left open.

**Grounding and application.** That value is grounded in experience, how the mechanisms would be used by or among AI systems, and whether a network of agents acting this way prevails over others are matters for other work. They are mentioned only as context.

## 3. What is in hand

*Pointers only; each result is stated, with its status, in the note named.*

- **Undefinability for mechanisms.** Every game form with at least three outcomes is dictatorial or has a participant at some preference for whom no program always computes a best reply (*Walls and Strategy*, Theorem 3, from Gibbard 1973 and a diagonal lemma, checked in Lean). With lotteries as outcomes, a non-dictatorial procedure either keeps this barrier or is straightforward and inefficient ex ante (Theorem 6, from Gibbard 1978). Any fixed definition of a shared goal as a rule over reports is therefore either a dictatorship or open to exploitation by someone.
- **Four levels of obstruction** (*Four Levels of Obstruction*; *Contextuality and Symmetry*, Section 3a): no locally consistent model; local models without a global one (contextuality); global solutions none of which is symmetric; a symmetric global solution. Agreement-type conflicts, such as Young–Levenglick read for joint draws, fail at the first level for every rule, fair or not. Symmetry-breaking conflicts, such as Arrow and Gibbard–Satterthwaite, have coherent solutions that each privilege someone, and drop to the second level when the participants can no longer be named (*Contextuality and Symmetry*, Section 2b). The level depends on scale: the electorate scenario for three alternatives passes through all four as the electorate grows (*Consistency as an Extension Problem*, Section 3d).
- **Where the symmetry goes.** An unavoidable symmetry ends up in the output, in the rule or in a lottery, at a single profile by the isotropy lemma and along loops as a degree (*Where the Symmetry Goes*; *The Global Form*; *Equivariant Obstructions*).
- **The fair fallback.** Uniform random ballot is singled out by strategy-proofness with unanimity (Gibbard 1977) and by full independence with unanimity and anonymity (*Four Levels*, Theorems 5 and 5′); electorate conditions alone do not single it out (*CORE and the Formal Results*, Section 2).
- **Proportionality.** Mixtures of dictatorships have additive power, and full compatibility forces additivity; the coin rule shows that pairwise independence alone allows subadditive power, through signalling (*Contextuality and Symmetry*, Section 2a). Proportional lotteries compose associatively across any grouping, which no deterministic majority hierarchy does (*A Ladder of Lost Properties*).
- **CORE's guarantees.** The draw is a martingale, which yields the fair-call results; against individually rational groups a participant's guarantee is a linear program between the paper's floor and the endowment, equal to the endowment on a line with losses proportional to distance; under strictly concave loss on a line no group has anything to agree on (*CORE and the Formal Results*, Sections 3 to 3b; checked in Lean in part). CORE's place relative to Gibbard: the fallback is the straightforward part, deliberation carries the barrier, and the theorems bound every formalisation of deliberation as a finite game form, not open deliberation itself (ibid., Section 4).
- **Measures.** For strategy-proof lotteries with three alternatives, negative degrees measure contextuality exactly: the contextual fraction is twice their sum (*The Global Form*, Proposition 5).

## 4. Threads

The threads are theory building and formalisation that can be done here. Each names its question, what exists, and a first step.

### T1. Undefinability as one statement

*Question.* State, in the language of alignment, what Theorems 3 and 6 of *Walls and Strategy* say: a shared goal defined as a rule over reported perspectives is either a dictatorship, or exploitable in a sense with no computable defence, or inefficient by construction. Make every hypothesis explicit, including what counts as a rule and what is left outside (open deliberation, perspectives that change).

*Exists.* Both theorems, checked in Lean or with one assumption from Gibbard.

*First step.* A short section, in a note or in the follow-up to the CORE paper, with the statement and its limits. Check whether the reading as an undefinability theorem, in the sense of Tarski rather than of Gödel, has a precedent in the literature on social choice and computability.

### T2. A classification of conflicts

*Question.* Sort conflicts between goals by level and by the exits each level admits, so that "these two goals conflict" can be refined to "they conflict in this way, and this is what can be given up".

*Exists.* The four levels, their exits (*Four Levels*, Section 6), the division from level 3 to level 2, the electorate thresholds.

*First steps.*
- A table of known incompatibilities placed by level and exit, extending the placements in *Where the Symmetry Goes*, Section 6, and *Four Levels*, Section 3a.
- Is every contextual (level-2) scenario in social choice the division of a symmetry-breaking one by its symmetry, or are there level-2 obstructions of another origin? The electorate scenario at eight voters is the test case.
- *Resolution.* Merging participants into composite participants changes the level. The strata of *Equivariant Obstructions*, where two voters become one composite voter, are a first formal instance. State how levels behave under merging and under dividing by a symmetry.

### T3. The paradox placed in time

*Question.* A voting rule halts by construction, and the barrier of T1 then appears as strategy. A procedure without a fixed end can carry the barrier in its course instead, with a definite state at every moment. Make this a third option beside "dictatorship" and "inefficient lottery".

*Exists.* The martingale of the CORE draw, which gives every intermediate state an expected outcome; the call structure solved by backward induction under complete information, and its split under private information (*CORE and the Formal Results*, Sections 3, 3g, 3h); sections of a contextual loop on a cover, where the Liar becomes an alternation in time (*Loops of Relations*).

*First steps.*
- Define a class of procedures that need not terminate but assign a value to every finite stage, and ask which guarantees of CORE characterise it.
- Relate the regress of Theorem 3 to such procedures: is the barrier then a property of the process (no stage at which a best continuation is computable) rather than of a table?
- Sequential voting in random order with private preferences (*Where the Symmetry Goes*, Section 5; main roadmap, thread D): is the best reply computable given a prior, and what replaces the diagonal?

### T4. Composition across scales

*Question.* A decision binds only the group that reaches it, and effects on others need a wider agreement that includes them. State this as an extension problem and find which mechanisms extend well.

*Exists.* Thread A of the main roadmap: joins and one-voter extensions as contexts (*Consistency as an Extension Problem*, Section 3c); associativity of proportional lotteries; sortition preserving the benchmark (CORE paper, Proposition 5); the delegation rules of the CORE paper, Section 13.2 (one seat per person, holder serves, nested revocation).

*First steps.*
- Covers by more than two overlapping sub-electorates, the step to a sheaf formulation (open in the main roadmap).
- Delegation formally. Each pass is a declaration that, in a deliberation between the two, the passer would accept the successor's proposal. Show what this preserves (no one's weight changes; the bound of the paper's Proposition 4 on shifts of endowment) and state precisely what it does not (the composition of the body may drift), so that the drift becomes a question with a measure.
- Order and bracketing of participants. *A Ladder of Lost Properties* conjectures that symmetric continuous rules at five alternatives need an order on the voters and at nine a bracketing of them. A proof or counterexample would connect grouping and delegation to the algebra (*Equivariant Obstructions*, open question 1).

### T5. The choice of fallback

*Question.* Random ballot and maximal lotteries are the two distinguished fair lotteries: the first escapes the strategic regress and ignores pairwise structure, the second respects pairwise structure and consistency for lotteries as wholes and keeps the regress. Which should a consensus procedure fall back on, or which mixture?

*Exists.* The comparison from strategy, aggregation, electorates and the Equality Criterion (*CORE and the Formal Results*, Section 2 and question 4; *The Equality Criterion and Reversal*).

*First step.* How manipulable each is when used as the fallback of a consensus procedure, where only the threat point matters, not the fallback's outcome itself. This can be computed for small cases.

### T6. Agents that model each other

*Question.* Participants who model one another's reasoning run into the diagonal of T1. Settle where it holds.

*Exists.* Thread D of the main roadmap: the rational diagonal on forms that are not tight and on totally tight forms; its failure on some tight forms with a common veto.

*First steps.* The remaining tight forms; randomised strategists; the call game with private ideals (*CORE and the Formal Results*, question 3).

### T7. Measuring misalignment

*Question.* If the obstruction can be measured, reducing conflict becomes a quantity rather than a slogan.

*Exists.* Degrees as real-valued classes; the contextual fraction for strategy-proof lotteries; the shortfall of the rational floor.

*First step.* Compare these measures on common examples, and ask whether a measure exists that is monotone under the exits of T2: smaller after an exit than before.

## 5. Corrections to earlier statements

Earlier informal texts stated some points more strongly than the formal work supports. The corrected forms are:

- **CORE is not strategy-proof.** Deliberation under CORE is strategic in Gibbard's full sense. What holds is that the fallback is straightforward and that certain floors are guaranteed: the paper's floor against arbitrary others, the rational floor against individually rational groups, and the endowment itself under the conditions of *CORE and the Formal Results*, Section 3b.
- **Random ballot is the unique fair fallback only relative to some criteria**: strategy-proofness or full independence, each with unanimity and anonymity. Relative to consistency over electorates and the Condorcet principle, the unique fair lottery is the maximal lottery (Brandl, Brandt and Seedig 2016). Which fallback to use is T5.
- **Optimality of consensus with random exclusion is open.** The fallback is characterised; that the whole procedure is optimal under minimal assumptions is not shown. Gibbard (1978) and *Walls and Strategy*, Theorem 6, show the trade-off it makes: freedom from the strategic regress at the fallback, at the cost of ex ante efficiency there, recovered only by deliberation, which carries the regress.
- **Alignment is not one theorem stating a goal.** As Section 1 says, it is a family of negative and constructive theorems, together with gaps (Section 2) that lie outside mathematics of this kind.

## 6. Suggested order

1. T1, which is mostly writing, since the theorems exist.
2. T2, the classification table and the question about level 2, which builds on the main roadmap's threads A and B.
3. T3, starting from the martingale and the class of non-terminating procedures.
4. T5, a computation on small cases.
5. T4 and T6 run alongside thread A and thread D of the main roadmap, where their open questions already sit.
6. T7 once T2 has its table.

## References

- Brandl, F., Brandt, F. and Seedig, H. G. (2016). Consistent probabilistic social choice. *Econometrica* 84, 1839–1880.
- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41, 587–601.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Hiveism (2025a). Recursive alignment. https://hiveism.substack.com/p/recursive-alignment
- Hiveism (2025b). A path towards solving AI alignment. https://hiveism.substack.com/p/a-path-towards-solving-ai-alignment
