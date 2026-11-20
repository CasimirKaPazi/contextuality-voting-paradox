# Where the Symmetry Goes

*Working note, exploration phase. It records a reading of the impossibility results as statements about where an unavoidable symmetry ends up when preferences are aggregated. The mathematical facts used are standard and cited; the organisation into one picture is interpretation.*

## 1. The starting observation

Take the profile of three voters with the rankings abc, bca and cab. Renaming the alternatives cyclically, a → b → c → a, maps this profile to itself: the three ballots are exchanged among the voters. Any rule that treats voters alike (anonymity) and alternatives alike (neutrality) must therefore return an outcome that the renaming leaves fixed. No single alternative is fixed by it. The only lottery it fixes is the uniform one.

A finite total order is *rigid*: its only symmetry is the identity. A cyclic order on three alternatives is not: it has a rotation without a fixed point. Aggregating such a profile into a ranking means mapping an object with a fixed-point-free symmetry onto a rigid one. The symmetry cannot be carried across. It has to end up somewhere.

## 2. Three places it can go

What happens depends on the kind of target the aggregation maps into.

**(i) A target that keeps the symmetry.** If the target is itself cyclic — the alternatives with their cyclic order, or truth values with negation — it carries a self-map without a fixed point. This is the condition in Lawvere's fixed-point theorem: when the target has such a map, no structure that refers to itself through the target can be complete. The obstruction appears in the output, as a paradox: the Condorcet cycle, or the Liar.

**(ii) A rigid target.** If the target is a total order, every symmetry of it is trivial and Lawvere's argument has nothing to act on there. The aggregation itself must then break the symmetry: by a tie-breaking order, an agenda, a status quo, or a dictator. This is the side of Arrow's theorem and of the incompatibility of anonymity, neutrality and determinism (Moulin). The obstruction has moved from the output into the rule.

**(iii) A target that keeps the symmetry and has a fixed point.** The simplex of lotteries over the alternatives carries the rotation, but the rotation fixes its centre, and by Brouwer's theorem every continuous self-map of the simplex has a fixed point. Lawvere's theorem now runs the other way: where every endomorphism of the target has a fixed point, self-reference can be consistent. This is the principle behind Scott's models of spaces isomorphic to their own function spaces, behind the existence of mixed-strategy equilibria (Nash, via Brouwer or Kakutani), and behind reflective oracles (Fallenstein, Taylor and Christiano, via Kakutani). The price is that the result is a lottery, and by Gibbard (1978) a procedure in which dominant strategies always exist is then in general inefficient ex ante.

The impossibility theorems can be read as statements about these three placements. A rule that insists on a definite ranking (ii) must break the symmetry; a rule that refuses to break it (i) produces a contradiction; a rule that dissolves it into a fixed point (iii) produces chance and gives up some efficiency. Combinations of criteria that are incompatible correspond to different decisions about where the leftover symmetry may go.

## 3. Composed voters

Social choice theory takes each voter's ranking as given. A voter is not a primitive: a ranking is formed from many considerations, and forming it is an aggregation one level down. If the considerations are in tension, the same three options arise inside the voter. A transitive preference is then the result of option (ii) at some internal level: a symmetry broken without a reason that could be justified from the considerations alone.

The theorems hold with voters as primitives, but this hides that the problem recurs at every level of composition. A procedure that is to be sound at every scale cannot rely on lower levels having already solved it. It needs, at each level, a way of resolving symmetry that does not pretend to a justification it does not have: a random element, which must then fit into a coherent whole at the next level. This is the shape of consensus with a random fallback, repeated across scales.

## 4. Agreeing for different reasons

Two groups may reach the same conclusion for incompatible reasons. Combining their data, an algorithm (no change of mind is required) may find that the pieces do not fit into one picture, and that the union points elsewhere than either part. Quantum contextuality has exactly this form: each context taken alone is consistent with hidden variables, while all contexts together exclude them.

The consistency criterion of voting (Smith, Young) demands the opposite: a candidate who wins in each of two electorates must win in their union. At the level of winners this forces gluing of local conclusions even when the full data do not glue. Read this way, winner-level consistency is an assumption of non-contextuality. A concrete case uses plurality, which is consistent: with three voters ranking abc, two bca and two cba, plurality elects a; with every ballot reversed it again elects a; in the union every pairwise comparison is exactly tied, and consistency, as plurality does, still returns a. Kemeny's rule, which satisfies consistency for full rankings but not for winners, keeps enough of the local data to notice a mismatch that the winner alone hides.

## 5. Sequential votes in random order

If voters are drawn one at a time in random order, each seeing the votes already cast but not knowing who comes next or what they prefer, the mutual prediction on which the diagonal argument of *Cycles, Twists and Walls* rests does not arise: later voters see earlier votes and need not predict them, so prediction runs only forward and terminates. What remains is uncertainty about future voters. The guess is that this converts the strategic regress into risk — a lottery over continuations — rather than a halting-type obstruction. A fixed and known order, by contrast, breaks the symmetry in advance in a way everyone can exploit. Not yet examined formally.

## 6. Known results sorted by placement

A first sorting of known theorems and paradoxes by where the symmetry goes: (i) into the output, which keeps a fixed-point-free symmetry and shows a paradox; (ii) into the rule, which breaks the symmetry to reach a rigid target; (iii) into a fixed point of a target that keeps the symmetry. The sorting is interpretation; the results themselves are cited.

| Result | Target | Placement | Remark |
|---|---|---|---|
| Condorcet paradox | tournaments (pairwise majority relation) | (i) | pairwise majority is anonymous and neutral; the cycle is the symmetry surviving in the output |
| Liar paradox; Lawvere | truth values with negation | (i) | negation is the fixed-point-free map |
| Chichilnisky | preference space itself (a circle of directions) | (i) | a continuous, anonymous, unanimous average on a circle does not exist; on the filled disc it does, which is a move to (iii) |
| McKelvey | spatial majority relation | (i), and (ii) for the agenda setter | without a total median the whole space is one cycle set; an agenda setter breaks the symmetry and can reach any outcome |
| May's theorem | two alternatives | (i) only at exact ties | with two alternatives the swap is the fixed-point-free symmetry; it bites only at a tie, which is a wall |
| Anonymity, neutrality, determinism (Moulin) | single alternatives | (ii) forced | the dilemma in its plainest form: some symmetry must be broken |
| Arrow | total orders | (ii) | the break falls on the voters: a dictator. Weak orders would admit the fully indifferent outcome, a trivial fixed point, but IIA and Pareto exclude it in general |
| Gibbard–Satterthwaite | single winners, strategic voters | (ii) | strategy-proofness forces the break onto one voter |
| Balinski–Young | integer seat numbers | (ii) | rounding to integers breaks proportionality somewhere; randomised apportionment satisfies quota in expectation, a move to (iii) |
| Kemeny | total orders | (ii), break chosen by the profile | cycles are broken at their cheapest edges; consistent for rankings, not for winners |
| Borda / Hodge gradient | scores (weak orders) | (iii), discrete | the cyclic part is sent to complete indifference, the fixed point among weak orders (observation 5) |
| Young–Levenglick; Moulin's no-show theorem | single winners, variable electorate | (i) then (ii), with gluing | a Condorcet extension keeps the pairwise cycle and then breaks it per profile; no such break is compatible across electorates |
| Sen's liberal paradox | social preference | (ii) per pair, then (i) | individual rights are local dictators on pairs; together with Pareto they produce a cycle |
| Gibbard 1977 | lotteries | (iii) | strategy-proof random rules are mixtures of unilateral and duple rules; with ex post efficiency, random dictatorship |
| Gibbard 1978; Theorem 10 of *Cycles, Twists and Walls* | lotteries, utility scales | (iii) or regress | dominant strategies throughout cost ex ante efficiency; otherwise the strategic regress returns |
| Theorem 8 of *Cycles, Twists and Walls* | strategies | (ii) or (i) at the level of reasoning | a dominant strategy is a fixed point; without one, the diagonal argument produces the regress |
| Nash; reflective oracles | mixed strategies, probabilistic oracles | (iii) | Brouwer and Kakutani make self-reference consistent |

**Gluing and symmetry together.** *A Map of Voting Paradoxes* gives an elementary argument, for three candidates and vote shares, that no Condorcet extension is consistent: electing any candidate of a cycle is undone by mixing with a profile from the Condorcet region of that candidate's predecessor in the cycle. The obstruction to gluing (thread A of the roadmap) is the fixed-point-free rotation (this note) acting on the possible symmetry breaks. This places Young–Levenglick firmly among the mixed cases of the table: the cycle must be broken, and no break is compatible with gluing, because the set of possible breaks is itself permuted cyclically without a fixed point.

**Observations.**

1. *Pure cases.* Condorcet, the Liar, Chichilnisky and McKelvey are pure (i). Arrow, Gibbard–Satterthwaite and Moulin's dilemma are pure (ii). Gibbard 1977, Nash and reflective oracles are pure (iii).
2. *Mixed cases are the two-family theorems.* The results combining placements — Young–Levenglick, the no-show theorem, Sen — are exactly those identified in *A Map of Voting Paradoxes* as incompatibilities between two families of criteria. They arise when a symmetry kept in one place must be broken in a way that is also required to glue in another.
3. *The fixed point is the average of the breaks.* Random dictatorship is the uniform mixture of all dictatorships, and Gibbard's strategy-proof random rules are mixtures of unilateral and duple rules: the (iii) solutions are built as averages over (ii) solutions. The fixed point of the symmetry on the space of rules is the barycentre of the rules that break it.

   The same statement has a topological form. In Baryshnikov and Root's proof of the Gibbard–Satterthwaite theorem, the space of profiles carries one oriented cycle for each voter, and a unanimous monotone rule assigns to each voter a degree: how often the outcome winds around the space of outcomes while that voter's cycle is traversed once. The degrees are integers in {0, 1}, and unanimity forces their sum to be 1, so exactly one voter has degree 1. If degrees could be real numbers, the solution that treats all N voters alike would give each the degree 1/N, which is random dictatorship. This is Chichilnisky's equation N·d = 1 again, without an integer solution and with the obvious real one. Baryshnikov and Root treat only deterministic rules; reading random dictatorship as the fractional solution is an interpretation, not a result of their paper.
4. *Exits from (i) and (ii) lead to (iii).* Chichilnisky's obstruction disappears on the filled disc; Balinski–Young's in expectation; Moulin's dilemma with lotteries. In each case the exit is convexification.
5. *Projection is a discrete form of (iii).* Borda neither keeps nor breaks the cyclic symmetry visibly; it discards the part of the data that carries it. On a profile that consists only of a cyclic component, every candidate receives the same Borda score, and the output is complete indifference. Among weak orders, complete indifference is the one ranking fixed by every renaming of the alternatives, the counterpart of the uniform lottery among lotteries. So Borda sends the cyclic part of a profile to the fixed point of a target that keeps the symmetry, which is placement (iii), with weak orders in place of lotteries. Borda does not thereby escape Arrow's theorem, which also allows weak orders as outputs: it violates independence of irrelevant alternatives.

The input and the output are not symmetric in the same way, however. A one-way cycle (shares on abc, bca and cab) is invariant under rotation of the alternatives but not under reversal, which turns it into the opposite cycle. Complete indifference is invariant under both. Mapping the one cycle to indifference therefore erases its handedness, the sign of the winding. This is the identification of a cycle with its reverse made in the Klein bottle construction, taken further: the Klein bottle keeps the parity, while Borda discards the cyclic component altogether. Only a profile carrying both directions equally — all six rankings in equal shares — is invariant under every renaming, and there nothing is lost.

At a pure one-way cycle no neutral rule could keep the handedness: every outcome fixed by rotation (the uniform lottery, complete indifference) is also fixed by reversal. The direction of a cycle can be represented only by the cycle itself, placement (i). In profiles combining a cyclic part with a consistent ranking the loss matters, since the direction of the cyclic part decides which comparison is weakest, and Condorcet methods use exactly this. A cyclic component introduced strategically is invisible to the Borda score.
6. *Consistency and the Condorcet principle ask for an unbeaten candidate.* The blocking construction in *A Map of Voting Paradoxes* shows that a consistent Condorcet extension would have to elect, at every profile, a candidate whom no one beats. At a profile without a Condorcet winner, assigning to each candidate one that beats it defines a map of the candidates into themselves without a fixed point. The impossibility is the absence of a fixed point of this map, which is the form of the obstruction in Lawvere's theorem and in the bounded-line argument of *Cycles, Twists and Walls*.
7. *Arrow's theorem is a symmetry-breaking task.* Rajsbaum and Raventós-Pujol prove Arrow's theorem for two voters and three alternatives with the index lemma of combinatorial topology, and reduce the general finite case to this one. Their output complex has one vertex for each pair of alternatives and each of its two signs; its triangles are the six strict orders, and the two Condorcet cycles are hollow triangles. This is the annulus of strict orders with its two boundary circles left open, the object that Livson, Pritam and Prokopenko close into a Klein bottle. Independence of irrelevant alternatives makes a rule a colour-preserving map, the colour of a vertex being its pair. The index lemma states that the winding of the boundary of a triangulated surface around a triangle equals the signed number of three-coloured triangles inside. Recolouring each vertex by the position of its pair around the triangle plus its sign, mod 3, makes exactly the cyclic triangles three-coloured. Since the image avoids them, nothing inside counts, and the windings of the four boundary circles of the profile complex must cancel. Unanimity fixes two of them; the other two are forced, and the remaining case analysis leaves two solutions, one per voter. The obstruction is the integer winding of *Cycles, Twists and Walls*, Proposition 4, in discrete form.

   Three points in the paper fit the picture here.

   First, the authors place the index lemma beside Sperner's lemma in distributed computing. Sperner's lemma underlies impossibility results for agreement tasks (consensus, set agreement); the index lemma underlies those for symmetry-breaking tasks (renaming, weak symmetry breaking). As a coloured complex, the output complex above is the output complex of weak symmetry breaking for three processes, in which each process outputs a bit and the bits may not all be equal: transitivity is the not-all-equal condition. Read in this way, each pairwise comparison is a process that decides from its own view only (independence of irrelevant alternatives), no process communicates with another, and together they must avoid the all-equal outcome. Without communication this can be guaranteed only by copying one common source whose bits already satisfy the condition, a single voter. A dictator is a shared reference, and random dictatorship is a shared coin. The identification and its reading are not in the paper. In distributed computing the processes do communicate, and whether weak symmetry breaking is solvable depends on arithmetic properties of the number of processes (Castañeda and Rajsbaum); the case without communication is the degenerate one.

   Second, the authors' version of the pivotal-voter argument closes into a cycle of weak inequalities between the pivotal voters of the six ordered pairs, k_BA ≤ k_CA ≤ k_CB ≤ k_AB ≤ k_AC ≤ k_BC ≤ k_BA. Returning to the start forces all six to be equal: there is one pivotal voter, the dictator. This is the bounded-line argument of *Cycles, Twists and Walls*, Proposition 1, with ≤ in place of <. A strict cycle cannot be placed on a line; a weak cycle placed on a line is constant. The Condorcet cycle is the first case and the dictator the second: where the alternatives cannot climb a staircase around a loop, the index of the deciding voter cannot change around it either.

   Third, on the domain in which no voter ranks C between A and B, the rule that takes the comparison of A and B from voter 1 and both comparisons with C from voter 2 is unanimous, independent of irrelevant alternatives and not dictatorial. On this domain {A, B} is a clone set for every voter, and the rule is a composition: one voter places the block, another orders its inside. *(Reading.)* Decision power can be split along a hierarchy of alternatives, but not around a cycle. This bears on question 3 below.

## 7. Open questions

1. State the trichotomy of Section 2 as a theorem: for aggregation maps that commute with a group acting on alternatives, classify targets by whether the group acts freely, trivially, or with a fixed point, and identify the corresponding impossibility in each case.
2. The sorting in Section 6 suggests that Arrow and Gibbard–Satterthwaite are pure cases of (ii) and that the two-family theorems combine placements. Can the combined cases be characterised as those in which a symmetry break must also satisfy a gluing condition?
3. Formulate the composed-voter recursion: a hierarchy of aggregations, each with a symmetry-breaking or randomising step, and conditions under which the whole is coherent. The clone-set example in observation 7 is the simplest coherent case: a hierarchy of alternatives along which decision power is split.
4. Make Section 5 precise: for sequential voting in random order with private preferences, is the best reply computable given a prior over preferences, and what replaces the diagonal argument?

## References

- Balinski, M. L. and Young, H. P. (1982). *Fair Representation*. Yale University Press.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Brouwer, L. E. J. (1911). Über Abbildung von Mannigfaltigkeiten. *Mathematische Annalen* 71, 97–115.
- Castañeda, A. and Rajsbaum, S. (2010). New combinatorial topology bounds for renaming: the lower bound. *Distributed Computing* 22, 287–301.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Fallenstein, B., Taylor, J. and Christiano, P. (2015). Reflective oracles: a foundation for classical game theory. arXiv:1508.04145.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem. *Duke Mathematical Journal* 8, 457–459.
- Herlihy, M., Kozlov, D. and Rajsbaum, S. (2013). *Distributed Computing Through Combinatorial Topology*. Morgan Kaufmann.
- Livson, O., Pritam, S. and Prokopenko, M. (2026). The non-orientable topology of Condorcet's paradox. arXiv:2601.07283.
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- May, K. O. (1952). A set of independent necessary and sufficient conditions for simple majority decision. *Econometrica* 20, 680–684.
- McKelvey, R. D. (1976). Intransitivities in multidimensional voting models and some implications for agenda control. *Journal of Economic Theory* 12, 472–482.
- Moulin, H. (1983). *The Strategy of Social Choice*. North-Holland.
- Moulin, H. (1988). Condorcet's principle implies the no show paradox. *Journal of Economic Theory* 45, 53–64.
- Nash, J. (1950). Equilibrium points in n-person games. *PNAS* 36, 48–49.
- Rajsbaum, S. and Raventós-Pujol, A. (2025). A combinatorial topology approach to Arrow's impossibility theorem. *Social Choice and Welfare*. doi:10.1007/s00355-025-01609-7. Conference version in PODC 2022; preprint MPRA Paper 113858.
- Sen, A. (1970). The impossibility of a Paretian liberal. *Journal of Political Economy* 78, 152–157.
- Scott, D. (1972). Continuous lattices. *Lecture Notes in Mathematics* 274, 97–136.
- Young, H. P. and Levenglick, A. (1978). A consistent extension of Condorcet's election principle. *SIAM Journal on Applied Mathematics* 35, 285–300.
