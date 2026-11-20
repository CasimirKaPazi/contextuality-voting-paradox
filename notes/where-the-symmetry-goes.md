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
4. *Exits from (i) and (ii) lead to (iii).* Chichilnisky's obstruction disappears on the filled disc; Balinski–Young's in expectation; Moulin's dilemma with lotteries. In each case the exit is convexification.
5. *Projection is a discrete form of (iii).* Borda neither keeps nor breaks the cyclic symmetry visibly; it discards the part of the data that carries it. On a profile that consists only of a cyclic component, every candidate receives the same Borda score, and the output is complete indifference. Among weak orders, complete indifference is the one ranking fixed by every renaming of the alternatives, the counterpart of the uniform lottery among lotteries. So Borda sends the cyclic part of a profile to the fixed point of a target that keeps the symmetry, which is placement (iii), with weak orders in place of lotteries. Borda does not thereby escape Arrow's theorem, which also allows weak orders as outputs: it violates independence of irrelevant alternatives.

The input and the output are not symmetric in the same way, however. A one-way cycle (shares on abc, bca and cab) is invariant under rotation of the alternatives but not under reversal, which turns it into the opposite cycle. Complete indifference is invariant under both. Mapping the one cycle to indifference therefore erases its handedness, the sign of the winding. This is the identification of a cycle with its reverse made in the Klein bottle construction, taken further: the Klein bottle keeps the parity, while Borda discards the cyclic component altogether. Only a profile carrying both directions equally — all six rankings in equal shares — is invariant under every renaming, and there nothing is lost.

At a pure one-way cycle no neutral rule could keep the handedness: every outcome fixed by rotation (the uniform lottery, complete indifference) is also fixed by reversal. The direction of a cycle can be represented only by the cycle itself, placement (i). In profiles combining a cyclic part with a consistent ranking the loss matters, since the direction of the cyclic part decides which comparison is weakest, and Condorcet methods use exactly this. A cyclic component introduced strategically is invisible to the Borda score.
6. *Consistency and the Condorcet principle ask for an unbeaten candidate.* The blocking construction in *A Map of Voting Paradoxes* shows that a consistent Condorcet extension would have to elect, at every profile, a candidate whom no one beats. At a profile without a Condorcet winner, assigning to each candidate one that beats it defines a map of the candidates into themselves without a fixed point. The impossibility is the absence of a fixed point of this map, which is the form of the obstruction in Lawvere's theorem and in the bounded-line argument of *Cycles, Twists and Walls*.

## 7. Open questions

1. State the trichotomy of Section 2 as a theorem: for aggregation maps that commute with a group acting on alternatives, classify targets by whether the group acts freely, trivially, or with a fixed point, and identify the corresponding impossibility in each case.
2. The sorting in Section 6 suggests that Arrow and Gibbard–Satterthwaite are pure cases of (ii) and that the two-family theorems combine placements. Can the combined cases be characterised as those in which a symmetry break must also satisfy a gluing condition?
3. Formulate the composed-voter recursion: a hierarchy of aggregations, each with a symmetry-breaking or randomising step, and conditions under which the whole is coherent.
4. Make Section 5 precise: for sequential voting in random order with private preferences, is the best reply computable given a prior over preferences, and what replaces the diagonal argument?

## References

- Balinski, M. L. and Young, H. P. (1982). *Fair Representation*. Yale University Press.
- Brouwer, L. E. J. (1911). Über Abbildung von Mannigfaltigkeiten. *Mathematische Annalen* 71, 97–115.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Fallenstein, B., Taylor, J. and Christiano, P. (2015). Reflective oracles: a foundation for classical game theory. arXiv:1508.04145.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem. *Duke Mathematical Journal* 8, 457–459.
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- May, K. O. (1952). A set of independent necessary and sufficient conditions for simple majority decision. *Econometrica* 20, 680–684.
- McKelvey, R. D. (1976). Intransitivities in multidimensional voting models and some implications for agenda control. *Journal of Economic Theory* 12, 472–482.
- Moulin, H. (1983). *The Strategy of Social Choice*. North-Holland.
- Moulin, H. (1988). Condorcet's principle implies the no show paradox. *Journal of Economic Theory* 45, 53–64.
- Nash, J. (1950). Equilibrium points in n-person games. *PNAS* 36, 48–49.
- Sen, A. (1970). The impossibility of a Paretian liberal. *Journal of Political Economy* 78, 152–157.
- Scott, D. (1972). Continuous lattices. *Lecture Notes in Mathematics* 274, 97–136.
- Young, H. P. and Levenglick, A. (1978). A consistent extension of Condorcet's election principle. *SIAM Journal on Applied Mathematics* 35, 285–300.
