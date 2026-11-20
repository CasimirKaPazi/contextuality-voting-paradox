# A Map of Voting Paradoxes

*Working overview. It groups the known paradoxes of voting and aggregation by what is varied, records the theorems that are known to connect them, and proposes patterns. Theorems are cited; patterns are interpretation and marked as such. References marked † are cited from memory and have not been checked against the original in this pass.*

## 1. Organising question: what is varied?

A voting paradox is a situation in which a rule behaves inconsistently when something is changed or regrouped. Most paradoxes fall into one of six families according to what changes:

1. **Nothing** — a fixed profile and a fixed set of alternatives, but the pairwise results do not fit together (static paradoxes).
2. **The set of alternatives** — adding, removing or cloning candidates.
3. **The electorate** — splitting, merging or adding voters.
4. **One voter's ballot** — a voter changes their ballot sincerely or strategically.
5. **The order of procedure** — agendas, rounds, sequences of decisions.
6. **The level of aggregation** — issues versus packages, districts versus nation, seats versus votes.

In each family a consistency requirement can be stated. Each is a requirement that results computed on parts fit the result computed on the whole, or that a change in one place does not cause an unrelated change elsewhere. This is the local-to-global form of contextuality: data that agree locally and fail to glue globally.

## 2. The families

### 2.1 Static: one profile, the parts do not fit

| Paradox | What happens | Formal core |
|---|---|---|
| Condorcet cycle | pairwise majorities form a cycle | no ranking extends the pairwise data; obstruction is a winding number (see *Cycles, Twists and Walls*) |
| Discursive dilemma / doctrinal paradox | majority on premises and on a conclusion are inconsistent | judgment aggregation; List–Pettit impossibility†; Arrow follows as a special case (Dietrich–List 2007) |
| Ostrogorski paradox | a party wins the majority on a majority of issues while losing on every issue, or similar reversals | issue-wise versus package-wise majority (overlaps with 2.6) |
| Anscombe paradox | a majority of voters is on the losing side on a majority of issues | issue-wise majority aggregated over voters |

### 2.2 Alternatives vary

| Paradox / criterion | What happens | Formal core |
|---|---|---|
| Spoiler effect; independence of irrelevant alternatives (IIA) | adding or removing a losing candidate changes the winner | Arrow: IIA, Pareto, transitivity ⇒ dictator. Abramsky: IIA is naturality of the aggregation map |
| Independence of clones | adding a near-copy of a candidate changes the winner | Tideman†; satisfied by Schulze, ranked pairs, IRV; failed by Borda, plurality. Clones add no cycles among themselves; what they distort is the linear side (Borda is inflated by teams), so clone independence sits with the pairwise rules |
| Chernoff / contraction consistency | the winner of a large menu is not the winner of a smaller menu containing it | choice-function rationality (Sen's α)† |
| Reversal paradoxes | reversing all ballots does not reverse the outcome | Saari's reversal symmetry†; satisfied by Borda among scoring rules |

### 2.3 The electorate varies

| Paradox / criterion | What happens | Formal core |
|---|---|---|
| Consistency (reinforcement) | a candidate wins in two separate electorates but not in their union | Smith 1973, Young 1975†: anonymity, neutrality, consistency (with continuity) characterise scoring rules. Young and Levenglick 1978: no Condorcet extension satisfies reinforcement (for three candidates, every Condorcet extension fails it with at least eight voters; Brandt, Dong and Peters) |
| No-show paradox (participation) | a voter is better off staying at home | Moulin 1988: no Condorcet extension satisfies participation (from four alternatives and a sufficient number of voters†); for three candidates the homogeneous Condorcet extensions avoiding it are exactly refinements of maximin (Brandt, Dong, Peters) |
| Simpson's paradox | a relation that holds in every subgroup reverses in the union | the statistical form of grouping dependence |
| Referendum paradox / districting | district majorities differ from the popular majority | non-associativity of majority (see *A Ladder of Lost Properties*) |

**The Kemeny fine point.** The Kemeny rule, read as a function producing a ranking, is consistent and Condorcet; read as a function producing only a winner, it is not consistent (Young and Levenglick 1978; Nurmi's discussion of Fishburn's objection). The reason is simple. Kemeny selects the ranking with the fewest disagreements with the ballots, counted over all voters and all pairs. This count is a sum over voters, so the count for a union of electorates is the sum of the counts for the parts; a ranking that is best in each part is best in the union. If a Condorcet winner exists, moving it to the top only reduces disagreements. But two electorates may have different best rankings with the same top candidate, say a b c d and a d c b. Then a wins in each, while the best ranking of the union can be a third ranking, best in neither part, with another candidate on top. Full rankings glue; their projection to a winner discards exactly the information that shows they disagree. Kemeny resolves cycles by reversing the cheapest set of majority comparisons — the symmetry is broken by the profile itself, at its weakest point — and finding that set is NP-hard.

**Participation and reinforcement** are related but not the same: reinforcement asks that the winner be preserved under union, participation that a newly added voter not be made worse off. Rules satisfying consistency generally satisfy participation as well.

### 2.4 One ballot varies

| Paradox / criterion | What happens | Formal core |
|---|---|---|
| Manipulability | a voter gains by misreporting | Gibbard 1973, Satterthwaite 1975; Theorem 8 of *Cycles, Twists and Walls* |
| Non-monotonicity | ranking a candidate higher makes them lose (IRV) | Muller–Satterthwaite 1977†: strong monotonicity with Pareto on three or more alternatives ⇒ dictator |
| Later-no-harm / later-no-help | adding a lower preference hurts or helps an earlier one | Woodall's criteria†; mutually incompatible with Condorcet consistency |
| Burial and compromise | strategic ranking of a rival lower, or a favourite lower | from a sincere Condorcet winner, burial requires creating a cycle (Proposition 6 of *Cycles, Twists and Walls*); within an existing cycle it can also work through the tie-breaking |

### 2.5 Order of procedure varies

| Paradox | What happens | Formal core |
|---|---|---|
| Agenda dependence | sequential pairwise votes yield different winners under different agendas | arises only when majority has a cycle; McKelvey 1976†: in spatial voting without a Condorcet winner, an agenda setter can reach almost any outcome |
| Path independence | choosing from parts of a menu and then among the winners differs from choosing from the whole | Plott 1973† |
| Iterative voting cycles | best-reply dynamics fail to settle | Meir et al.; rule-dependent |

### 2.6 Level of aggregation varies

| Paradox | What happens | Formal core |
|---|---|---|
| Multiple elections paradox | the combination that wins issue by issue receives no votes at all | Brams, Kilgour, Zwicker 1998† |
| Apportionment paradoxes (Alabama, population, new states) | rounding seats to integers produces non-monotone allocations | Balinski–Young 1982†: no apportionment method both stays within quota and avoids the population paradox |
| Liberal paradox | individual rights over personal matters conflict with Pareto | Sen 1970 |

## 3. Known links between families

Several of the strongest theorems are not impossibilities within one family but **incompatibilities between two families**:

| Theorem | Family A | Family B |
|---|---|---|
| Arrow | static (transitive social ranking) and Pareto | alternatives (IIA) |
| Young–Levenglick | static (Condorcet winner elected) | electorate (reinforcement) |
| Moulin (no-show) | static (Condorcet winner elected) | electorate (participation) |
| Gibbard–Satterthwaite | range of at least three outcomes | ballot (strategy) |
| Muller–Satterthwaite | range of at least three outcomes, Pareto | ballot (monotonicity) |
| Balinski–Young | quota (proportional fidelity) | electorate (population monotonicity) |

The family most often in tension with the others is the pairwise one: rules built from pairwise majorities (Condorcet extensions) fail the electorate family; rules built from linear counts (scoring rules) satisfy the electorate family and fail the Condorcet criterion.

**The components of a profile.** Saari decomposes profiles of three candidates into *basic* components, on which all standard methods agree; *reversal* components, which pairwise comparisons do not see and which account for all differences between the tallies of different positional rules; and *Condorcet* components, the cyclic parts that pairwise majorities see and that Borda ignores. A sharper form for the pairwise data is the combinatorial Hodge decomposition of Jiang, Lim, Yao and Ye 2011: pairwise comparison data on a graph decompose orthogonally into a gradient part (a consistent ranking, recovered by least squares), a curl part (local cycles on triangles) and a harmonic part (global cycles not visible on any triangle). On complete ranking data the gradient part is the Borda count, and their HodgeRank generalises Borda to incomplete data; Kemeny's rule corresponds to fitting signs of score differences instead of the differences themselves. Condorcet cycles live in the non-gradient parts. The winding number of *Cycles, Twists and Walls* is an integer form of the same cohomological fact. This is the most direct existing link between voting and topology on the static side, and it should be cited in that draft.

## 4. Patterns (interpretation)

**P1. Early rounding.** In almost every family, the consistent object is a count or a distribution, and the paradox is created by a deterministic decision taken before the end:

- per pair → Condorcet cycles;
- per group → consistency failures, Simpson, districting, Ostrogorski, Anscombe;
- per round → non-monotonicity of IRV (elimination rounds round off at each stage);
- per issue → multiple elections paradox;
- per seat → apportionment paradoxes.

**P2. Linear versus pairwise.** Rules that are linear in the profile (sum first, decide once) satisfy the electorate family, because sums can be computed over any grouping. Rules that decide per pair satisfy a pairwise independence but cannot satisfy the electorate family together with the Condorcet criterion. In the Hodge picture, linear rules see only the gradient; pairwise rules see the curl and harmonic parts, and must break their symmetry somehow.

**P3. Gluing.** The electorate family is literally a gluing condition. Consistency says: if the local winners on the parts of a cover of the electorate agree, the global winner equals them. Kemeny's ranking satisfies gluing; its winner does not. Gluing survives for full sections and fails after projection to the top element. This is the local-to-global structure of contextuality, with sub-electorates as contexts, and a more natural place to apply sheaf methods than the encodings tried in *Two Kinds of Loop*, which used pairs of alternatives as contexts.

Contextuality also suggests that winner-level consistency is not always desirable. In a contextual scenario each context alone supports a hidden-variable account and all together exclude it; two electorates can likewise reach the same winner for incompatible reasons. A plurality example: three voters ranking abc, two bca and two cba elect a; with every ballot reversed, plurality again elects a; in the union every pairwise comparison is exactly tied, and plurality, being consistent, still elects a. Winner-level consistency amounts to assuming non-contextuality. Saari's reversal components are the part of the profile through which this happens: they cancel exactly when a profile is joined with its reversal, and they are what separates positional rules from one another.

**Gluing as convexity (checked numerically).** Joining two electorates mixes their profiles: in terms of vote shares, the union is a weighted average of the parts. Consistency therefore says that each candidate's winning region in the simplex of vote shares is convex (closed under such averages), which is the geometric content of Young's characterisation of consistent rules. The region where a candidate is the Condorcet winner is an intersection of half-spaces and therefore convex, so for a Condorcet extension every failure of consistency must involve a profile with a majority cycle. A random test with three candidates and continuous vote shares (40,000 pairs of profiles) confirms this: Borda and plurality show no violations; maximin (equal to ranked pairs and Schulze for three candidates) and Black's rule show violations, every one of which involves a profile in the cycle region; instant runoff shows violations of which about a third involve no cycle at all, coming instead from the rounding at its elimination step. The gluing failure of a Condorcet method is located exactly where its symmetry must be broken.

**No consistent way to break a cycle (elementary, three candidates, vote shares).** The failure is not a defect of particular rules. Let x be a profile with the majority cycle a ≻ b ≻ c ≻ a, and suppose a Condorcet extension elects a at x. Let y be the profile in which a share ½ + δ/2 of voters rank a c b and a share ½ − δ/2 rank c a b. In y, a is the Condorcet winner (a beats c by δ and b unanimously), so a wins at y; and c beats b unanimously. Mix the two: z = t x + (1 − t) y. The margin of c over a in z is t·m_ca(x) − (1 − t)·δ, positive for δ small enough; the margin of c over b is (1 − t) − t·m_bc(x), positive for t < 1/(1 + m_bc(x)). For such t and δ, c is the Condorcet winner of z, so a Condorcet extension elects c, although a wins both parts. Consistency fails. The same construction blocks electing b (through a) and electing c (through b), and the reverse cycle by symmetry.

Every profile with a cycle therefore defeats every Condorcet extension, which is a continuous-shares form of the theorem of Young and Levenglick for three candidates. A numerical test confirmed this for 2,000 random cycle profiles.

**Any number of candidates.** The construction does not use the number of candidates. Let x be any profile without a Condorcet winner, with any number of candidates, and suppose a Condorcet extension elects a at x. Since a is not a Condorcet winner, some candidate c beats a in x. Let y give a share ½ + δ/2 to the ranking (a, c, then the others) and ½ − δ/2 to (c, a, then the others). In y, a is the Condorcet winner, and c beats every other candidate unanimously. Choose t = ½ / (1 + w), where w ≥ 0 is the largest margin by which c loses to any other candidate in x, and δ = ½ t·m_ca(x) / (1 − t). Then in the mixture t x + (1 − t) y, c beats a by ½ t·m_ca(x) > 0 and beats every other candidate by at least ½. So c is the Condorcet winner of the mixture, although a wins both parts. (Checked numerically for three to six candidates.)

So for a Condorcet extension, consistency fails at *every* profile without a Condorcet winner, whatever the rule does there. The reason is short: consistency together with the Condorcet principle would require the rule to elect a candidate whom nobody beats, and at such a profile every candidate is beaten by someone. This is the same structure as the bounded-line argument of *Cycles, Twists and Walls* (Proposition 1): whatever is placed on top must have something above it. The vote shares here are continuous; for finite electorates the mixture requires sufficiently many voters, consistent with the thresholds found by Brandt, Dong and Peters.

Moulin's no-show theorem does not follow from the same construction: participation adds a single voter, a vanishing share, while the blocking profile y must carry substantial weight. Why Condorcet extensions also fail participation, but only from four candidates on, remains to be placed in this picture. The structure of the obstruction is notable: electing a is blocked from the Condorcet region of c, the candidate that beats a in the cycle; b is blocked by a, c by b. The blocking relation is the cycle itself, a rotation without a fixed point. No choice of winner inside the cycle region can be glued consistently to the Condorcet regions around it, because each choice is undone by its predecessor in the cycle.

**P4. The centre.** Random dictatorship (choose a voter uniformly, elect their favourite) is linear in the profile and decides once. It satisfies consistency and participation for lotteries, monotonicity and strategy-proofness, and regrouping does not affect it. It fails ex ante efficiency and does not elect a Condorcet winner with certainty. On this map it sits at the point where the electorate, ballot and grouping families are all satisfied, and the static family is given up. Most other rules sit between it and the Condorcet extensions.

**P5. Two axes.** The incompatibilities in Section 3 suggest two axes: *pairwise structure* (respect for Condorcet winners, IIA, independence of clones) and *linearity in voters* (consistency, participation, regrouping). Deterministic rules can have at most limited amounts of both; lotteries can have full linearity.

**P6. Where the symmetry goes.** The patterns can be read together: early rounding is stopping a process that cannot be completed in finite time; the two axes are the two ways of breaking a symmetry (by pair or by voter); the centre is the fixed point that cannot be removed. The note *Where the Symmetry Goes* develops this: aggregation into a rigid total order must break a fixed-point-free symmetry of the profile, and the leftover symmetry goes into the output (a paradox), into the rule (a dictator or tie-breaker), or into a fixed point that is not a single alternative (a lottery).

**P7. Local versus global quality.** Condorcet efficiency is a local criterion (pairwise), while measures of overall welfare such as voter satisfaction efficiency are global. Under strategic voting, rules tend to drift towards Condorcet behaviour, since the pairwise structure is where strategic pressure acts. A rule that blends a gradient signal (score differences, which contain no cycles) with a signal containing the conflict (pairwise margins) trades these off; weighting the blend by the measured local inconsistency (the curl on triangles) rather than by score differences is a natural refinement.

## 5. Questions

1. Is there a single topological statement behind Young–Levenglick and Moulin, as the winding number is behind the Condorcet cycle? A natural guess: electing the Condorcet winner requires reading the curl and harmonic parts of the Hodge decomposition, and those parts do not add over sub-electorates in a way compatible with a single winner.
2. Can the consistency criterion be set up as an honest sheaf condition (sub-electorates as the cover, winners as sections), and is the Young–Levenglick theorem then an obstruction in cohomology?
3. Where do clone independence and reversal symmetry sit in the Hodge picture?
4. Is every paradox in the map an instance of early rounding (P1), or are there genuinely different mechanisms? The liberal paradox and the discursive dilemma are candidates for exceptions.

## References

- Arrow, K. J. (1963). *Social Choice and Individual Values*, 2nd ed.
- Balinski, M. L. and Young, H. P. (1982). *Fair Representation*. Yale University Press.†
- Brams, S. J., Kilgour, D. M. and Zwicker, W. S. (1998). The paradox of multiple elections. *Social Choice and Welfare* 15, 211–236.†
- Brandt, F., Dong, C. and Peters, D. (2024). Condorcet-consistent choice among three candidates. arXiv:2411.19857.
- Dietrich, F. and List, C. (2007). Arrow's theorem in judgment aggregation. *Social Choice and Welfare* 29, 19–33.
- Fishburn, P. C. and Brams, S. J. (1983). Paradoxes of preferential voting. *Mathematics Magazine* 56, 207–214.†
- Jiang, X., Lim, L.-H., Yao, Y. and Ye, Y. (2011). Statistical ranking and combinatorial Hodge theory. *Mathematical Programming* 127, 203–244.
- McKelvey, R. D. (1976). Intransitivities in multidimensional voting models and some implications for agenda control. *Journal of Economic Theory* 12, 472–482.
- Moulin, H. (1988). Condorcet's principle implies the no show paradox. *Journal of Economic Theory* 45, 53–64.
- Muller, E. and Satterthwaite, M. A. (1977). The equivalence of strong positive association and strategy-proofness. *Journal of Economic Theory* 14, 412–418.†
- Nurmi, H. On the relevance of theoretical results to voting system choice (discussion of consistency and Kemeny).
- Plott, C. R. (1973). Path independence, rationality, and social choice. *Econometrica* 41, 1075–1091.†
- Saari, D. G. (2000). Mathematical structure of voting paradoxes I, II. *Economic Theory* 15, 1–53 and 55–102.†
- Saari, D. G. (2011). Geometry of voting. In K. Arrow, A. Sen and K. Suzumura (eds.), *Handbook of Social Choice and Welfare* II, ch. 27, Elsevier.
- Sen, A. (1970). The impossibility of a Paretian liberal. *Journal of Political Economy* 78, 152–157.
- Smith, J. H. (1973). Aggregation of preferences with variable electorate. *Econometrica* 41, 1027–1041.†
- Tideman, T. N. (1987). Independence of clones as a criterion for voting rules. *Social Choice and Welfare* 4, 185–206.†
- Young, H. P. (1975). Social choice scoring functions. *SIAM Journal on Applied Mathematics* 28, 824–838.†
- Young, H. P. and Levenglick, A. (1978). A consistent extension of Condorcet's election principle. *SIAM Journal on Applied Mathematics* 35, 285–300.
