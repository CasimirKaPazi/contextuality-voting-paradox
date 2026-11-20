# Consistency as an Extension Problem

*Working note. It states the consistency criterion of voting as an extension problem in the space of vote shares, identifies the obstruction for Condorcet methods, and combines this with known characterisations to describe which combinations of symmetry, gluing and sensitivity to cycles are possible, and with which kind of output. Cited results are marked; the overall reading is interpretation.*

## 1. Setting

Fix m candidates. A profile is described, up to the size of the electorate, by its vote shares: a point p of the simplex Δ whose vertices are the m! strict rankings. Joining two disjoint electorates with shares p and q, of sizes in the ratio t : (1 − t), gives the shares t p + (1 − t) q. Rational shares correspond to finite electorates; real shares are their limit.

A rule assigns to each p a set f(p) of winners (or, below, a lottery). The **consistency** criterion (reinforcement; Smith 1973, Young 1975) says: if f(p) and f(q) have common winners, the union elects exactly these. For a rule with unique winners this says that each winning region W_x = {p : f(p) = {x}} is closed under mixing — it is **convex**. Gluing local results into a global one is, in this space, convexity.

Young (1975) showed that, with an unbounded supply of potential voters, the anonymous, neutral and continuous rules satisfying consistency are exactly the scoring rules (without continuity: composite scoring rules, in which further scoring vectors break ties).

## 2. The Condorcet winner as a partial assignment with holes

For each candidate x let R_x be the set of shares at which x is the Condorcet winner. R_x is the intersection of the half-spaces "x beats y" for all y ≠ x, hence convex. The assignment p ↦ x on R_x is therefore consistent wherever it is defined: two profiles in R_x mix to a profile in R_x, and profiles in different regions impose no constraint.

The complement of the regions R_x (apart from ties) is the **cycle region**: the profiles without a Condorcet winner. A Condorcet extension is an extension of the partial assignment across this region. Asking it to be consistent asks for a convex extension: every winning region W_x must contain R_x, be convex, and the W_x must together cover Δ.

**Blocking lemma** (any number of candidates; proved in *A Map of Voting Paradoxes*). Let p be in the cycle region and x any candidate. Since x is not a Condorcet winner at p, some c beats x at p. There is a profile q in R_x, and a mixture of p with q, that lies in R_c. Hence p cannot be assigned to x.

So the partial assignment has no consistent extension across any point of the cycle region. The structure of the obstruction is simple: an extension would have to choose, at p, a candidate whom no one beats; at a point of the cycle region, choosing for each candidate one that beats it defines a map of the candidates into themselves without a fixed point. The failure to extend is the absence of a fixed point.

**Relation to contextuality.** The form is that of a local-to-global problem: data defined consistently on parts of a space that admit no global consistent extension. Two differences from the sheaf-theoretic setting of Abramsky and Brandenburger should be kept in view. The condition here is closure under mixing (convexity), not agreement on overlaps of a cover; and the obstruction is a fixed-point-free map of the candidates rather than a cohomology class. For three candidates there is a visible topology: each of the two cycle cones has three faces, and across them lie the regions R_a, R_b, R_c in cyclic order, the direction of the cycle. Whether the obstruction can be expressed as an invariant of this arrangement — the winding again — is open.

## 3. Symmetry, gluing and cycles

Three properties are in play:

- **S, symmetry**: anonymity and neutrality.
- **G, gluing**: consistency over electorates (population-consistency for lotteries).
- **C, cycle sensitivity**: the Condorcet principle, electing a Condorcet winner when there is one.

The output may be **deterministic** (sets of winners, or rankings) or a **lottery**.

| Output | Combination | Status | Where the cycle goes |
|---|---|---|---|
| deterministic | S + G (+ continuity) | possible, exactly the scoring rules (Young 1975) | every scoring rule gives a complete tie on a profile in which each candidate occupies each position equally often, such as abc, bca, cab: pure cycles are sent to indifference and their direction is erased (placement iii, discrete) |
| deterministic | G + C | impossible (Young and Levenglick 1978; every Condorcet extension fails from eight voters, every anonymous and neutral one from five, for three candidates: Brandt, Dong and Peters) | the blocking lemma: no break of the cycle glues |
| deterministic | S + C, unique winner | impossible at the Condorcet profile (Section 1 of *Where the Symmetry Goes*) | a tie-breaker or agenda breaks the symmetry from outside (placement ii) |
| lottery | S + G + C, and consistency with respect to clones | possible, uniquely: **maximal lotteries** (Fishburn 1984; Brandl, Brandt and Seedig 2016) | the lottery is the optimal mixed strategy of the symmetric zero-sum game given by the pairwise majority margins; it exists by von Neumann's minimax theorem (placement iii) |

Brandl, Brandt and Seedig also show that consistency over electorates and consistency with respect to clones cannot both hold for any deterministic rule. These are the two axes of *A Map of Voting Paradoxes* — linearity in voters, and pairwise structure, with which clone independence was grouped — and the lottery that reconciles them is unique.

**The cycle inside a maximal lottery.** For a majority cycle a ≻ b ≻ c ≻ a with margins m_ab, m_bc, m_ca, the maximal lottery gives each candidate a probability proportional to the margin of the comparison not involving it: p_a : p_b : p_c = m_bc : m_ca : m_ab. (Each candidate then has expected margin zero against the lottery.) The reversed cycle with the same magnitudes gives the same lottery. Maximal lotteries thus keep the strengths of the cyclic comparisons, which Borda discards, and lose only their direction, which no neutral outcome can carry (*Where the Symmetry Goes*, observation 5).

## 3a. Why maximal lotteries glue, and why deterministic rules cannot also respect clones

**Gluing as a convex condition.** Write M(p) for the matrix of pairwise majority margins of the shares p; it is linear in p. A lottery q is maximal for M if it does at least as well as every candidate, that is, qᵀM ≥ 0 in every coordinate. For fixed q this is a system of linear inequalities in M. If q is maximal for M(p) and for M(p′), it is therefore maximal for every mixture t·M(p) + (1 − t)·M(p′) = M(t p + (1 − t) p′). That is population-consistency, in one line. The condition "x is the winner" of a Condorcet extension has no such form: it would have to read "x is unbeaten", and at a profile with a cycle no candidate is. Maximal lotteries replace an unsatisfiable condition by one that is always satisfiable (by the minimax theorem) and convex in the profile.

**Positions versus comparisons.** Brandl, Brandt and Seedig show that no deterministic rule satisfies both consistency over electorates and consistency with respect to clones. In the terms used here the reason is visible for symmetric rules. By Young's theorem, symmetric and consistent deterministic rules are scoring rules: they give points by *position* in a ranking. Inserting a clone inserts a position, and shifts the positions, hence the scores, of every candidate ranked below it; the coordinate system the scores are written in changes when the set of alternatives is refined. Pairwise comparisons do not depend on positions: introducing clones of x leaves the comparison between any two other candidates unchanged. So the two axes of *A Map of Voting Paradoxes* correspond to two kinds of data: position-based data are linear in voters and can be glued, but are not invariant under refining the alternatives; comparison-based data are invariant under that refinement, but a deterministic decision based on them cannot be glued. Maximal lotteries use comparison-based data and replace the decision by a convex optimality condition, and so have both.

This is an explanation of the incompatibility for symmetric rules, not a new proof of the theorem, which is more general.

## 4. Reading

Taken together:

- A deterministic rule must choose between gluing and seeing cycles. Symmetric gluing forces linearity, and linear rules are blind to cycles. Seeing cycles forbids gluing, and determinism then forces an arbitrary break.
- In lotteries, symmetry, gluing and cycle sensitivity are jointly possible. The reconciling rule is a fixed point: the equilibrium of the game in which the candidates play against each other with the majority margins as payoffs. The obstruction to gluing is removed by convexification, as the obstruction to a symmetric choice was.
- What remains is strategy. Maximal lotteries are not strategy-proof; by Gibbard (1977) the only strategy-proof rules that are efficient ex post are random dictatorships, and by Gibbard (1978) and Theorem 10 of *Cycles, Twists and Walls*, avoiding the strategic regress costs ex ante efficiency. The obstruction moves one level up: from aggregating given preferences to reasoning about the preferences others will report.

On this reading the problem is resolved at one level by a fixed point and reappears at the next, which is the recursive pattern the wider project expects. *(Interpretation.)*

**Consequence for consensus with a random fallback.** Random dictatorship and maximal lotteries are the two distinguished lotteries in this picture: the first removes the strategic regress and ignores the pairwise structure; the second respects the pairwise structure and gluing, and leaves the regress. A consensus procedure with a fallback chooses between them, or between mixtures of them; comparing the two as fallbacks is a concrete question for the design of such procedures.

## 5. Open questions

1. Express the obstruction of Section 2 as an invariant of the arrangement of Condorcet regions around the cycle region, for three and for more candidates.
2. Section 3a explains the incompatibility of consistency over electorates and over clones for symmetric deterministic rules through positions and comparisons. Is there a blocking-type argument that covers the non-symmetric case as well?
3. Characterise how far maximal lotteries are from strategy-proofness, and compare them with random dictatorship as a fallback for consensus procedures. A related point concerns adding alternatives. When voters' utilities decrease concavely with distance in a space of positions, every voter prefers a candidate placed at the mean position of a lottery to the lottery itself (Jensen's inequality). A compromise therefore always exists against a lottery fallback, even where no position beats every other, as in McKelvey's theorem. Successive compromises can then be expected to move the remaining cycle into a small central region rather than remove it. The cost of a final lottery would then shrink with the size of that region. Whether deliberately sustained cycles can prevent this, and how far random removal deters them, are open.
4. Does the pattern "resolved by a fixed point, reappearing one level up" continue: is there a natural third level beyond aggregation and strategy?

## References

- Brandl, F., Brandt, F. and Seedig, H. G. (2016). Consistent probabilistic social choice. *Econometrica* 84, 1839–1880. arXiv:1503.00694.
- Brandt, F., Dong, C. and Peters, D. (2024). Condorcet-consistent choice among three candidates. arXiv:2411.19857.
- Fishburn, P. C. (1984). Probabilistic social choice based on simple voting comparisons. *Review of Economic Studies* 51, 683–692.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Smith, J. H. (1973). Aggregation of preferences with variable electorate. *Econometrica* 41, 1027–1041.
- von Neumann, J. (1928). Zur Theorie der Gesellschaftsspiele. *Mathematische Annalen* 100, 295–320.
- Young, H. P. (1975). Social choice scoring functions. *SIAM Journal on Applied Mathematics* 28, 824–838.
- Young, H. P. and Levenglick, A. (1978). A consistent extension of Condorcet's election principle. *SIAM Journal on Applied Mathematics* 35, 285–300.
