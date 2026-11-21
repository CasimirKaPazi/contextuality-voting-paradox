# Four Levels of Obstruction in Social Choice

## Inconsistency, contextuality and symmetry breaking

*Draft, November 2026.*

## Abstract

Impossibility theorems of social choice are usually stated as the incompatibility of a list of axioms. We sort them instead by how they fail, in the language of sheaf-theoretic contextuality extended by a symmetry group. A scenario can admit no locally consistent model at all; admit locally consistent models but no global solution; admit global solutions none of which is symmetric; or admit a symmetric global solution. Three of them appear for a single cycle placed in three value spaces: a bounded line, an unbounded line and a circle. The unbounded line is contextual only possibilistically; the probabilistic form appears on the circle, for a candidate that beats every member of a cycle. Young and Levenglick's incompatibility of consistency with the Condorcet principle, read for jointly drawn winners, is at the first level: no rule that elects every Condorcet winner, deterministic or lottery-valued, is consistent in this sense, and the no-show theorem behaves the same way. Arrow's theorem is at the third level. Its scenario, with independence of irrelevant alternatives as non-contextuality, has the dictatorships as global solutions, and for three and four alternatives and any number of voters its empirical models are exactly their mixtures (Theorems 5 and 5′), a probabilistic Arrow theorem in which independence is required of the joint lottery on any set of pairs. Dividing by the voters' permutations moves it to the second level, and random dictatorship becomes strongly contextual: its hidden variable is the symmetry break. Exits from each level change what counts as a value: maximal lotteries are consistent ex ante, not ex post. Several statements are checked in the Lean proof assistant and the rest by exhaustive computation on small cases.

## 1. Introduction

The companion paper *Cycles and Twists* places a Condorcet cycle in three value spaces. On a bounded line no compatible model exists. On an unbounded line a compatible possibilistic model exists without a global placement, but no probabilistic one. On a circle the cycle is placed evenly and nothing is wrong. Those three outcomes are levels of a hierarchy familiar from contextuality (Abramsky and Brandenburger): failure of local consistency, contextuality, and consistency.

Social choice needs one more level, between contextuality and consistency. Arrow's problem has global solutions, the dictatorships, and what fails is that none of them treats the voters alike. This is a failure of symmetry, not of gluing. Distributed computing draws the same line between agreement tasks, impossible even when processes may use their identities, and symmetry-breaking tasks, trivial unless anonymity is required (Castañeda, Herlihy and Rajsbaum; Rajsbaum and Raventós-Pujol place Arrow's theorem on the symmetry-breaking side).

This paper states the four levels precisely (Section 2), places the value spaces and the main theorems of social choice in them (Sections 3–5), and describes the exits (Section 6). The results are elementary. The contribution is the sorting, a few small theorems that make it exact, and computations that check it.

## 2. Scenarios, models and symmetry

A **scenario** consists of a set of variables, a set of values for each, a family of finite sets of variables called **contexts**, and for each context C a set A_C of admissible joint values of the variables in C. Boundary conditions, such as unanimity, are part of A_C.

- A **global section** is an assignment of values to all variables whose restriction to every context is admissible.
- An **empirical model** is a family of probability distributions e_C on A_C, one per context, that is *compatible*: two contexts induce the same distribution on the variables they share (Abramsky and Brandenburger). A family is **weakly compatible** if this holds for each shared variable separately.
- An empirical model is **non-contextual** if it is the image of one distribution over global sections, and **strongly contextual** if no global section is consistent with its support.

A **symmetry** of the scenario is a group G acting on variables and values so that contexts go to contexts and admissible values to admissible values. A global section or a model is *symmetric* if G fixes it.

**Definition (levels).** Relative to G, a scenario is at

1. **local inconsistency** if it has no empirical model;
2. **contextuality** if it has empirical models but no global section;
3. **symmetry breaking** if it has global sections but none is symmetric;
4. **consistency** if it has a symmetric global section.

**Proposition 1 (division).** Let G be finite and the scenario at level 3. Average a global section s over G: the uniform mixture of the sections g·s, g ∈ G, is a symmetric empirical model. It is non-contextual, with the group element as hidden variable. Among symmetric objects it has no global explanation: restricted to symmetric models and symmetric sections, the scenario is at level 2.

*Proof.* Each g·s is a global section, and any mixture of global sections is a compatible family supported on admissible values. The uniform mixture is fixed by G. There is no symmetric global section by assumption. ∎

The proposition makes two readings exact. The fixed point of a symmetry acting on rules is the average of the rules that break it. And a symmetry-breaking obstruction is a contextuality obstruction whose only hidden variables are the breaks.

## 3. The template: one cycle in three value spaces

Take alternatives as variables, values in a set O with a relation "placed above", and as contexts the pairs, each requiring the winner of the pair in a tournament T to be placed above the loser (*Cycles and Twists*, Section 2). Let G be the cyclic renaming of a cycle a₁ ≻ … ≻ aₙ ≻ a₁, acting on the circle by rotation.

| Value space | Result in *Cycles and Twists* | Level |
|---|---|---|
| bounded line | no compatible model (Proposition 1) | 1 |
| unbounded line | compatible possibilistic model, no global section (Proposition 3); no probabilistic model (remark d) | 2 possibilistically, 1 probabilistically |
| circle | the evenly spaced placement, fixed by rotation (Proposition 2) | 4 |
| circle, a fourth alternative beating every member of the cycle | an empirical model (uniform placements), no global section (after Proposition 2) | 2 |

The definitions of Section 2 are probabilistic. On the unbounded line a probability distribution sees the placements only through a bounded increasing function, through which the line becomes a bounded interval, and the first row applies again. The circle is the consistent space for a single cycle but not for every tournament: it fits exactly the locally transitive ones (*Cycles and Twists*, after Proposition 2), and the last row is the smallest case outside them.

In its general form, checked in Lean (`lean/ValueSpaces.lean`), the bounded-line result needs only that every alternative in a set is beaten by some alternative in the set. The cycle need not close up. The hypothesis is a map of the alternatives into themselves without a fixed point, and the proof is "whatever is on top is beaten from above". This shape returns at level 1 in social choice.

## 4. Level 1: everything is beaten

**Deterministic consistency.** A rule is *consistent* if, whenever two disjoint electorates elect the same candidate, their union elects that candidate. A *Condorcet extension* elects the Condorcet winner whenever there is one.

**Theorem 2.** A consistent Condorcet extension never elects a candidate whom another candidate beats by majority. Hence there is none at a profile where every candidate is beaten, in particular at every profile with a majority cycle on three candidates.

This is Young and Levenglick's incompatibility in a sharper form. It is proved in Lean for finite electorates, ballots with ties and any number of candidates (`lean/Consistency.lean`). If x is elected at a profile of n voters and w beats x, the proof adds an electorate of 2n + 1 voters ranking x first and w second and 2n voters ranking w first and x second. By the Condorcet principle this electorate elects x, so by consistency the union of two copies of the profile with it elects x; but w is its Condorcet winner. *A Map of Voting Paradoxes* gives the same construction for vote shares.

**Joint draws.** For a lottery-valued rule, consistency can be read as a statement about winners drawn jointly: the winners of two electorates and of their union are drawn, each from its own lottery, so that whenever the two parts elect the same candidate the union elects that candidate too. Take the winner at each profile as a variable, two profiles together with a mixture of them as a context, consistency as the constraint and the Condorcet principle as boundary condition. A lottery-valued rule that is consistent in this sense is exactly a weakly compatible family on this scenario.

**Lemma 3 (joint draw).** For lotteries μ, ν and λ over the candidates, winners X ~ μ, Y ~ ν and Z ~ λ can be drawn jointly so that X = Y implies Z = X exactly when λ(a) ≥ μ(a) + ν(a) − 1 for every candidate a. (Proof in *Consistency as an Extension Problem*, Section 3b.)

**Theorem 4.** No rule that elects a Condorcet winner with certainty when there is one, deterministic or lottery-valued, is consistent for joint draws (vote shares, any number of candidates). The scenario is at level 1, even for weakly compatible families.

*Proof.* At a profile p without a Condorcet winner, let a receive positive probability. Theorem 2's construction, for vote shares, gives an electorate q with Condorcet winner a and a mixture of p with q whose Condorcet winner beats a. Lemma 3 then requires the probability of a at p to be at most zero. This holds for every candidate, which is impossible. ∎

**Participation.** For a lottery-valued rule, Moulin's participation condition read for joint draws asks that the winners without and with an added voter can be drawn jointly so that the voter never gets a worse winner. On a ranking such a draw exists exactly when the lottery with the voter stochastically dominates the lottery without, which is SD-participation. Brandt, Geist and Peters proved that no Condorcet-consistent rule satisfies SD-participation, which places the no-show theorem at level 1 as well (from four alternatives; with three, maximin satisfies participation).

In each case the proof has the shape of the bounded line: whatever candidate receives probability is beaten by one whose region blocks it.

## 5. Levels 2 and 3: Arrow's scenario

**The scenario.** Read the three pairs of three alternatives around the triangle; a ranking is a triple of bits, not all equal (*Cycles and Twists*, Section 5). For N voters take as variables the social decision on each pair for each pattern of the voters' bits on that pair, and as contexts the profiles. Two profiles share a variable when they agree on a pair. Requiring each variable to take one value in every context containing it is independence of irrelevant alternatives, the non-contextuality assumption of Kochen and Specker in this setting. Unanimity is the boundary condition, and G is the group of permutations of the voters. This is the formulation of aggregators as polymorphisms (Dokow and Holzman; Szegedy and Xu), and as a complex it is the input complex of Rajsbaum and Raventós-Pujol.

**Global sections.** The global sections are the dictatorships (Arrow; computed for two and three voters). They form one orbit of G, and none is symmetric: the scenario is at level 3.

**Empirical models.** Write the three pairs as issues 1, 2, 3 (ab, bc, ca). At a profile the voters' bits on issue j form a column, identified with the set of voters having bit 1. Let p_j(S) be the probability of social bit 1 on issue j when its column is S, and q_ij the probability that issues i and j both have social bit 1. Full compatibility says that q_ij depends only on the two columns of issues i and j.

**Theorem 5.** For three alternatives and any number of voters, every empirical model on Arrow's scenario is a mixture of dictatorships. There are weights λ_k ≥ 0 summing to 1 such that at every profile the lottery over rankings is that of drawing voter k with probability λ_k and adopting k's ranking.

*Proof.* At every profile the social triple is not all equal, so the probabilities of 000 and 111 vanish. By inclusion and exclusion,

  (∗) q₁₂ + q₂₃ + q₃₁ = p₁ + p₂ + p₃ − 1,

and, since issues 1 and 2 both at 1 force issue 3 to 0, q₁₂ ≤ 1 − p₃, together with the cyclic versions.

Fix columns A, B on issues 1 and 2. The voters' rankings force column 3 on A ∩ B (bit 0) and outside A ∪ B (bit 1) and leave it free elsewhere. Two choices are admissible:
- W* = complement of A ∩ B, the largest;
- W₀ = complement of A ∪ B, the smallest.

By full compatibility q₁₂(A, B) is the same at both profiles. At W*, the bound gives q₁₂(A, B) ≤ 1 − p₃(W*). At W₀, the cyclic bound for issues 2 and 3 gives q₂₃(B, W₀) ≤ 1 − p₁(complement of B ∩ W₀) = 1 − p₁(all) = 0 by unanimity, and likewise q₃₁(W₀, A) = 0. So (∗) gives

  q₁₂(A, B) = p₁(A) + p₂(B) + p₃(W₀) − 1.

With B empty, unanimity gives q₁₂ = 0 and hence p₁(A) = 1 − p₃(complement of A). With A empty, p₂(B) = 1 − p₃(complement of B). The cyclic argument gives the other identities, so all issues have the same function β with β(S) = 1 − β(complement of S). Now q₁₂(A, B) = β(A) + β(B) − β(A ∪ B), which is at least 0 and at most 1 − β(complement of A ∩ B) = β(A ∩ B). For disjoint A and B this gives β(A ∪ B) = β(A) + β(B), so β(S) is the sum of λ_k = β({k}) over k in S, and q₁₂(A, B) = β(A ∩ B).

The mixture of dictatorships with weights λ has the same single and pairwise probabilities. A distribution on the six admissible triples is determined by these, since with 000 and 111 excluded the remaining degree of freedom of a distribution on {0, 1}³ is fixed. So the two coincide at every profile. ∎

The proof is checked in Lean, step by step, for any finite set of voters (`lean/ProbabilisticArrow.lean`). There full compatibility is encoded by letting each single and pairwise probability be a function of the relevant columns only.

The proof uses full compatibility at exactly one point: q₁₂(A, B) is the same at the profiles with W* and W₀. A rule that is only weakly compatible may let this joint probability depend on the third column. The coin rule does so, and by the proof it must.

For more alternatives the scenario has a variable for each pair of alternatives and each column on it, and full compatibility says that for every set of pairs the joint lottery of the social comparisons on these pairs depends only on their columns.

**Theorem 5′.** For four alternatives and any number of voters, every empirical model on Arrow's scenario is a mixture of dictatorships.

*Proof.* (i) *Triples.* Restricted to the pairs of a triple of alternatives, the model is an empirical model of the three-alternative scenario, so by Theorem 5 it is a mixture of dictatorships with weights λ^T. If only voter k ranks x above y, the probability of x above y is λ^T_k for every triple T containing x and y, and by full compatibility it is the same for all of them. So the weights agree for triples sharing a pair, hence for all four triples.

(ii) *Three pairs determine the lottery.* A distribution on the 24 rankings of four alternatives is determined by its marginals on all sets of three pairs: the map to these marginals has rank 24. Up to renaming a set of three pairs is a triangle (a triple, covered by (i)), a star {ab, ac, ad} or a path {ab, bc, cd}. It remains to show that the lottery on a star and on a path is that of the mixture, at every profile.

(iii) *Completion.* Fix a star or a path S and columns on its three pairs. By full compatibility the lottery on S does not depend on the other three columns, so they may be chosen freely. Give every voter a ranking determined by its pattern of comparisons on S, by the following rules; a pattern lists the comparisons in the order of the pairs in S, 1 meaning the first-named alternative is above.

| pattern on S | star {ab, ac, ad} | path {ab, bc, cd} |
|---|---|---|
| 000 | bcda | dcba |
| 001 | bcad | cbad |
| 010 | bdac | bdca |
| 011 | bacd | bcad |
| 100 | cdab | adcb |
| 101 | cabd | acbd |
| 110 | dabc | abdc |
| 111 | abcd | abcd |

At the completed profile the voters use only rankings from the eight W of the rule. By (i) the lottery on each triple is the mixture of the voters' restricted rankings, so a ranking with positive probability has on every triple a restriction used by some voter. For both rules the only rankings whose four triple restrictions all occur in W are the rankings of W themselves, so the lottery is supported on W. On W the triple marginals determine the lottery, and they are those of the mixture. So at the completed profile the lottery is that of the mixture, hence also its marginal on S, and by full compatibility so is the lottery on S at the original columns. With (ii) this proves the theorem. ∎

The rules were found by linear programming over completions; the identities they rest on are finite and exact, and they use only (i) and full compatibility, not the number of voters (`scripts/symmetry/pin_certificate.py`; the search is `scripts/symmetry/pin_search.py`; working note *Theorem 5 for four alternatives*, `notes/theorem5-four-alternatives.md`). An earlier check by computation, for up to four voters, agrees (`scripts/symmetry/probabilistic_arrow.py`, part 4).

The completion is where positivity of probabilities enters, through the support. Linear relations alone do not suffice: neither unanimity on other pairs nor the triple lotteries determine the joint lottery of two disjoint pairs, since on rankings of four alternatives the triple marginals and the three joints of disjoint pairs together span only 18 of 24 dimensions. The joint lottery of ab and cd is a path with its middle comparison summed out. In the simplest instance every voter places c and d next to each other between a and b; the triple lotteries then put a and b at the extremes with probability 1, and "a above b and c above d" becomes "a above c above d", whose probability is the weight of the voters in both columns.

The scenario therefore has no contextual model; each has a hidden-variable explanation, and the hidden variable is a dictator.

**Division.** By Proposition 1, random dictatorship is a symmetric empirical model with no symmetric global explanation. By Theorems 5 and 5′, for three and four alternatives and any number of voters it is the only symmetric empirical model, since a symmetric mixture gives every voter the same weight. Divided by the voters' permutations, Arrow's scenario is at level 2, with random dictatorship strongly contextual.

**Weak compatibility.** Barberà and Sonnenschein's random social welfare functions satisfy independence of irrelevant alternatives one pair at a time, which is weak compatibility. Their coalition power is in general subadditive. From three voters on there are such rules that are not mixtures of dictatorships. The simplest, the *coin rule*, follows unanimity on a pair and otherwise gives probability ½. It exists for three to five alternatives and fails for some profiles with six. For three and four voters it admits no fully compatible choice of lotteries: the lottery on two pairs depends on the voters' comparisons on the third. For three and four alternatives and any number of voters, the gap between subadditive and additive power is therefore a gap of signalling, not of contextuality (Theorems 5 and 5′). With more alternatives the gap closes: McLennan proved that power is additive when there are at least six alternatives, and the failure of the coin rule at six is the computational trace of that threshold. Pattanaik and Peleg obtain additivity from four alternatives for stochastic choice from feasible sets under a regularity condition, and Nandeibam with nonimposition and monotonicity in place of the Pareto condition.

**At a single profile.** The pointwise form of level 3 is the isotropy lemma: a neutral rule sends a profile to an output fixed by the profile's stabiliser under renaming the alternatives. Conversely, on a finite set of profiles closed under renaming, such a rule exists if every stabiliser fixes an admissible output. The condition reproduces Moulin's existence condition for anonymous, neutral and resolute rules (m is not a sum of divisors of n exceeding 1), the condition gcd(n, m!) = 1 for Pareto-optimal winners and for rankings, and existence for weak orders and lotteries (computed for small m and n; *Where the Symmetry Goes*, Section 7). In Lean the three-voter case at the Condorcet profile uses only the two symmetries involved (`lean/ProfileFacts.lean`).

Gibbard–Satterthwaite can be written the same way, with pairs of profiles that differ in one voter's ballot as contexts and strategy-proofness as constraint. Its global sections with at least three outcomes are dictatorial, and random dictatorship is the symmetric model of Gibbard (1977). The detailed placement is not carried out here.

## 6. Exits

An exit changes what counts as a value and so moves a problem down the hierarchy.

| Problem | Level | Exit | What it costs |
|---|---|---|---|
| a cycle on a bounded line | 1 | close the line into a circle | a cyclic order instead of a ranking |
| consistency with the Condorcet principle | 1 | maximal lotteries, consistent ex ante: the lottery as a value in the simplex (Brandl, Brandt and Seedig) | the drawn winner is not consistent |
| participation with the Condorcet principle | 1 | maximal lotteries with lotteries compared by independent draws (Brandl, Brandt and Hofbauer) | SD-participation fails |
| Arrow, divided by the voters | 2 | random dictatorship | a hidden variable that breaks the symmetry |

The ex ante reading is not a weakening of the ex post one but a different statement. It is about lotteries as wholes, not about the winners drawn from them. That is why maximal lotteries satisfy population-consistency and elect every Condorcet winner, while Theorem 4 excludes both together for joint draws.

When can the symmetry be kept without fractions? For constraint languages the answer is known. The basic linear-programming relaxation, which requires only local consistency of distributions, decides every instance exactly when the language has symmetric polymorphisms of all arities (Kun, O'Donnell, Tamaki, Yoshida and Zhou). Read through Section 5, symmetric polymorphisms are anonymous aggregators that use the same rule on every pair. So the symmetry can be kept integrally for every size of electorate exactly when local consistency implies a global solution. For "not all equal" it cannot: the assignment ½ everywhere, the fixed point of reversing every preference, satisfies every relaxation and cannot be rounded.

## 7. Relation to other work

The hierarchy below the new level is that of Abramsky and Brandenburger, and the link between constraint satisfaction and local hidden variables is due to Abramsky, Gottlob and Kolaitis. Aggregation as polymorphisms is due to Dokow and Holzman and to Szegedy and Xu. Rajsbaum and Raventós-Pujol give a combinatorial-topology proof of Arrow's theorem by the index lemma and place it among symmetry-breaking tasks, and Felber, Hummes Flores and Rincon Galeana characterise task solvability by global sections of a task sheaf. Systems that signal, such as the coin rule, are the subject of Dzhafarov and Kujala's contextuality-by-default, which separates contextuality from direct influences of context and would give the coin rule a measure of contextuality beyond its signalling. For promise problems, where the symmetric fractional solution need only be rounded into a weaker target, symmetric polymorphisms and relaxations are studied by Brakensiek and Guruswami. On the probabilistic side, the results used are those of Barberà and Sonnenschein, McLennan, Brandl, Brandt and Seedig, Brandl, Brandt and Hofbauer, and Brandt, Geist and Peters. Group-theoretic existence conditions for anonymous and neutral rules are due to Moulin, Bubboloni and Gori, and Doğan and Giritligil. The companion papers *Cycles and Twists* and *Walls and Strategy* treat the topology of the cycle and the computability of strategy.

## 8. Status and open problems

| Statement | Status | Check |
|---|---|---|
| Proposition 1 (division) | proved here, elementary | |
| Value spaces at levels 1, 2, 4 | proved (*Cycles and Twists*) | `lean/ValueSpaces.lean` |
| Theorem 2 (consistent Condorcet extensions elect no beaten candidate) | proved; sharpens Young and Levenglick | `lean/Consistency.lean` |
| Lemma 3 (joint draw), Theorem 4 | proved here | `scripts/consistency/ex_post_consistency.py` |
| Participation at level 1 | cited (Brandt, Geist and Peters), equivalence with joint draws proved here | same script |
| Global sections of Arrow's scenario | cited (Arrow) | `scripts/symmetry/arrow_as_csp.py`, two and three voters |
| Theorem 5: empirical models of Arrow's scenario are mixtures of dictatorships | proved here, three alternatives, any number of voters | `lean/ProbabilisticArrow.lean` (any finite set of voters, following the proof step by step); `scripts/symmetry/probabilistic_arrow.py` (two and three voters) |
| Theorem 5′: the same for four alternatives | proved here, any number of voters, by a reduction to finitely many exact identities | `scripts/symmetry/pin_certificate.py` (the identities, in exact arithmetic); `scripts/symmetry/probabilistic_arrow.py`, part 4 (up to four voters, independently) |
| Coin rule: weakly but not fully compatible | computed | same script |
| Isotropy lemma and recovered existence conditions | proved; conditions computed | `scripts/symmetry/isotropy_check.py`; `lean/ProfileFacts.lean` for one case |
| Distributed-computing analogy, readings of exits | interpretation | |

**Open problems.**

1. Does Theorem 5 extend to five or more alternatives? Theorem 5′ gives the triple and four-alternative lotteries, and the question is whether full compatibility forces the whole lottery. The proof for four alternatives does not carry over as it stands: marginals on sets of three pairs leave a kernel of dimension 24 among the 120 rankings of five alternatives, and of 394 among the 720 of six. A proof along these lines needs completions for larger sets of pairs, with Theorem 5′ in place of Theorem 5.
2. Place Gibbard–Satterthwaite precisely: its scenario, its empirical models, and whether random dictatorship is the only symmetric one.
3. Give a single scenario with electorates and their extensions as contexts in which consistency and participation are both constraints, so that both level-1 theorems become the statement that it has no empirical model.
4. Find a topological invariant for each level: winding numbers and degrees are integer invariants at level 3 (Baryshnikov and Root; Rajsbaum and Raventós-Pujol), and the bounded line suggests a fixed-point index at level 1.

## References

- Abramsky, S. (2014). Contextual semantics: from quantum mechanics to logic, databases, constraints, and complexity. arXiv:1406.7386.
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Abramsky, S., Gottlob, G. and Kolaitis, P. G. (2013). Robust constraint satisfaction and local hidden variables in quantum mechanics. *IJCAI 2013*, 440–446.
- Arrow, K. J. (1963). *Social Choice and Individual Values*, 2nd ed. Yale University Press.
- Barberà, S. and Sonnenschein, H. (1978). Preference aggregation with randomized social orderings. *Journal of Economic Theory* 18, 244–254.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Brakensiek, J. and Guruswami, V. (2020). Symmetric polymorphisms and efficient decidability of promise CSPs. *SODA 2020*. arXiv:1907.04383.
- Brandl, F., Brandt, F. and Hofbauer, J. (2019). Welfare maximization entices participation. *Games and Economic Behavior* 114, 308–314.
- Brandl, F., Brandt, F. and Seedig, H. G. (2016). Consistent probabilistic social choice. *Econometrica* 84, 1839–1880.
- Brandt, F., Geist, C. and Peters, D. (2017). Optimal bounds for the no-show paradox via SAT solving. *Mathematical Social Sciences* 90, 18–27.
- Bubboloni, D. and Gori, M. (2016). Resolute refinements of social choice correspondences. arXiv:1506.06069.
- Castañeda, A., Herlihy, M. and Rajsbaum, S. (2012). An equivariance theorem with applications to renaming. *LATIN 2012*, LNCS 7256. arXiv:1102.4946.
- Doğan, O. and Giritligil, A. E. (2022). Anonymous and neutral social choice: a unified framework for existence results, maximal domains and tie-breaking. *Review of Economic Design*. doi:10.1007/s10058-021-00269-0.
- Dokow, E. and Holzman, R. (2010). Aggregation of binary evaluations. *Journal of Economic Theory* 145, 495–511.
- Dzhafarov, E. N., Kujala, J. V. and Larsson, J.-Å. (2015). Contextuality in three types of quantum-mechanical systems. *Foundations of Physics* 45, 762–782.
- Felber, S., Hummes Flores, B. and Rincon Galeana, H. (2025). A sheaf-theoretic characterization of tasks in distributed systems. arXiv:2503.02556.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics* 17, 59–87.
- Kun, G., O'Donnell, R., Tamaki, S., Yoshida, Y. and Zhou, Y. (2012). Linear programming, width-1 CSPs, and robust satisfaction. *ITCS 2012*.
- McLennan, A. (1980). Randomized preference aggregation: additivity of power and strategy proofness. *Journal of Economic Theory* 22, 1–11.
- Moulin, H. (1988). Condorcet's principle implies the no show paradox. *Journal of Economic Theory* 45, 53–64.
- Moulin, H. (1991). *Axioms of Cooperative Decision Making*. Cambridge University Press.
- Nandeibam, S. (2003). A reexamination of additivity of power in randomized social preference. *Review of Economic Design* 8, 293–299.
- Pattanaik, P. K. and Peleg, B. (1986). Distribution of power under stochastic social choice rules. *Econometrica* 54, 909–922.
- Rajsbaum, S. and Raventós-Pujol, A. (2025). A combinatorial topology approach to Arrow's impossibility theorem. *Social Choice and Welfare*. doi:10.1007/s00355-025-01609-7.
- Szegedy, M. and Xu, Y. (2015). Impossibility theorems and the universal algebraic toolkit. arXiv:1506.01315.
- Young, H. P. and Levenglick, A. (1978). A consistent extension of Condorcet's election principle. *SIAM Journal on Applied Mathematics* 35, 285–300.
- *Cycles and Twists*; *Walls and Strategy* (companion drafts, this repository).
- *A Map of Voting Paradoxes*, *Consistency as an Extension Problem*, *Where the Symmetry Goes*, *Contextuality and Symmetry* (working notes, this repository).
