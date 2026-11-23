# Four Levels of Obstruction in Social Choice

## Inconsistency, contextuality and symmetry breaking

*Draft, November 2026.*

## Abstract

Impossibility theorems of social choice are usually stated as the incompatibility of a list of axioms. We sort them instead by how they fail, in the language of sheaf-theoretic contextuality extended by a symmetry group. A scenario can admit no locally consistent model at all; admit locally consistent models but no global solution; admit global solutions none of which is symmetric; or admit a symmetric global solution. Three of them appear for a single cycle placed in three value spaces: a bounded line, an unbounded line and a circle. The unbounded line is contextual only possibilistically; the probabilistic form appears on the circle, for a candidate that beats every member of a cycle. Young and Levenglick's incompatibility of consistency with the Condorcet principle, read for jointly drawn winners, is at the first level: no rule that elects every Condorcet winner, deterministic or lottery-valued, is consistent in this sense, and the no-show theorem behaves the same way. For finite electorates and three alternatives the same scenario passes through all four levels as the electorate grows, and each step down is caused by the Condorcet profile. Arrow's theorem is at the third level. Its scenario, with independence of irrelevant alternatives as non-contextuality, has the dictatorships as global solutions, and for any number of alternatives and voters its empirical models are exactly their mixtures (Theorems 5 and 5′), a probabilistic Arrow theorem in which independence is required of the joint lottery on any set of pairs. Dividing by the voters' permutations moves it to the second level, and random dictatorship becomes strongly contextual: its hidden variable is the symmetry break. Exits from each level change what counts as a value: maximal lotteries are consistent ex ante, not ex post. Several statements are checked in the Lean proof assistant and the rest by exhaustive computation on small cases.

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

**Finite electorates.** Theorem 4 concerns vote shares, so electorates of every size. With electorates of at most n voters the scenario is finite, and for three alternatives and anonymous rules its level can be computed for each n (*Consistency as an Extension Problem*, Sections 3c and 3d). Take as symmetry the renamings of the alternatives.

| Voters | Level | What exists | Obstruction |
|---|---|---|---|
| up to 2 | 4 | a neutral consistent Condorcet extension | |
| 3 to 7 | 3 | consistent Condorcet extensions, none neutral | isotropy at the Condorcet profile: a neutral winner would be fixed by the 3-cycle |
| 8 | 2 | empirical models, no global section | a case split at the Condorcet profile |
| 9 and more | 1 | no weakly compatible family | the blocking lemma at one profile |

*(Computed. At eight voters the empirical models agree on every pair of profiles shared by two joins; since there is no global section, each of them is strongly contextual.)*

The thresholds of eight and nine voters are known for set-valued rules. Brandt, Dong and Peters show that every Condorcet extension violates subset-reinforcement (a candidate chosen in both parts is chosen in the union) from nine voters, and that every anonymous one violates reinforcement from eight. Their proofs are the two obstructions of the table.

- **Nine voters.** Let q be the Condorcet profile doubled. For each candidate x there is a three-voter electorate p_x with Condorcet winner x such that p_x + q has as Condorcet winner the candidate that beats x in q. Lemma 3 with L(p_x)(x) = 1 gives L(q)(x) ≤ L(p_x + q)(x) = 0, for each x, against Σ_x L(q)(x) = 1. This is Brandt, Dong and Peters' proof of subset-reinforcement summed over the three renamings, and the linear program finds it as the certificate of least weight. It applies to lotteries because, on a join with a Condorcet part, Lemma 3 says exactly that the supports satisfy subset-reinforcement.
- **Eight voters.** No profile is blocked on its own. A minimal unsatisfiable set of profiles has ten members: the Condorcet profile Q0, six four-voter profiles with two unbeaten candidates and three eight-voter joins of them. If Q0 elects x, two of the four-voter profiles are pushed by their joins with Q0 onto the candidate that beats x. Their join is also Q0 joined with a five-voter electorate whose Condorcet winner is x, and so it must elect x. A deterministic rule can resolve a tie once and use the resolution as a witness. A lottery can split it, so it needs a direct witness and fails one voter later.

Each step down the table is caused by the same profile, and each obstruction is closer to a single point than the one before.

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

**Theorem 5′.** For any number of alternatives and any number of voters, every empirical model on Arrow's scenario is a mixture of dictatorships.

*Proof.* By induction on the number m of alternatives, from Theorem 5 at m = 3. Let m ≥ 4.

(i) *Sub-models.* Restricted to the pairs of any m − 1 alternatives, the model is an empirical model of the scenario on them, hence a mixture of dictatorships. If only voter k ranks x above y, the probability of x above y is the weight of k in every such mixture containing x and y, and by full compatibility it is the same for all of them. So the weights agree for sets sharing a pair, hence for all such sets, and the lottery on any set of pairs touching at most m − 1 alternatives is that of one mixture, with weights λ.

(ii) *A ranking is an event on a path.* Fix a profile and a ranking t, and name the alternatives so that t is a₁ > a₂ > … > aₘ. The social ranking is t exactly when a_i is above a_{i+1} for every i < m, so by full compatibility the probability of t depends only on the columns of these m − 1 pairs. The voters ranking t are exactly the voters in all of these columns. It therefore suffices to find one profile with these columns at which the probability of t is the total weight of the voters ranking t.

(iii) *Completion.* Give every voter a ranking with the same comparisons on the path, chosen so that a voter who ranks a₂ above both a₁ and a₃, or below both, ranks a₃ above a₁. This is possible, since the comparisons on the path force a₁ above a₃ only through a₁ above a₂ above a₃. At the completed profile a voter ranks a₁ above a₃ only if it ranks a₁ above a₂ above a₃.

(iv) *Pinning.* Let T be the alternatives other than a₂, and o the restriction of t to T, that is a₁ > a₃ > a₄ > … > aₘ. A voter whose restriction to T is o ranks a₁ above a₃, hence by (iii) a₁ above a₂ above a₃, hence ranks t. By (i) the probability of o on T is therefore the total weight of the voters ranking t. Every other ranking σ with restriction o on T places a₂ above both or below both of a₁ and a₃, with a₁ above a₃. Let U be the alternatives other than aₘ; since m ≥ 4 it contains a₁, a₂ and a₃. By (iii) no voter has the restriction of σ to U, so by (i) that restriction has probability zero, and so has σ. The probability of t equals that of o on T, which is the total weight of the voters ranking t. ∎

At the completed profile the step is a one-term identity, P(a₁ > a₂ > … > aₘ) = P(a₁ > a₃ > … > aₘ on the alternatives other than a₂); for four alternatives, P(a > b > c > d) = P(a > b > d). The proof uses unanimity only through Theorem 5, and full compatibility only to pass to sub-models and to the completed profile. The completion breaks a symmetry: it fixes the orientation "a₃ above a₁" wherever the path leaves it open, so it is not invariant under reversing all preferences. On the cases computed, completions that keep this symmetry leave a parity class unresolved and do not pin the probability (working note *Theorem 5 for any number of alternatives*). Theorem 5 is the case m = 3 of the same idea: there the joint probability of two issues is evaluated at the smallest admissible third column, where unanimity makes the other terms vanish; in the step the completion makes them vanish through the support.

The proof is checked in Lean as a whole, for any finite sets of alternatives (at least three) and voters: the pinning step (iv) in `lean/PathPinning.lean`, the sub-models, the use of full compatibility, the completion (moving a₁ to directly below a₃) and the induction in `lean/ArrowGeneral.lean`, and the passage to Theorem 5 in `lean/ArrowBase.lean` (theorem `theorem5'`). The step was found by computation, and the computations now serve as independent checks: exact checks along paths for m ≤ 10 (`scripts/symmetry/pin_path_certificate.py`, `pin_path_greedy.py`); a linear-programming check of the argument for m ≤ 6 (`path_proof_check.py`); an earlier, longer form of the induction for m ≤ 6, with completion rules for every shape of m − 1 pairs, closed and identified supports, and determination of the distribution by its marginals on sets of m − 1 pairs (`pin_certificate_m.py`, `pin_rules.json`, and independently `pin_independent_check.py`); and four alternatives with up to four voters (`probabilistic_arrow.py`, part 4).

The completion is where positivity of probabilities enters, through the support. Linear relations alone do not suffice: neither unanimity on other pairs nor the triple lotteries determine the joint lottery of two disjoint pairs, since on rankings of four alternatives the triple marginals and the three joints of disjoint pairs together span only 18 of 24 dimensions. The joint lottery of ab and cd is a path with its middle comparison summed out. In the simplest instance every voter places c and d next to each other between a and b; the triple lotteries then put a and b at the extremes with probability 1, and "a above b and c above d" becomes "a above c above d", whose probability is the weight of the voters in both columns.

The scenario therefore has no contextual model; each has a hidden-variable explanation, and the hidden variable is a dictator.

**Division.** By Proposition 1, random dictatorship is a symmetric empirical model with no symmetric global explanation. By Theorems 5 and 5′, for any number of alternatives and voters it is the only symmetric empirical model, since a symmetric mixture gives every voter the same weight. Divided by the voters' permutations, Arrow's scenario is at level 2, with random dictatorship strongly contextual.

**Weak compatibility.** Barberà and Sonnenschein's random social welfare functions satisfy independence of irrelevant alternatives one pair at a time, which is weak compatibility. Their coalition power is in general subadditive. From three voters on there are such rules that are not mixtures of dictatorships. The simplest, the *coin rule*, follows unanimity on a pair and otherwise gives probability ½. It exists for three to five alternatives and fails for some profiles with six. For three and four voters it admits no fully compatible choice of lotteries: the lottery on two pairs depends on the voters' comparisons on the third. For any number of alternatives and voters, the gap between subadditive and additive power is therefore a gap of signalling, not of contextuality (Theorems 5 and 5′). With six or more alternatives the gap is empty: McLennan proved that power is additive when there are at least six alternatives, and the failure of the coin rule at six is the computational trace of that threshold. Pattanaik and Peleg obtain additivity from four alternatives for stochastic choice from feasible sets under a regularity condition, and Nandeibam with nonimposition and monotonicity in place of the Pareto condition.

**At a single profile.** The pointwise form of level 3 is the isotropy lemma: a neutral rule sends a profile to an output fixed by the profile's stabiliser under renaming the alternatives. Conversely, on a finite set of profiles closed under renaming, such a rule exists if every stabiliser fixes an admissible output. The condition reproduces Moulin's existence condition for anonymous, neutral and resolute rules (m is not a sum of divisors of n exceeding 1), the condition gcd(n, m!) = 1 for Pareto-optimal winners and for rankings, and existence for weak orders and lotteries (computed for small m and n; *Where the Symmetry Goes*, Section 7). In Lean the three-voter case at the Condorcet profile uses only the two symmetries involved (`lean/ProfileFacts.lean`).

**Gibbard–Satterthwaite.** The scenario has the outcomes at the profiles as variables, the pairs of profiles that differ in one voter's ballot as contexts, and as admissible values the pairs of outcomes with which that voter gains by switching in neither direction (working note *Gibbard–Satterthwaite as a Scenario*). Contexts share at most one variable, so weak and full compatibility coincide. The joint draws on contexts are, for whole rules, equivalent to strategy-proofness in the stochastic-dominance sense: the draw is built along a path of adjacent swaps of the ballot, although for an isolated pair of lotteries it is a strictly stronger requirement from four alternatives on. With unanimity and at least three alternatives, Gibbard's (1977) characterisation then makes the empirical models exactly the mixtures of dictatorships, as for Arrow's scenario: the scenario is at level 3, random dictatorship is its only anonymous model, and divided by the voters it is at level 2. Without unanimity there are contextual models already for one voter, such as the voter's first or second choice with probability ½ each.

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
| Finite electorates through all four levels (three alternatives) | computed; the certificates at 8 and 9 voters are Brandt, Dong and Peters' proofs | `scripts/consistency/yl_certificates.py`, `electorate_scenario.py` |
| Global sections of Arrow's scenario | cited (Arrow) | `scripts/symmetry/arrow_as_csp.py`, two and three voters |
| Theorem 5: empirical models of Arrow's scenario are mixtures of dictatorships | proved here, three alternatives, any number of voters | `lean/ProbabilisticArrow.lean` (any finite set of voters, following the proof step by step); `scripts/symmetry/probabilistic_arrow.py` (two and three voters) |
| Theorem 5′: the same for any number of alternatives | proved here, any number of voters, by induction | `lean/ArrowBase.lean` (`theorem5'`, with `ArrowGeneral.lean`, `PathPinning.lean`); `scripts/symmetry/pin_path_certificate.py` (m ≤ 10), `path_proof_check.py` (m ≤ 6); earlier form, m ≤ 6: `pin_certificate_m.py`, independently `pin_independent_check.py`; `probabilistic_arrow.py`, part 4 (four alternatives, up to four voters) |
| Coin rule: weakly but not fully compatible | computed | same script |
| Gibbard–Satterthwaite scenario: joint draws equivalent to SD-strategy-proofness for whole rules; with unanimity the models are the mixtures of dictatorships | proved (the second from Gibbard 1977) | `lean/JointDraws.lean` (first part); `scripts/strategy/gs_joint_draws.py`, `gs_scenario.py` (three alternatives with two and three voters, four with two) |
| Gibbard–Satterthwaite without unanimity: contextual models for one voter | proved | `scripts/strategy/gs_random_top_two.py` |
| Isotropy lemma and recovered existence conditions | proved; conditions computed | `scripts/symmetry/isotropy_check.py`; `lean/ProfileFacts.lean` for one case |
| Distributed-computing analogy, readings of exits | interpretation | |

**Open problems.**

1. Under weak compatibility, rules beyond the mixtures exist for three to five alternatives and not from six on (McLennan): how far from the mixtures can they be, measured by their signalling?
2. A single scenario with electorates and their extensions as contexts, in which consistency and participation are both constraints, is given in *Consistency as an Extension Problem*, Section 3c. Both level-1 theorems are statements about its sub-scenarios. For three alternatives the combination fails from the same electorate sizes as consistency alone: 8 voters for deterministic rules, 9 for lotteries drawn jointly. At eight voters its weakly compatible families can be made empirical models, so the joins pass through all four levels (Section 4). Open: whether from four alternatives on the combination fails for smaller electorates than either constraint alone, and the levels for four alternatives.
3. Find a topological invariant for each level: winding numbers and degrees are integer invariants at level 3 (Baryshnikov and Root; Rajsbaum and Raventós-Pujol), and the bounded line suggests a fixed-point index at level 1.

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
- Brandt, F., Dong, C. and Peters, D. (2024). Condorcet-consistent choice among three candidates. arXiv:2411.19857.
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
