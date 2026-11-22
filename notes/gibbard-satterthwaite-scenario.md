# Gibbard–Satterthwaite as a Scenario

*Working note, November 2026. Placement of Gibbard–Satterthwaite in the hierarchy of* Four Levels of Obstruction in Social Choice *(listed there as an open problem until this note).*

## Summary

Gibbard–Satterthwaite is written as a scenario in the sense of *Four Levels*, Section 2. The variables are the outcomes at the profiles. A context is a pair of profiles that differ in one voter's ballot, and its admissible values are the pairs of outcomes with which that voter gains by switching in neither direction. Unanimity is the boundary condition. Three results follow.

1. **Joint draws cost nothing beyond SD-strategy-proofness for whole rules** (Proposition 1). An empirical model is a random rule together with a joint draw for each context, and such draws exist exactly when the rule is strategy-proof in the stochastic-dominance sense. For an isolated pair of lotteries the joint draw is a strictly stronger requirement from four alternatives on. The intermediate ballots close the gap: the draw is built along a path of adjacent swaps.
2. **With unanimity and at least three alternatives**, the empirical models are exactly the mixtures of dictatorships (Corollary 2, from Gibbard 1977). Then:
   - none of them is contextual;
   - the scenario is at level 3, symmetry breaking;
   - random dictatorship is its only anonymous empirical model;
   - divided by the voters' permutations, the scenario is at level 2, like Arrow's.
3. **Without unanimity**, contextual empirical models exist already for one voter (Proposition 3). An example is the *random top two*: the voter's first or second choice, with probability ½ each. It is strategy-proof, but it is not a mixture of deterministic strategy-proof rules. Unanimity removes all such models.

The contrast with Arrow's scenario is in compatibility. Here contexts overlap in at most one variable, so weak and full compatibility coincide. In Arrow's scenario only full compatibility forces the mixtures of dictatorships.

## 1. The scenario

Fix a finite set of voters N and a finite set of alternatives A, with m = |A|. Ballots are strict rankings of A, and a profile assigns a ballot to each voter.

- **Variables.** One variable X_π per profile π, with values in A: the outcome at π.
- **Contexts.** The pairs {π, π′} of profiles that differ only in the ballot of one voter k. Write R for k's ballot in π and R′ for k's ballot in π′.
- **Admissible values.** The pairs (x, x′) with x ≽_R x′ and x′ ≽_{R′} x. With true preference R, voter k does not gain by reporting R′. With true preference R′, it does not gain by reporting R.
- **Boundary condition, unanimity.** If every voter ranks the same alternative a first in π, then X_π = a.

A global section is a deterministic rule that is strategy-proof and unanimous. For m ≥ 3 these are the dictatorships, by Gibbard (1973) and Satterthwaite (1975); unanimity makes the rule onto.

An empirical model consists of a lottery p_π on A for each profile, together with, for each context {π, π′}, a joint distribution of (X_π, X_π′) with marginals p_π and p_π′, supported on admissible pairs. Two contexts share at most one variable. Compatibility on shared sets of variables is therefore compatibility on single variables, so **weak and full compatibility coincide** in this scenario.

The symmetry group G is the permutations of the voters. Renaming the alternatives is not included: it is irrelevant with unanimity, since dictatorships are neutral, and only changes the placement without unanimity (Section 4).

## 2. Joint draws and stochastic dominance

A joint draw for the context {π, π′} gives for every upper set U of R

  P(X_π ∈ U) ≥ P(X_π′ ∈ U),

since X_π′ ∈ U and X_π ≽_R X_π′ imply X_π ∈ U. Similarly for the upper sets of R′. So an empirical model is SD-strategy-proof: no voter, with any von Neumann–Morgenstern utility consistent with its ranking, gains in expectation by misreporting. This is Gibbard's (1977) notion of strategy-proofness for decision schemes. The converse holds for whole rules, though not for isolated pairs.

**Proposition 1.** A family of lotteries (p_π) is the family of marginals of an empirical model of the scenario exactly when it is SD-strategy-proof.

The boundary condition concerns the lotteries only, so the statement holds with and without it.

*Proof.* Only the converse remains. Fix a context: profiles π and π′ differing in voter k's ballot, R in π and R′ in π′.

*(a) Adjacent swaps.* Suppose R′ is R with an adjacent pair x > y exchanged, and write q for the lottery at the second profile. The upper sets of R and R′ coincide except U ∪ {x} for R and U ∪ {y} for R′, where U is the set above the pair. SD in both directions gives equality on all common upper sets. Hence p and q agree outside {x, y}, p(x) + p(y) = q(x) + q(y), and from U ∪ {x}, p(x) ≥ q(x). A joint draw:
- every outcome other than x stays put;
- x stays x with conditional probability q(x)/p(x) and moves to y otherwise.

The move (x, y) is admissible, since x is above y in R and y is above x in R′.

*(b) Any two ballots.* Choose a shortest path R = R₀, R₁, …, R_ℓ = R′ of adjacent swaps; each swap exchanges a pair on which R and R′ disagree, and each such pair is exchanged once. The profiles along the path differ from π only in k's ballot. The rule assigns a lottery to each of them, and SD-strategy-proofness holds between neighbours. Chain the draws of (a), each conditional on the previous outcome. A step moves the outcome from x to y only when x is above y in R and y is above x in R′. So the outcome descends weakly in R and ascends weakly in R′ along the chain. The first and last outcomes form an admissible pair, and the chained draw has the right marginals. ∎

The argument resembles the pinning in Theorem 5′ of *Four Levels*: in both, a condition on one pair is reached through the intermediate objects of a path.

**The intermediate ballots are needed.** For an isolated pair of lotteries, SD in both directions does not give a joint draw from four alternatives on. Take R = a > b > c > d and R′ = b > c > d > a, with lotteries

  p = (¼, 0, ¼, ½) at R and q = (0, ¼, 0, ¾) at R′, on (a, b, c, d).

Both SD conditions hold. Under R and R′ the only admissible partner of c is c itself, but q(c) = 0 < p(c) = ¼. By Proposition 1, no SD-strategy-proof scheme of one voter contains this pair, which the linear program in `gs_joint_draws.py` confirms. In random samples, 33 of 1,286 pairs that are SD-ordered both ways have no joint draw.

For three alternatives no such example exists. Up to renaming, two rankings are at distance 1, 2 or 3:
- At distance 1, (a) applies.
- At distance 3 (reversal), the admissible pairs are those with x ≽_R x′. A monotone coupling exists because p SD-dominates q.
- At distance 2, say a > b > c against b > c > a, the admissible pairs are the diagonal and (a, b), (a, c). A draw exists when q(b) ≥ p(b) and q(c) ≥ p(c). The first is SD for R′. The second follows from SD for R on {a, b}.

## 3. With unanimity: mixtures of dictatorships

**Corollary 2.** Let m ≥ 3. The empirical models of the scenario with unanimity are exactly the mixtures of dictatorships.

*Proof.* By Proposition 1, the marginals of an empirical model form a unanimous SD-strategy-proof decision scheme. By Gibbard (1977), every strategy-proof decision scheme is a probability mixture of schemes, each of which is unilateral (depends on one voter's ballot only) or duple (puts all probability on a fixed pair of alternatives). Unanimity at a profile requires probability 1 on one alternative. It therefore holds for every component of positive weight.
- A duple component fails at a unanimous profile whose top is outside its pair, which exists for m ≥ 3.
- A unilateral component of voter i, at any ballot R, gives what it gives at the unanimous profile in which every voter has ballot R. That is R's top.

So every component is a dictatorship. Conversely, a mixture of dictatorships with weights λ is an empirical model. Draw the dictator once, with probability λ_i for voter i, and use the same draw in every context. If the dictator is not the switching voter, the two outcomes are equal. If it is, they are the tops of R and R′, which form an admissible pair. ∎

Consequences:

- **No contextual model.** Every empirical model is a mixture of global sections, with the dictator as hidden variable. This is the situation of Theorems 5 and 5′ for Arrow's scenario.
- **Level 3.** For two or more voters, no dictatorship is fixed by permuting the voters.
- **Random dictatorship** is the only anonymous empirical model, since an anonymous mixture gives every voter weight 1/|N|. Divided by the voters' permutations, the scenario is at level 2, and random dictatorship is an empirical model with no symmetric global explanation (*Four Levels*, Proposition 1).

Corollary 2 rests on Gibbard's theorem. The linear programs in `gs_scenario.py` check it directly on small cases, without that theorem. Over all empirical models with unanimity, they maximise:
- the total probability of outcomes that are no voter's top;
- the difference between voter 1's apparent weight at two profiles. The weight is measured as the probability of voter 1's top, at profiles where it is nobody else's top.

Both maxima are 0. This holds with joint draws and with SD-strategy-proofness alone, for m = 3 with two and three voters, and for m = 4 with two voters (SD form only, which suffices by Proposition 1).

## 4. Without unanimity: contextual models for one voter

Without unanimity the constant rules are global sections, and they are anonymous. Relative to the voters' permutations the scenario is then at level 4. Its empirical models are nonetheless richer than the mixtures of its global sections, already for a single voter.

For one voter, a deterministic strategy-proof rule picks the voter's best element of its range: f(R) ≽_R f(R′) for all R′ means that f(R) is R's best element of the range. So the global sections are the *range rules* "best element of S", one for each nonempty S ⊆ A.

**Proposition 3.** For m ≥ 3 and one voter, the random top two is an empirical model of the scenario without unanimity, and it is contextual. It gives the voter's first and second choice with probability ½ each.

*Proof.* Strategy-proofness: the truthful lottery has ½ on the top and 1 on the top two. Any report gives at most ½ to the top and at most 1 to the top two. By Proposition 1 the joint draws exist.

Suppose the scheme were a mixture of range rules.
- A set S missing two alternatives a and b gives an outcome outside the top two on a ballot that starts with a, b. Such a set cannot carry weight.
- The second choice b under top choice a is drawn only by S = A ∖ {a}. So each of these m sets has weight ½, and the weights sum to m/2 > 1. ∎

Gibbard's unilateral components need not be mixtures of deterministic strategy-proof rules, and the random top two is the simplest such case. That strategy-proof decision schemes reach beyond the mixtures of deterministic ones is not claimed as new. What Proposition 3 adds is the reading: those schemes are the contextual models of this scenario, and unanimity rules them out.

## 5. Comparison with Arrow's scenario

| | Arrow's scenario | Gibbard–Satterthwaite scenario |
|---|---|---|
| variables | social decision on each pair, per profile | outcome per profile |
| contexts | profiles (all pairs at one profile) | pairs of profiles differing in one ballot |
| overlap of contexts | many variables | at most one variable |
| global sections (m ≥ 3, with unanimity) | dictatorships | dictatorships |
| empirical models | mixtures of dictatorships (Theorems 5, 5′) | mixtures of dictatorships (Corollary 2) |
| needs full compatibility? | yes: the coin rule is weakly compatible (three to five alternatives) | no: weak = full |
| local condition | IIA per pair | joint draws, equivalent for whole rules to SD-strategy-proofness (Proposition 1) |
| without the boundary condition | (not examined here) | contextual models for one voter (Proposition 3) |
| level; divided by voters | 3; 2, random dictatorship the only symmetric model | 3; 2, random dictatorship the only symmetric model |

Both theorems sit at the same place in the hierarchy. The difference is how they get there. In Arrow's scenario the mixtures of dictatorships need full compatibility on overlapping contexts. In the Gibbard–Satterthwaite scenario the overlaps are single variables. The local condition can also be weakened from joint draws to stochastic dominance without changing the models.

## 6. Scope

- **Strict preferences only.** Gibbard (1977) works with strict orderings. Indifferences were not examined.
- **Corollary 2 cites Gibbard's characterisation** and uses only its "only if" direction. It is not reproved here. The direct checks are the linear programs for small cases in Section 3.
- **Not formalised in Lean.** Proposition 1 is elementary and would be a natural candidate: an adjacent-swap lemma plus chaining along a path. Proposition 3 is a short counting argument.
- **Only the probabilistic models.** Possibilistic models and strong contextuality, such as whether the random top two is strongly contextual, were not examined.
- **Renaming alternatives** was left out of G. With unanimity it changes nothing. Without unanimity it removes the constant rules as symmetric sections. The resulting placement was not worked out.
- **Arrow without unanimity**, the empty cell of the table, was not examined.

## 7. Checks

| Script (`scripts/strategy/`) | What it checks |
|---|---|
| `gs_scenario.py` | Linear programs over empirical models with unanimity (joint draws or SD-strategy-proofness): no probability on outcomes that are nobody's top, and no variation of a voter's weight. m = 3 with two and three voters, m = 4 with two voters |
| `gs_joint_draws.py` | Isolated pairs: always a joint draw for three alternatives in random samples, not always for four; the example of Section 2, exactly; that it does not extend to a whole scheme; the construction of Proposition 1 run on 33,120 pairs of ballots from 60 vertices of the one-voter polytope (m = 4), marginals and support exact to rounding |
| `gs_random_top_two.py` | The random top two: SD-strategy-proof (exact) and not a mixture of range rules (linear program), m = 3, 4, 5 |

## References

- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41, 587–601.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10, 187–217.
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
