# Contextuality and Symmetry

*Working note. It joins thread A of the roadmap (consistency as non-contextuality) to thread B (where the symmetry goes) by writing aggregation as a constraint network in which both questions can be asked. The ingredients are published results: aggregation as polymorphisms (Dokow and Holzman; Szegedy and Xu), the basic linear-programming relaxation and symmetric polymorphisms (Kun, O'Donnell, Tamaki, Yoshida and Zhou), constraint satisfaction as contextuality (Abramsky; Abramsky, Gottlob and Kolaitis), and the distinction between agreement and symmetry-breaking tasks in distributed computing. The joining is interpretation; the small cases are computed.*

## 1. Aggregation as a scenario

Take three alternatives and read the three pairs around the triangle as *issues*, ab, bc and ca. A ranking is a triple of bits, one per issue; the six rankings are exactly the triples that are not all equal, and the two Condorcet cycles are 000 and 111. A profile of N voters is an N × 3 table whose rows are rankings. Its *column* on an issue is the vector of the N voters' bits on that issue.

Write the aggregation problem as a scenario in the sense of contextuality:

- a **variable** for each issue and each possible column: the social bit on that issue when the voters' bits are that column;
- a **context** for each profile, containing its three variables, one per issue;
- the **constraint** in each context: the three social bits are not all equal.

Two profiles share a variable when they have the same column on an issue. Requiring the variable to take one value, whatever context it appears in, is independence of irrelevant alternatives: the social decision on a pair may not depend on the rest of the profile. In the language of quantum foundations this is the assumption of non-contextuality: the value assigned to an observable does not depend on which compatible observables are measured with it.

A global assignment of the variables that satisfies every constraint is an aggregator satisfying independence of irrelevant alternatives; unanimity fixes the variables at the constant columns. This is the formulation of Dokow and Holzman and of Szegedy and Xu, in which aggregators are polymorphisms of the relation of admissible evaluations. It is also, as a complex, the input complex of Rajsbaum and Raventós-Pujol: their vertices, one for each pair and each sign vector of the voters, are the variables here, and their triangles are the profiles. Their chromatic maps are the global assignments.

## 2. Four kinds of solution

The script `scripts/symmetry/arrow_as_csp.py` computes the solutions for N = 2 and 3. The voters' permutations act on everything by permuting the rows of profiles.

- **Global assignments.** Exactly N, the dictatorships (Arrow's theorem; computed). They form one orbit under the voters' permutations, and no permutation fixes any of them.
- **Symmetric global assignments.** None (computed). A symmetric assignment depends on each column only through its number of ones, that is, on the share of voters who rank the first alternative of the pair above the second.
- **Symmetric local rule.** On a single issue, the unique anonymous, neutral and positively responsive rule is majority (May). Applied on every issue, it violates the constraint at the Condorcet profile, where every share is 2/3.
- **Symmetric fractional assignment.** Assign to each variable not a bit but the share itself. This is consistent in every context: the profile is itself a distribution over admissible triples with exactly these marginals. The distribution is the one obtained by choosing a voter at random and taking that voter's ranking, so this fractional solution is random dictatorship, the average of the N integral solutions (computed).

These are the three placements of *Where the Symmetry Goes*, now for rules and the voters' permutations instead of outcomes and renamings of alternatives. Majority keeps the symmetry locally and fails to glue (i). The dictators glue and break the symmetry (ii). Random dictatorship keeps the symmetry and glues, at the price of being fractional (iii). Section 2a shows that it is not the only fractional solution.

## 2a. Lottery-valued rules are empirical models

A *random social welfare function* assigns to each profile a lottery over rankings. It satisfies probabilistic independence of irrelevant alternatives if the probability that x is placed above y depends only on the voters' comparisons of x and y. It is Paretian if a comparison on which all voters agree is followed with probability one (Barberà and Sonnenschein). In the scenario of Section 1 such a rule is exactly an *empirical model* in the sense of Abramsky and Brandenburger. It gives a distribution over joint outcomes in each context, namely the lottery at that profile, supported on admissible outcomes, and its marginal on each variable is the same in every context containing it. Probabilistic independence of irrelevant alternatives is the no-signalling condition.

The model is non-contextual if it is the image of one distribution over global assignments. Every global assignment in the support must then satisfy every constraint and unanimity, so by Arrow's theorem it is a dictatorship. **The non-contextual random rules are therefore the mixtures of dictatorships.** Their marginals are additive: the probability that x is placed above y is the total weight of the voters who prefer x to y. A rule whose marginals are not additive is contextual, whatever joint lotteries it uses.

Barberà and Sonnenschein showed that a Paretian random rule with probabilistic independence is described by a power function on coalitions, which in general is subadditive, not additive. In the present terms, the gap between subadditive and additive power is the gap between contextual and non-contextual models. *(Reading of a known characterisation.)*

The gap is not empty. The following is computed with `scripts/symmetry/probabilistic_arrow.py`.

- **Two voters.** Every rule has additive marginals (three to five alternatives). On each pair this follows from complementarity: the probabilities of a comparison and of its reverse add to one, so the powers of the two voters add to one. The computation shows in addition that the split of power is the same on every pair.
- **Three or more voters.** There are rules with non-additive marginals. The simplest is the **coin rule**. A pair on which all voters agree is ranked as they agree; every other pair gets probability ½, with the lotteries chosen jointly so that the outcome is always a ranking.
  - Such lotteries exist for every unanimity order with three and four alternatives (checked for all), and with five alternatives on all sampled profiles.
  - With six alternatives they fail at a few unanimity orders. There the linear-ordering polytope has facets beyond the triangle inequalities.

The coin rule is anonymous, neutral, Paretian and independent in probability, and it is contextual: its power function gives every proper coalition ½.

This refines placement (iii). Random dictatorship, the symmetric fractional point of Section 2, is non-contextual: it is the average of the breaks, a mixture of integral solutions. The coin rule is symmetric, fractional and contextual: no mixture of integral solutions produces it.

The two differ visibly at the Condorcet profile abc, bca, cab:
- **Random dictatorship** puts probability 2/3 on each majority comparison and so keeps the direction of the cycle.
- **The coin rule** puts ½ on each comparison, realised by the uniform lottery over all six rankings. It erases the direction, as Borda does (*Where the Symmetry Goes*, observation 5).

*(Observation on small cases, not a theorem.)*

For the agreement-type theorems the comparison runs differently. *Consistency as an Extension Problem*, Section 3b, writes Young and Levenglick's problem as a scenario with electorates in the contexts: the variables are the winners at the profiles, a context is two profiles with a mixture of them, and the constraint is consistency. Read as a joint draw of winners, a lottery-valued rule that elects every Condorcet winner gives no empirical model on this scenario at all. The obstruction there is a failure of local consistency, stronger than contextuality, while for Arrow's problem empirical models exist and only their global sections are restricted. Maximal lotteries avoid the obstruction by being consistent ex ante, as values in the simplex, not ex post.

## 2b. The hidden variable is the symmetry break

Random dictatorship is non-contextual: it has a hidden-variable model, and the hidden variable is the identity of the dictator. Draw a voter, then let every pair be decided by that voter. The hidden variable is a symmetry break: it singles out one voter.

Now restrict the scenario to rules that treat voters alike. In this divided scenario the global assignments are the anonymous deterministic solutions, and there are none (Arrow's theorem with anonymity; computed for two and three voters in Section 2). Random dictatorship is still an empirical model of the divided scenario, since its probabilities depend on each column only through the number of ones in it. But it has no hidden-variable model there, since there is nothing to mix. It is strongly contextual in the divided scenario, as is every symmetric random rule, the coin rule included.

So the same object is non-contextual or contextual depending on whether its hidden variables may break the symmetry. In that sense a symmetry-breaking obstruction is a contextuality obstruction whose only hidden variables are the breaks. The isotropy lemma of *Where the Symmetry Goes*, Section 7, says the same at a single profile: a neutral rule cannot output anything that its stabiliser moves, and a hidden variable that names a dictator is such an output. *(Interpretation of computed and cited facts.)*

## 3. Agreement and symmetry breaking

"Fractional but not integral" is the constraint form of contextuality. In Abramsky's formulation, a scenario is contextual when local data that agree on overlaps admit no global assignment. Abramsky, Gottlob and Kolaitis relate local hidden variables to robust satisfiability of constraint networks. Here the fractional assignment is a family of distributions, one per context, with agreeing marginals, and the question is whether an integral assignment exists.

The aggregation problem then shows a distinction that distributed computing draws between two kinds of task.

- **The problem without symmetry** has integral solutions: the dictators. It is not contextual.
- **The problem divided by the symmetry**, whose solutions are the symmetric assignments, has a fractional solution and no integral one. It is contextual.

A symmetry-breaking problem is one that becomes contextual only after division by its symmetry. An agreement problem is contextual already. In distributed computing, consensus cannot be solved even by protocols that use process identities; the impossibility results for agreement tasks are proved by connectivity and Sperner-type arguments. Weak symmetry breaking is trivial if identities may be used, so the requirement of anonymity is part of the task. As Castañeda, Herlihy and Rajsbaum put it, <q>to rule out trivial solutions any protocol for WSB must be anonymous</q>, and the impossibility is proved with an equivariance argument and the index lemma. Arrow's theorem has the form of weak symmetry breaking: the non-dictatorship condition is what rules out the trivial solutions.

The same distinction sorts theorems of social choice. Young and Levenglick's theorem has the agreement form. The incompatibility of the Condorcet principle with consistency over electorates holds for all rules, not only for symmetric ones (for three candidates, every Condorcet extension fails from eight voters; Brandt, Dong and Peters). No break of the cycle glues (*Consistency as an Extension Problem*, blocking lemma), so there is no global solution at all; read ex post, there is not even a locally consistent probabilistic one (ibid., Section 3b). Moulin's no-show theorem is of the same kind. Arrow's and the Gibbard–Satterthwaite theorems, and Moulin's condition for anonymous, neutral and resolute rules, have the symmetry-breaking form: solutions exist and none is symmetric. This refines observation 2 of *Where the Symmetry Goes*: the two-family theorems are the agreement-type obstructions, and the one-family theorems with a dictator are the symmetry-breaking ones. *(Interpretation.)*

## 3a. A hierarchy of obstructions

Collected, the results of this note and of *Consistency as an Extension Problem* sort the obstructions into four levels. They are the levels of Abramsky and Brandenburger's hierarchy, with symmetry breaking added between contextuality and consistency. They are also the three value spaces of *Cycles, Twists and Walls*, Section 3, with the circle split into two cases.

| Level | What exists | Value spaces (*Cycles, Twists and Walls* §3) | Social choice |
|---|---|---|---|
| Local inconsistency | no empirical model | bounded line (Proposition 1): whatever is on top is beaten from above | Young–Levenglick read ex post: whatever candidate receives probability is blocked; the no-show theorem read ex post (with four or more alternatives; with three, maximin satisfies participation) |
| Contextuality | empirical models, no global section | unbounded line (Proposition 3) | symmetric random rules in the scenario divided by the voters' permutations; the coin rule also in the full scenario |
| Symmetry breaking | global sections, none symmetric | | Arrow (dictatorships), Gibbard–Satterthwaite, Moulin's condition for anonymous and neutral rules |
| Consistency | a symmetric global section | circle (Proposition 2): the evenly spaced placement | for instance, scoring rules for consistency over electorates, at the price of the Condorcet principle |

Exits move a problem down the table by changing what counts as a value. Maximal lotteries move Young–Levenglick from the first level to the last by reading consistency ex ante, with the lottery as a value. Random dictatorship moves Arrow's problem from the third level to a non-contextual model, at the price of a hidden variable that breaks the symmetry. *(Interpretation; the placements in the table are the computed and cited results above.)*

## 4. When can the symmetry be kept? The linear-programming bridge

For a constraint language Γ, the *basic LP relaxation* of an instance assigns to every variable a distribution over values and to every constraint a distribution over its admissible tuples, with agreeing marginals. This is the relaxation in which only local consistency of distributions is required; in the language of contextuality, it asks for a compatible family of local distributions. Kun, O'Donnell, Tamaki, Yoshida and Zhou proved that the basic LP relaxation correctly decides every instance of CSP(Γ) exactly when Γ has symmetric polymorphisms of every arity.

Read through Section 1, a symmetric polymorphism of arity N is an anonymous aggregator for N voters that uses the same rule on every issue. Rounding a fractional solution whose values have denominator N by such a polymorphism is electing by an anonymous rule from vote shares. The theorem then says that the symmetry can be kept integrally for every size of electorate exactly when local consistency of distributions always implies a global solution. Keeping the symmetry and passing from fractional to integral are the same problem.

For the relation "not all equal" the relaxation fails in a visible way. Assigning ½ to every variable, and the uniform distribution over the six admissible triples to every constraint, is consistent for every instance, satisfiable or not. The point ½ is the fixed point of reversing every preference, the bit flip that exchanges the two cycles (*Cycles, Twists and Walls*, §5). Placement (iii) is therefore always available in the relaxation and cannot be rounded. This agrees with Arrow's theorem for anonymous rules, with the computation of Section 2, and with the fact that satisfiability of not-all-equal constraints is NP-complete.

On this reading, the observation that the exits from impossibility are convexifications (*Where the Symmetry Goes*, observation 4) has a converse: the convexification can be undone without breaking the symmetry exactly when symmetric polymorphisms of all arities exist. *(Reading of a known theorem.)*

## 5. Where earlier statements sit

**Binary encoding.** *Cycles, Twists and Walls*, remark (a) of Section 3, says that recording only the winner of each pair makes a Condorcet cycle a constraint violation and not contextuality. That concerns a single profile. Over the network of all profiles, with independence of irrelevant alternatives as non-contextuality, the symmetric aggregation problem is contextual in the constraint sense of Section 3, and Section 2a gives random rules, such as the coin rule, that are contextual in the probabilistic sense of Abramsky and Brandenburger. The two statements concern different scenarios. The unbounded line of Proposition 3 places the obstruction in the value space of one profile; the network here places it in the space of rules.

**Two directions of non-contextuality.** The roadmap asked how consistency over electorates relates to independence of irrelevant alternatives. In the present terms, independence says that aggregation commutes with restricting a profile to a subset of alternatives: the decision on a pair is computed from the restriction to that pair. Consistency says that aggregation respects joining electorates: winners shared by the parts are the winners of the whole. One is a locality condition in the direction of alternatives, the other a gluing condition in the direction of voters. Together they resemble the two axioms of a sheaf. The two axes of *A Map of Voting Paradoxes* (linearity in voters, pairwise structure) are these two directions. *(Interpretation; not yet a theorem.)*

**Rajsbaum and Raventós-Pujol.** Their counterexample domain, in which no voter ranks C between A and B, removes contexts from the scenario. Fewer constraints admit more global assignments, among them a non-dictatorial one that splits decision power along a clone set (*Where the Symmetry Goes*, observation 7). The fact that homeomorphic domains can differ in possibility is the statement that solvability depends on the scenario, which sets are contexts, and not only on the space they cover.

## 6. Open questions

1. *A contextual fraction for aggregation.* By Section 2a, a Paretian random rule with probabilistic independence has a well-defined contextual fraction in the sense of Abramsky, Barbosa and Mansfield: the largest weight of a mixture of dictatorships that fits inside it, subtracted from one. How does it relate to the subadditivity of Barberà and Sonnenschein's power function, is the coin rule maximally contextual among symmetric rules, and is there a non-additive rule for every number of alternatives?
2. *Relaxing locality in steps.* Rules that look at more than one pair, such as Borda, which uses each voter's full ranking, are contextual in the sense of Section 1. Stronger relaxations than the basic LP (the Sherali–Adams hierarchy) correspond to consistency over larger sets of variables. Is there a hierarchy of rules seeing k issues at a time, matching the levels of the relaxation, with Saari's intensity form of independence as an early level?
3. *Agreement-type theorems in topological form.* If Young–Levenglick is of agreement type, is there a Sperner-type proof of it, as there is an index-type proof of Arrow's theorem?
4. *Neutral versus non-neutral.* The bridge of Section 4 uses polymorphisms that apply the same rule to every issue, that is, neutral rules. Arrow's theorem allows different rules on different issues. The multi-sorted version of the bridge should be stated and checked.

## References

- Abramsky, S. (2014). Contextual semantics: from quantum mechanics to logic, databases, constraints, and complexity. arXiv:1406.7386.
- Abramsky, S., Barbosa, R. S. and Mansfield, S. (2017). Contextual fraction as a measure of contextuality. *Physical Review Letters* 119, 050504.
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Abramsky, S., Gottlob, G. and Kolaitis, P. G. (2013). Robust constraint satisfaction and local hidden variables in quantum mechanics. *IJCAI 2013*, 440–446.
- Barberà, S. and Sonnenschein, H. (1978). Preference aggregation with randomized social orderings. *Journal of Economic Theory* 18, 244–254.
- Brandt, F., Dong, C. and Peters, D. (2024). Condorcet-consistent choice among three candidates. arXiv:2411.19857.
- Castañeda, A., Herlihy, M. and Rajsbaum, S. (2012). An equivariance theorem with applications to renaming. *LATIN 2012*, LNCS 7256. arXiv:1102.4946.
- Dokow, E. and Holzman, R. (2010). Aggregation of binary evaluations. *Journal of Economic Theory* 145, 495–511.
- Felber, S., Hummes Flores, B. and Rincon Galeana, H. (2025). A sheaf-theoretic characterization of tasks in distributed systems. arXiv:2503.02556.
- Herlihy, M., Kozlov, D. and Rajsbaum, S. (2013). *Distributed Computing Through Combinatorial Topology*. Morgan Kaufmann.
- Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics* 17, 59–87.
- Kun, G., O'Donnell, R., Tamaki, S., Yoshida, Y. and Zhou, Y. (2012). Linear programming, width-1 CSPs, and robust satisfaction. *ITCS 2012*.
- May, K. O. (1952). A set of independent necessary and sufficient conditions for simple majority decision. *Econometrica* 20, 680–684.
- Moulin, H. (1988). Condorcet's principle implies the no show paradox. *Journal of Economic Theory* 45, 53–64.
- Rajsbaum, S. and Raventós-Pujol, A. (2025). A combinatorial topology approach to Arrow's impossibility theorem. *Social Choice and Welfare*. doi:10.1007/s00355-025-01609-7.
- Szegedy, M. and Xu, Y. (2015). Impossibility theorems and the universal algebraic toolkit. arXiv:1506.01315.
- Young, H. P. and Levenglick, A. (1978). A consistent extension of Condorcet's election principle. *SIAM Journal on Applied Mathematics* 35, 285–300.
