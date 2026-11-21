# Theorem 5 for four alternatives

*Working note. It extends Theorem 5 of* Four Levels of Obstruction in Social Choice *(empirical models of Arrow's scenario are mixtures of dictatorships) from three to four alternatives, for any finite number of voters. Proof by a reduction to finitely many exact identities, checked by `scripts/symmetry/pin_certificate.py`.*

## Statement

**Theorem 5′.** For four alternatives and any finite set of voters, every empirical model on Arrow's scenario (full compatibility, unanimity) is a mixture of dictatorships: there are weights λ_k ≥ 0 summing to 1 such that at every profile the social ranking has the law of the ranking of voter k drawn with probability λ_k.

Throughout, a *column* on a pair xy is the set of voters ranking x above y. Full compatibility says: for every set S of pairs, the joint law of the social comparisons on S depends only on the columns of the pairs in S.

## Proof

**Step 1 (triples).** Restricted to the pairs of a triple, the model is an empirical model of the three-alternative scenario. By Theorem 5 its law at every profile is a mixture of dictatorships with weights λ^T. Two triples sharing a pair xy give the same probability of x above y when only voter k ranks x above y; that probability is λ^T_k. So the weights agree for triples sharing a pair, hence for all four triples: λ^T = λ.

**Step 2 (three pairs determine the law).** A probability law on the 24 rankings of four alternatives is determined by its marginals on all sets of three pairs (the marginal map has rank 24; exact check). Up to renaming, a set of three pairs is a triangle (a triple, covered by Step 1), a star {ab, ac, ad}, or a path {ab, bc, cd}. It remains to show that the law of the social comparisons on a star and on a path is the mixture law, at every profile.

**Step 3 (pinning by completion).** Fix a star or path S and arbitrary columns on its three pairs. By full compatibility the law on S is the same at every profile with these columns, so the other three columns may be chosen freely. Give every voter a full ranking determined only by its pattern of comparisons on S, by the following rules.

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

(A pattern lists the comparisons in the order of the pairs in S, 1 meaning the first-named alternative is above.)

At the completed profile, the voters use at most the eight rankings W of the rule. By Step 1, each triple's social law is the mixture law of the voters' restricted rankings. So a ranking with positive social probability has, on every triple, a restriction used by some voter of positive weight. For both rules, the only rankings all of whose triple restrictions occur in W are the eight rankings of W themselves. So the social law is supported on W, and for both rules the probability of each of the eight rankings is an exact rational combination of triple probabilities (for example, for the star, P(pattern 010) = P(b > d > c), the probability of that order on the triple bcd). Those identities hold whatever the weights, including weights zero for patterns that no voter has, and the mixture of dictatorships satisfies them. So the social law at the completed profile, and with it the law on S at the original columns, is the mixture law.

Steps 2 and 3 together give the theorem. ∎

## Remarks

- The step that the draft left open, the joint lottery of two disjoint pairs such as ab and cd, is the special case of a path with the middle comparison summed out. A one-line instance of the mechanism: let every voter place c and d next to each other between a and b. The triple laws then put a and b at the extremes and c, d in the middle with probability 1, so "a above b and c above d" is the event "a on top of acd and c above d". Its probability is the weight of the voters ranking a above c above d, that is, of the voters in both columns.
- The rules were found by linear programming over completions, then certified exactly. The certificates use only Step 1 and full compatibility, not the number of voters.
- **Five or more alternatives.** The same reduction does not suffice as it stands: laws on sets of three pairs leave a kernel of dimension 24 among the 120 rankings of five alternatives (394 of 720 for six). A proof along these lines needs pinning for larger sets of pairs, with completions that use the four-alternative result in place of Step 1.

## Check

`scripts/symmetry/pin_certificate.py` verifies, in exact rational arithmetic: that each rule matches its patterns; that the support closure of each rule is its eight rankings; the identity for each of the sixteen events; and the rank of the three-pair marginal map. `scripts/symmetry/pin_search.py` is the search that found the rules (linear programs over completions, with random tests of other weights).
