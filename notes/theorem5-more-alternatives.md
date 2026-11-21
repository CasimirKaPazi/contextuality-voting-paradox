# Theorem 5 for four, five and six alternatives

*Working note. It extends Theorem 5 of* Four Levels of Obstruction in Social Choice *(empirical models of Arrow's scenario are mixtures of dictatorships) from three alternatives to four, five and six, for any finite number of voters. The proof is an induction on the number of alternatives whose step reduces, for each m, to finitely many exact checks; they are carried out for m = 4, 5, 6 by `scripts/symmetry/pin_certificate_m.py` from the rules in `scripts/symmetry/pin_rules.json`. Section "Symmetry and uniform rules" records what is known towards all m.*

## Statement

**Theorem 5′.** For m ≤ 6 alternatives and any finite set of voters, every empirical model on Arrow's scenario (full compatibility, unanimity) is a mixture of dictatorships: there are weights λ_k ≥ 0 summing to 1 such that at every profile the social ranking has the law of the ranking of voter k drawn with probability λ_k.

A *column* on a pair xy is the set of voters ranking x above y. Full compatibility says: for every set S of pairs, the joint law of the social comparisons on S depends only on the columns of the pairs in S.

## The induction step

Let m ≥ 4 and assume the theorem for m − 1 alternatives (for m = 4 this is Theorem 5).

**Step 1 (sub-models).** Restricted to any m − 1 alternatives, the model is an empirical model of the scenario on those alternatives, hence a mixture of dictatorships. Two such sets sharing a pair xy give the same probability of x above y when only voter k ranks x above y, and that probability is the weight of k. So all these mixtures have the same weights λ. In particular the law on any set of pairs touching at most m − 1 alternatives is the mixture law.

**Step 2 (determination).** *(D_m)*: a probability law on the m! rankings is determined by its marginals on all sets of m − 1 pairs. Given (D_m), it suffices to show that the law on every set S of m − 1 pairs is the mixture law, at every profile. By Step 1 this holds when S touches at most m − 1 alternatives. The remaining sets touch all m alternatives; up to renaming they are finitely many *shapes* (for m = 4: the star and the path; for m = 5: the path, the star, the fork, and a triangle with a disjoint pair; for m = 6: the six trees on six vertices, and a 4-cycle, a triangle with a pendant pair, or a triangle with a path, each together with whatever completes the six vertices).

**Step 3 (pinning by completion).** *(P_m)*: for each shape S there is a *rule* assigning to every realizable pattern of comparisons on S a full ranking with that pattern, such that the set W of the rule's rankings satisfies:
- *closure*: every ranking whose restrictions to all (m − 1)-element subsets occur among the restrictions of W lies in W;
- *identification*: the indicators of the rankings in W are linearly independent as functions of their restrictions to (m − 1)-element subsets.

Given (P_m), fix arbitrary columns on S. By full compatibility the law on S is the same at every profile with these columns, so give each voter the rule's ranking for its pattern. At this completed profile, by Step 1, each (m − 1)-alternative law is the mixture law of the voters' restricted rankings. So a ranking with positive social probability has every restriction used by some voter of positive weight, and by closure it lies in W. By identification, the probability of each ranking in W is a fixed linear combination of (m − 1)-alternative marginals, the same for every choice of weights (including zero weights for patterns no voter has). The mixture satisfies the same equations, so the social law at the completed profile is the mixture law, and with it the law on S at the original columns. ∎

The three-alternative proof of Theorem 5 is the case m = 3 of the same idea: there the joint probability on two issues is evaluated at the smallest admissible third column, where unanimity forces the other terms to vanish.

## The checks

For m = 4, 5, 6, `pin_certificate_m.py` verifies (D_m) and (P_m) exactly:
- (D_m) as full rank of the marginal map (rank 24, 120 and 720), computed for its Gram matrix modulo a prime; full rank modulo a prime implies full rank over the rationals;
- that every set of m − 1 pairs touching all m alternatives is, up to renaming, one of the shapes of the rules file;
- for each rule: pattern correctness, closure, and identification (rank modulo a prime).

The rules were found by randomised local search (`pin_search.py` for four alternatives, `pinm_search.py` in general), minimising the closure of W. For four alternatives `pin_certificate.py` also prints the explicit identities; for example, with the star rule, the probability of the voters' pattern "a below b, above c, below d" equals the probability of the order b > d > c on the triple bcd.

A one-line instance of the mechanism, for the joint lottery of two disjoint pairs ab and cd with four alternatives: let every voter place c and d next to each other between a and b. The triple laws then put a and b at the extremes with probability 1, so "a above b and c above d" becomes "a on top of acd and c above d", whose probability is the weight of the voters in both columns.

## Symmetry and uniform rules

Towards all m, the question is whether rules can be chosen uniformly. Computations for tree shapes and for all shapes give the following picture (scripts `pin_kernel.py`, `pin_star_uniform.py`, `pin_updown.py`, `pin_greedy.py`).

- **Symmetric completions cannot pin.** Grow a voter's ranking along a tree shape, inserting each alternative directly above or below its neighbour according to the bit. This rule commutes with reversing all preferences and with the shape's automorphisms. Its set of rankings is always closed, but never identified: some signed combination of its rankings is invisible to all (m − 1)-alternative laws. For stars this invisible part is exactly one-dimensional and is the *parity character*, the sign (−1)^(number of 1-bits) of the voter's pattern, for m = 4, 5, 6; for other trees the parity is always among the invisible combinations. The obstruction is a ℤ/2 class, the kind of holonomy the Liar has in *Loops of Relations*. Breaking the symmetry at a single insertion does not remove it.
- **Breaking the reversal symmetry does.** For the star with centre a, the rule "leaves above a in a fixed order, then a, then leaves below a in the same order" is closed and identified for m = 4, 5, 6 and 7 (seven alternatives, 64 rankings). Up and down are treated alike as orders but not as mirror images, so reversal is broken while the renaming structure is kept. For trees, the rule "insert in breadth-first order from a root; an alternative above its neighbour goes directly above it, one below goes to the bottom" pins every tree with some root for m ≤ 6 (rooting at a in every case checked).
- **A uniform rule for all shapes.** A voter's pattern on S is a partial order on the alternatives. Take its greedy linear extension for a fixed priority order of the alternatives (repeatedly place on top the highest-priority alternative that nothing remaining must exceed). For every shape with m = 4, 5, 6, some priority orders pin, and the share that fails decreases with m: for the hardest shape it is 18 of 24 for m = 4, at most 36 of 120 for m = 5, at most 128 of 720 for m = 6; for stars, and several other shapes, every priority order works.

*Reading.* This is the pattern of *Where the Symmetry Goes* inside the proof: a completion that keeps the symmetry leaves a parity class unresolved, and pinning requires breaking it. *(Interpretation.)*

What a proof for all m still needs: (D_m) in general, a choice of priority orders (or another uniform rule) with a proof of closure and identification, and a proof for the non-tree shapes.

## Remarks

- Sets of fewer pairs do not suffice for determination: for five alternatives, laws on sets of three pairs leave a kernel of dimension 24 among the 120 rankings; for six, 394 of 720.
- **All m.** The step goes through for every m for which (D_m) and (P_m) hold; both are verified for m = 4, 5, 6. For m = 7 the check is computation (5,040 rankings, sets of six pairs); the star is already done there by the uniform rule.
- **Relation to weak compatibility.** Under weak compatibility (independence one pair at a time, as for Barberà and Sonnenschein's random social welfare functions) there are rules that are not mixtures of dictatorships, such as the coin rule, and McLennan obtains additive power only from six alternatives on. Under full compatibility the mixture is forced from three alternatives on: the gap between the two is signalling, not contextuality, at every m checked.

## Files

- `scripts/symmetry/pin_certificate_m.py` and `scripts/symmetry/pin_rules.json`: the checks for m = 4, 5, 6;
- `scripts/symmetry/pin_certificate.py`: the four-alternative case with explicit identities;
- `scripts/symmetry/pin_search.py`, `scripts/symmetry/pinm_search.py`: the searches;
- `scripts/symmetry/pin_kernel.py`, `pin_star_uniform.py`, `pin_tree_uniform.py`, `pin_updown.py`, `pin_greedy.py`, `rankmod.py`: the uniform rules and the parity obstruction.
