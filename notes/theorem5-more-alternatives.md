# Theorem 5 for up to ten alternatives

*Working note. It extends Theorem 5 of* Four Levels of Obstruction in Social Choice *(empirical models of Arrow's scenario are mixtures of dictatorships) from three alternatives to every number up to ten, for any finite number of voters. The proof is an induction on the number of alternatives. Each step reduces to one finite check on a path of comparisons; the checks are carried out for m = 4, …, 10 by `scripts/symmetry/pin_path_certificate.py` and `scripts/symmetry/pin_path_greedy.py`. A hand proof of the step for all m is outlined at the end.*

## Statement

**Theorem 5′.** For m ≤ 10 alternatives and any finite set of voters, every empirical model on Arrow's scenario (full compatibility, unanimity) is a mixture of dictatorships: there are weights λ_k ≥ 0 summing to 1 such that at every profile the social ranking has the law of the ranking of voter k drawn with probability λ_k.

A *column* on a pair xy is the set of voters ranking x above y. Full compatibility says: for every set S of pairs, the joint law of the social comparisons on S depends only on the columns of the pairs in S.

## The induction step

Let m ≥ 4 and assume the theorem for m − 1 alternatives (for m = 4 this is Theorem 5).

**Step 1 (sub-models).** Restricted to any m − 1 alternatives, the model is an empirical model of the scenario on those alternatives, hence a mixture of dictatorships. Two such sets sharing a pair xy give the same probability of x above y when only voter k ranks x above y, and that probability is the weight of k. So all these mixtures have the same weights λ.

**Step 2 (a ranking is an event on a path).** The social ranking equals x₁ > x₂ > … > xₘ exactly when x_i is above x_{i+1} for every i. So its probability is the probability of one pattern on the path of the m − 1 consecutive pairs, and by full compatibility it depends only on the columns of these pairs. Likewise, the voters with ranking x₁ > … > xₘ are exactly the voters in all these columns. It therefore suffices to show, for one profile with the given path columns, that the probability of x₁ > … > xₘ is the total weight of those voters. Up to renaming, the path is a₁ – a₂ – … – aₘ and the target ranking is a₁ > a₂ > … > aₘ.

**Step 3 (completion).** Give every voter a full ranking determined by its pattern on the path by a *rule*, and let W be the set of the rule's rankings. Suppose:
- *closure*: every ranking whose restrictions to all (m − 1)-element subsets occur among the restrictions of W lies in W;
- *target identification*: on W, the indicator of a₁ > … > aₘ is a linear combination of the indicators "the restriction to the (m − 1)-subset T is o".

At the completed profile, by Step 1, each (m − 1)-alternative law is the mixture law of the voters' restricted rankings. A ranking with positive social probability has every restriction used by some voter of positive weight, so by closure it lies in W. By target identification its probability is a fixed combination of (m − 1)-alternative marginals, the same for every choice of weights (including zero weights for patterns no voter has), and the mixture satisfies the same identity. So the probability of the target is the mixture's. ∎

The three-alternative proof of Theorem 5 is the smallest case of the same idea: there the joint probability on two issues is evaluated at the smallest admissible third column, where unanimity forces the other terms to vanish.

## The rule and the checks

The rule used is the *greedy linear extension*. A voter's pattern on the path is a partial order; for a fixed priority order of the alternatives, place on top the highest-priority alternative that no remaining alternative must exceed, and repeat.

| m | priority order | rule rankings | check |
|---|---|---|---|
| 4 | a c d b | 8 | exact; P(a>b>c>d) = P(a>b>d) |
| 5 | a b c d e | 16 | exact; five marginal terms |
| 6 | d f a b c e | 32 | exact; one term, P(target) = P(a>b>d>e>f) |
| 7 | a b c d e f g | 64 | exact |
| 8 | g h d a c f b e | 128 | exact; one term, P(target) = P(a>b>c>d>e>f>h) |
| 9 | a b c d e f g h i | 256 | exact |
| 10 | b j c a e g h d i f | 512 | full identification modulo a prime |

"Exact" means: closure verified, and the identity solved modulo a prime, lifted to rationals and verified over the integers (`pin_path_certificate.py m priority`). For m = 10, `pin_path_greedy.py 10 1 bjcaeghdif` verifies closure and that the rule's rankings are linearly independent over the (m − 1)-alternative indicators modulo a prime; full rank modulo a prime implies full rank over the rationals, which gives target identification. For odd m the natural priority order works; for even m it misses by exactly one dimension, while random priority orders work (for m = 8, every priority order tried).

## Towards all m: a hand proof

The one-term identities point to a direct argument. Suppose the rule satisfies, for a middle alternative a_j and T = all alternatives except a_j:
- *(uniqueness)* among the rule's rankings, only the target restricts on T to a₁ > … > a_{j−1} > a_{j+1} > … > aₘ;
- *(exclusion)* every ranking obtained from that restriction by inserting a_j anywhere other than between a_{j−1} and a_{j+1} has, on some (m − 1)-element subset, a restriction that no rule ranking has.

Then the social probability of the target equals the social probability of that restriction on T, which equals the mixture's (Step 1), which by uniqueness is the weight of the target voters. Uniqueness is easy to arrange for every m: a voter whose pattern differs from the target outside the two comparisons at a_j already has a different order on T; for the four patterns at a_j, the pattern "a_j above a_{j−1} and a_{j+1} below a_j" forces a_{j+1} above a_{j−1}; in the two patterns that leave a_{j−1} and a_{j+1} free, the rule must put a_{j+1} above a_{j−1}. What remains to be proved by hand is exclusion, for a rule defined uniformly in m.

## Symmetry and the parity obstruction

- **Symmetric completions cannot pin.** On tree shapes, the rule that inserts each alternative directly next to its neighbour commutes with reversing all preferences. Its rankings are always closed but never identified; for stars the invisible part is exactly the parity character (−1)^(number of 1-bits) of the voter's pattern, a ℤ/2 class of the kind the Liar has in *Loops of Relations*.
- **Breaking reversal pins.** For the star with centre a, "leaves above a in a fixed order, then a, then leaves below a in the same order" is closed and identified for m = 4, …, 7; the greedy rule pins every shape of m − 1 pairs for m ≤ 6 with suitable priority orders, the failing share shrinking with m.
- On the path, the natural priority order fails by one dimension exactly for even m, consistent with a residual symmetry of the path that it does not break for even m.

*Reading.* This is the pattern of *Where the Symmetry Goes* inside the proof: a completion that keeps the symmetry leaves a parity class unresolved, and pinning requires breaking it. *(Interpretation.)*

## Remarks

- Sets of fewer than m − 1 pairs do not determine a law on rankings: for five alternatives, laws on sets of three pairs leave a kernel of dimension 24 among the 120 rankings; for six, 394 of 720.
- **Relation to weak compatibility.** Under weak compatibility (independence one pair at a time, as for Barberà and Sonnenschein's random social welfare functions) there are rules that are not mixtures of dictatorships, such as the coin rule, and McLennan obtains additive power only from six alternatives on. Under full compatibility the mixture is forced from three alternatives on: the gap between the two is signalling, not contextuality, at every m checked.

## Files

- `scripts/symmetry/pin_path_certificate.py`: the exact check of the step for given m and priority order;
- `scripts/symmetry/pin_path_greedy.py`: the same check with numpy (used for m = 10) and a search over priority orders;
- `scripts/symmetry/pin_certificate.py`: the four-alternative case with the first rules found (star and path) and explicit identities;
- `scripts/symmetry/pin_certificate_m.py`, `pin_rules.json`: the earlier, longer form of the step for m = 4, 5, 6 (all shapes of m − 1 pairs);
- `scripts/symmetry/pin_search.py`, `pinm_search.py`, `pin_kernel.py`, `pin_star_uniform.py`, `pin_tree_uniform.py`, `pin_updown.py`, `pin_greedy.py`, `rankmod.py`: searches, uniform rules and the parity obstruction.
