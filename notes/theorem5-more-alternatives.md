# Theorem 5 for any number of alternatives

*Working note. It extends Theorem 5 of* Four Levels of Obstruction in Social Choice *(empirical models of Arrow's scenario are mixtures of dictatorships) from three alternatives to any number, for any finite number of voters. The proof is a short induction on the number of alternatives; it is checked in Lean (`lean/ArrowBase.lean`, theorem `theorem5'`). It was found through computations (exact certificates for up to ten alternatives) that are listed at the end and now serve as independent checks.*

## Statement

**Theorem 5′.** For any number m ≥ 3 of alternatives and any finite set of voters, every empirical model on Arrow's scenario (full compatibility, unanimity) is a mixture of dictatorships: there are weights λ_k ≥ 0 summing to 1 such that at every profile the social ranking has the law of the ranking of voter k drawn with probability λ_k.

A *column* on a pair xy is the set of voters ranking x above y. Full compatibility says: for every set S of pairs, the joint law of the social comparisons on S depends only on the columns of the pairs in S.

## Proof

By induction on m. For m = 3 this is Theorem 5. Let m ≥ 4 and assume the theorem for m − 1 alternatives.

**Step 1 (sub-models).** Restricted to any m − 1 alternatives, the model is an empirical model of the scenario on those alternatives, hence a mixture of dictatorships. Two such sets sharing a pair xy give the same probability of x above y when only voter k ranks x above y, and that probability is the weight of k. So all these mixtures have the same weights λ.

**Step 2 (a ranking is an event on a path).** Fix a profile and a ranking; rename the alternatives so that the ranking is a₁ > a₂ > … > aₘ. The social ranking equals it exactly when a_i is above a_{i+1} for every i < m. So its probability depends only on the columns of the m − 1 pairs a_i a_{i+1} (full compatibility), and the voters who rank a₁ > … > aₘ are exactly the voters in all these columns. It suffices to show the claim at one profile with these columns.

**Step 3 (completion).** Replace each voter's ranking by one with the same comparisons on the pairs a_i a_{i+1}, chosen as follows: if the voter ranks a₂ above both a₁ and a₃, or below both, it ranks a₃ above a₁; otherwise any ranking with these comparisons. This is always possible: the comparisons on the path force a₁ above a₃ only when a₁ is above a₂ and a₂ above a₃. (Concretely: move a₁ to directly below a₃; this changes only comparisons involving a₁ and keeps a₁ against a₂.) The columns of the path are unchanged.

**Step 4 (pinning).** Let T be all alternatives except a₂, and let o be the target's restriction to T, that is a₁ > a₃ > a₄ > … > aₘ. At the completed profile:

- *Only target voters restrict to o.* A voter whose restriction to T is o has a_i above a_{i+1} for every i ≥ 3 and a₁ above a₃. If it ranked a₂ above both a₁ and a₃, or below both, it would rank a₃ above a₁ by Step 3; if it ranked a₃ above a₂ above a₁, it would rank a₃ above a₁ by transitivity. So it ranks a₁ above a₂ above a₃, and with the other comparisons its ranking is a₁ > … > aₘ. By Step 1, the social probability of o on T is therefore the total weight of the target voters.
- *No other ranking with restriction o has positive probability.* A ranking σ ≠ a₁ > … > aₘ with restriction o on T puts a₂ above a₁ or below a₃; in both cases a₂ is above both or below both of a₁ and a₃, while a₁ is above a₃. Let U be all alternatives except aₘ; since m ≥ 4, U contains a₁, a₂, a₃. A voter with the same restriction to U as σ would rank a₂ above both or below both of a₁ and a₃ and a₁ above a₃, which Step 3 excludes. So by Step 1 the social probability of σ's restriction to U is zero, and so is that of σ.

Hence the social probability of a₁ > … > aₘ equals that of o on T, which is the total weight of the voters ranking a₁ > … > aₘ. By Step 2 this holds at every profile and for every ranking, so the model is the mixture of dictatorships with weights λ. ∎

The proof uses unanimity only through the case m = 3, and full compatibility at one point: the probability of a ranking is unchanged when the columns off its path are replaced.

## Remarks

- **The identity behind it.** At the completed profile, P(a₁ > a₂ > … > aₘ) = P(a₁ > a₃ > … > aₘ on all alternatives but a₂). The computations found exactly such one-term identities, for example P(a > b > c > d) = P(a > b > d) for four alternatives, before the general argument.
- **Symmetry.** The completion breaks a symmetry: it fixes the orientation "a₃ above a₁" wherever the path leaves it open, and so is not invariant under reversing all preferences. Completions that keep that symmetry cannot pin: on the shapes computed, a rule that inserts each alternative directly next to its neighbour gives rankings whose (m − 1)-alternative laws never identify them; for stars the invisible part is exactly the parity character (−1)^(number of 1-bits) of the voter's pattern, a ℤ/2 class of the kind the Liar has in *Loops of Relations*. *Reading:* the pattern of *Where the Symmetry Goes* inside the proof, a symmetry-keeping completion leaves a parity class unresolved and pinning requires breaking it. *(Interpretation.)*
- **Relation to weak compatibility.** Under weak compatibility (independence one pair at a time, as for Barberà and Sonnenschein's random social welfare functions) there are rules that are not mixtures of dictatorships, such as the coin rule, and McLennan obtains additive power only from six alternatives on. Under full compatibility the mixture is forced from three alternatives on, for every number of alternatives: the gap between the two is signalling, not contextuality.

## Formal proof

The whole theorem is checked in Lean, for any finite type of alternatives with at least three elements and any finite type of voters:
- `lean/PathPinning.lean`: Step 4, as a lemma about a non-negative function on rankings whose marginals on T and U are mixtures;
- `lean/ArrowGeneral.lean`: the general framework (rankings as strict total orders, models with full compatibility for any set of ordered pairs and unanimity, mixtures), restriction of a model to fewer alternatives, the induction step (Steps 1–4, with the completion constructed explicitly) and the induction from the three-alternative case;
- `lean/ArrowBase.lean`: the translation of a model on three alternatives into the column encoding of `lean/ProbabilisticArrow.lean` (Theorem 5) and back, and the final theorem `theorem5'`.

## Computational checks

Before the general argument, the induction step was verified exactly for m = 4, …, 10 by completions chosen as greedy linear extensions, with closure of the voters' rankings and identification of the target checked in exact arithmetic (`scripts/symmetry/pin_path_certificate.py`, `pin_path_greedy.py`); and for m = 4, 5, 6 in a longer form with all shapes of m − 1 pairs (`pin_certificate_m.py`, `pin_rules.json`). The argument above was also checked by linear programming: for random completions of the kind in Step 3 and random weights, with some patterns absent, the probability of the target is forced to the mixture's for m = 4, 5, 6 (`path_proof_check.py`).

## Files

- `lean/PathPinning.lean`, `lean/ArrowGeneral.lean`, `lean/ArrowBase.lean`: the formal proof;
- `scripts/symmetry/path_proof_check.py`: linear-programming check of the argument;
- `scripts/symmetry/pin_path_certificate.py`, `pin_path_greedy.py`: exact checks of the step, m ≤ 10;
- `scripts/symmetry/pin_certificate.py`: the four-alternative case with the first rules found and explicit identities;
- `scripts/symmetry/pin_certificate_m.py`, `pin_rules.json`, `pin_search.py`, `pinm_search.py`, `pin_kernel.py`, `pin_star_uniform.py`, `pin_tree_uniform.py`, `pin_updown.py`, `pin_greedy.py`, `rankmod.py`: the earlier searches, uniform rules and the parity obstruction (optional; the proof does not depend on them).
