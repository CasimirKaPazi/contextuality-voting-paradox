# Lean roadmap

Proofs in the notes and drafts that are not yet formalised, ordered by how much later work would rest on them. The index of what is already checked is `README.md` in this folder.

## 1. Foundations to build on

1. **Scenarios and levels** (*Four Levels*, Section 2 and Proposition 1).
   - Definitions:
     - a scenario (variables, values, contexts, admissible values);
     - global sections;
     - empirical models with weak and full compatibility;
     - non-contextuality;
     - a symmetry group and the four levels.
   - Proposition 1 (division): the average of a global section over a finite group is a symmetric, non-contextual model.
   - Then show that the existing models are instances: `ArrowGeneral.Model` for Arrow's scenario, and `JointDraws` with one voter's slice for Gibbard–Satterthwaite.
   - Value: every later placement becomes a theorem about one structure instead of a file with its own definitions.
   - Effort: moderate. The definitions are the work; the proofs are short.
   - Status: definitions, "mixtures of global sections are models", "full implies weak compatibility" and Proposition 1 are in `Scenarios.lean`. The Gibbard–Satterthwaite instance is in `GSScenario.lean`. Open: the Arrow instance.
2. **One encoding of rankings.**
   - `PathPinning.Rk` (Boolean strict total orders) and `JointDraws` (injective maps to ℕ) encode rankings differently.
   - A bridge lemma, or a single encoding with the swap lemmas, removes this seam before more files depend on it.
   - Effort: small to moderate.
   - Status: done in `Rankings.lean`. `PathPinning.Rk` is the common encoding; the joint-draw theorem is stated for it (`prop1R`).
3. **Lotteries and joint draws as a toolkit.**
   - Couplings, Markov kernels and their composition, and stochastic dominance.
   - Part of this exists inside `JointDraws.lean`; move it into its own file.
   - Then add Lemma 3 of *Four Levels*, the joint-draw criterion λ(a) ≥ μ(a) + ν(a) − 1, also stated in *Consistency as an Extension Problem*, Section 3b.
   - Used by consistency, participation and Gibbard–Satterthwaite.
   - Effort: small.
   - Status: the necessary direction of Lemma 3 is in `JoinLotteries.lean`. Open: the sufficient direction (a transport argument of Hall type: an off-diagonal coupling exists when no candidate carries more than the total), and moving the couplings and kernels out of `JointDraws.lean`.

## 2. Results that complete a thread

4. **Theorem 4 of *Four Levels*.** No Condorcet extension is consistent for joint draws, with vote shares and any number of candidates.
   - Needs Lemma 3 and the blocking lemma (*A Map of Voting Paradoxes*) for vote shares.
   - `Consistency.lean` already has the integer-electorate construction of Theorem 2.
   - Also needed later for the electorate scenario of *Consistency as an Extension Problem*, Section 3c, whose reduction proposition (conditions J and E) would follow.
   - Effort: moderate.
   - Status: done in `JoinLotteries.lean`, for electorates as weighted lists (joins as unions, no anonymity or homogeneity assumed); it needs only the necessary direction of Lemma 3. Open: the reduction proposition, which needs both directions.
5. **Isotropy lemma, general form** (*Where the Symmetry Goes*). Both directions:
   - a neutral rule maps a profile to an output fixed by its stabiliser;
   - an output fixed by the stabiliser of every orbit representative extends to a neutral rule.
   - `ProfileFacts.lean` has one instance. Mathlib's `MulAction` and orbits fit.
   - It is the pointwise form of level 3, and Item 1 would use it.
   - Effort: small to moderate.
   - Status: done in `Isotropy.lean`, for any group action and any equivariant family of admissible outputs; no finiteness needed.
6. **Gibbard–Satterthwaite placement, rest.**
   - Proposition 3 (the random top two is contextual): a short counting argument.
   - Corollary 2 with Gibbard's (1977) characterisation entering as an explicit hypothesis, in the way `Lotteries.lean` treats Gibbard's 1978 Corollary 2.
   - Effort: small for both.
7. **Soundness of the summary automaton** (note *The rational diagonal on totally tight game forms*, update-rule lemma).
   - The claim: whether a player lacks a strict Nash strategy depends only on the set of row summaries, and adding a constant row or column changes the set by the stated rule.
   - This would make the computer proof of Proposition 5′ of *Walls and Strategy* rest on a checked reduction.
   - It is also the tool for general tight forms (thread D).
   - Effort: moderate. A certificate check of the cases with four outcomes is a separate, possibly heavy step.

## 3. Later or large

8. **Gibbard (1978), Corollary 2**, now an assumption in `Lotteries.lean`. Effort: moderate to large.
9. **CORE propositions** (*CORE and the Formal Results*).
   - The martingale property and the decomposition of holdings are finite sums over subsets: small to moderate.
   - The concave-loss results need invertibility and positivity of distance matrices: large.
   - These matter once the CORE follow-up is written.
10. **Gibbard (1977)**, the characterisation of strategy-proof decision schemes. Large; it would remove the hypothesis of Item 6.

## Not planned

- **Proposition 6 of *Cycles and Twists*** (comparison complexes as spheres, quotients as projective spaces). It needs homotopy theory that Mathlib does not yet offer in usable form.
- **The count over all 18,138 two-player game forms.** It would need a formal proof that the enumeration is complete. The general results in Items 7 and 1 are the better targets.
