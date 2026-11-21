# CORE and the Formal Results

*Working note for thread G of the roadmap. It places the CORE mechanism (Consensus Or Random Exclusion; `papers/CORE_13.md`) against the results of* Four Levels of Obstruction in Social Choice, Walls and Strategy *and* Consistency as an Extension Problem. *Four connections are stated: a third characterisation of CORE's fallback, a reading of the draw as the hidden variable of random dictatorship, the exact place of CORE relative to Gibbard's theorems, and a reading of its bargaining in terms of fixed points. Proved statements, computed checks and interpretation are marked. The note ends with the material it would contribute to a follow-up to the CORE paper.*

## 1. CORE in brief

The participants deliberate toward a unanimously accepted proposal, possibly a lottery. At any time any participant may call for a removal: one participant present, drawn uniformly and possibly the caller, leaves the deliberation but keeps their stake in the outcome. If removals run to the end, the last participant enacts their ideal. The fallback is therefore random dictatorship over the participants, and the value of this lottery to participant i at a set S is i's *endowment* e_i(S), the average of i's utilities for the ideals of the members of S. In the *one-shot* variant a stalled deliberation goes straight to the lottery. In the *sequential* variant, which the paper recommends for all but small groups, smaller groups may agree along the way.

## 2. The fallback from three directions

CORE's paper justifies the fallback by Gibbard's (1977) characterisation, extended by Gibbard (1978), Hylland (1980) and Dutta, Peters and Sen: a strategy-proof rule that chooses an option everyone ranks first is a random dictatorship. The results of this repository give two further characterisations, which reach the same object from other sides.

**From aggregation.** By Theorems 5 and 5′ of *Four Levels*, for three to six alternatives and any number of voters, every lottery over rankings that satisfies unanimity and full probabilistic independence of irrelevant alternatives (the joint lottery on any set of pairs depends only on the voters' comparisons on those pairs) is a mixture of dictatorships. If it is also anonymous, all weights are equal, so it is uniform random dictatorship (*Four Levels*, Division). Its winner, the top of the drawn voter's ranking, is CORE's fallback. So uniform random ballot is the winner distribution of the only anonymous lottery over rankings that respects unanimity and independence in this joint sense.

Strategy-proofness and independence are different conditions, and the two characterisations are parallel rather than one. On the strategy side, weakening the condition from dominant strategies leaves Gibbard's mixtures of unilateral and duple rules. On the aggregation side, weakening full to pairwise independence leaves rules with subadditive power such as the coin rule (Barberà and Sonnenschein), and the gap between the two is signalling, not contextuality. McLennan (1980) connected additivity of power with strategy-proofness, and is the closest precedent for treating the two together.

**From electorates.** Random ballot is affine in the vote shares. It therefore satisfies consistency read for joint draws of winners (*Consistency as an Extension Problem*, Section 3b) and participation read for joint draws, which is SD-participation: an added voter raises the probability of each initial segment of their own ranking. Both are checked on random profiles (`scripts/consistency/ex_post_consistency.py` for consistency; the computation behind this note for both). A fallback that elects every Condorcet winner can have neither (*Four Levels*, Theorem 4; Brandt, Geist and Peters). In the scenario of Section 3c, with joins and one-voter extensions as contexts, random ballot is a global section once the Condorcet principle is dropped.

| | strategy | aggregation | electorates |
|---|---|---|---|
| condition | strategy-proofness, unanimity | full independence, unanimity | consistency and participation for joint draws |
| result | random dictatorship (Gibbard 1977; Hylland) | mixtures of dictatorships (*Four Levels*, Theorems 5, 5′; up to six alternatives) | satisfied by random ballot; impossible with the Condorcet principle |
| with anonymity | uniform random dictatorship | uniform random dictatorship | |

**What CORE does with the dropped condition.** The fallback ignores the pairwise structure, which is how it escapes the level-1 obstructions. CORE reintroduces that structure only through unanimous improvement on the fallback, which is not a rule applied to a profile. A Condorcet winner can be agreed on under CORE only if everyone prefers it to the lottery, and then only as one of the options the bargaining may settle on; that it is a Condorcet winner plays no role. A Condorcet winner that some participant finds worse than the lottery cannot be enacted with certainty. Maximal lotteries, the other distinguished lottery (*Consistency as an Extension Problem*, Section 4), make the opposite choice: they keep the Condorcet principle and are consistent and participatory only for lotteries compared as wholes. *(The comparison is a reading of the cited and computed facts.)*

## 3. The draw is the hidden variable

In *Four Levels*, random dictatorship is non-contextual with one hidden variable, the identity of the dictator, and becomes strongly contextual once the voters' permutations are divided out: its hidden variable is the symmetry break. CORE makes this variable physical. Let D be the participant who would be left if removals ran to the end.

**Proposition (martingale).** Under uniform removals, given the current set S of participants, D is uniformly distributed on S. Hence

  e_i(S) = E[ u_i(a*_D) | the removals so far ],

and the endowments e_i(S_0), e_i(S_1), … along any sequence of calls form a martingale.

*Proof.* By induction on |S|: the removed participant is uniform on S, and given who was removed, by the induction hypothesis D is uniform on the rest; so each member of S is D with probability 1/|S|. The second statement is the definition of e_i(S) as the average over S. A conditional expectation of a fixed random variable along an increasing flow of information is a martingale. ∎

The fair-call results of the CORE paper follow at once. Theorem 1 (a call leaves the expected endowment unchanged) is the martingale property for one step. Corollary 1.1 (any sequence of calls, decided in any way on what has happened) is optional stopping for a stopping time bounded by n − 1. Corollary 1.3 (the caller must stand in the draw) is the observation that exemption destroys the uniformity of D: the removals then carry information about who called, not only about D. In the extreme case of a participant who always calls and is exempt, D is that participant with certainty (computed for five participants). Proposition 5 (sortition preserves the benchmark) is the same statement for a uniform sample S: drawing S and then D uniformly within S leaves D uniform on everyone.

The proposition gives the veil of the CORE paper (Section 11) an exact form. Before an agreement, every participant faces the same unrevealed variable D. The one-shot variant reveals it all at once. The sequential variant reveals it by elimination, one non-dictator at a time, and lets those who remain renegotiate with what they have learned. That is why, in the sequential variant, holdings and benchmark come apart (Section 7 of the paper): the benchmark is the expected value of the ideal of D, a martingale whatever anyone does, while holdings depend on the agreements that smaller groups reach once they know that D is among them. The martingale is about the draw, not about what is enacted. *(Proposition proved here; the reading of the veil is interpretation.)*

## 4. Where CORE stands relative to Gibbard

*Walls and Strategy* gives two exact statements that the CORE paper describes in words.

**The dichotomy.** By Theorem 3, every game form with at least three outcomes is dictatorial or has a participant at some preference for whom no program always computes a best reply. By Theorem 6, with lotteries as outcomes, a non-dictatorial procedure either keeps this barrier or is straightforward and inefficient ex ante. CORE's fallback is the straightforward part: the last participant simply enacts their ideal, so there is nothing to compute. Deliberation, which recovers the ex ante gains, is case (i). The CORE paper's Section 9.5 compares this with incompleteness and leaves the comparison as an analogy. Theorem 3 makes it a theorem about any formalisation of deliberation as a finite game form: what remains is a diagonal of the halting type, in substance Canning's (1992), and with opponents required to be rational it is the absence of a strict Nash strategy (Propositions 4, 5 and 5′ for the cases settled).

**A floor computable from inside.** In the one-shot variant a participant's endowment needs only the participants' ideals, not a model of anyone's strategy, and a call secures it. This is the computable floor of *Walls and Strategy*, Section 4. In the sequential variant what can be secured without modelling others is the individual floor of the paper's Proposition 2.

**What does not transfer.** Theorems 3 and 6 concern game forms with finitely many strategies and a fixed set of outcomes. CORE's deliberation has neither: proposals may be lotteries and may introduce options that were on no list (the paper's Theorem 3 on where the gains lie). The theorems therefore bound every way of formalising deliberation as a game form, and say that no such formalisation can remove the barrier while recovering the gains. They do not describe deliberation itself, which is what the paper leaves open on purpose. Whether the open search has properties that no finite formalisation has is a question these results cannot reach.

**Turns.** The observation on simultaneity in *Walls and Strategy* (sequential rationality with visible moves removes the rational diagonal in the veto-then-pick example) bears on the sequential variant: calls are public and taken one at a time, and each removal is observed before the next move. Whether this removes part of the obstruction for the call structure, as distinct from deliberation, is not settled. *(Open.)*

## 5. Bargaining, cycles and fixed points

*(Interpretation throughout.)* Section 9.4 of the CORE paper argues that with a fixed set of options that cannot be mixed, revisions of ballots can only circle a Condorcet cycle; that lotteries dissolve the cycle; and that interim agreements, which lock in a gain for everyone, turn circling into convergence, as in Raiffa's procedure. In the terms of *Cycles and Twists* and *The Switch Between Fixed Point and No Fixed Point*:

- circling is the winding of Section 4 of *Cycles and Twists*: on the cycle there is no fixed point, and a revision that climbs at every step never closes;
- admitting lotteries is the switch "adding values": the cycle is filled into a disc, which has a centre, and the uniform lottery is a fixed point of the cyclic renaming;
- locking in gains makes the process monotone in time: no participant's value can fall back, so the process cannot return to an earlier state, and an increasing bounded sequence converges. This is the switch "acyclic covers glue", with acyclicity in time. Raiffa's procedure is also random dictatorship applied again, one level up, over the improvements on the current benchmark.

So CORE uses two of the three switches between no fixed point and a fixed point: it adds values (lotteries) and it removes cycles (lock-in). The third, going around twice, does not appear.

## 6. Questions

1. **The sequential equilibrium.** The CORE paper's main open problem is what participants hold in the sequential variant, which needs a rule for which agreement each smaller group reaches. In the language of thread A this is a family of data on the poset of sub-electorates, one continuation value per group, whose consistency across groups is not given. Is there a formulation in which the absence of a canonical selection is an obstruction of a definite level?
2. **Characterisation of the winner lottery.** Section 2 characterises random ballot as the winner distribution of a ranking lottery. Is there a direct characterisation of the winner lottery by consistency and participation for joint draws, together with anonymity, neutrality and a condition replacing the Condorcet principle, such as unanimity on first choices?
3. **The call structure as a game.** Does the sequential call structure, with public calls and observed removals, admit an analysis by sequential rationality that removes part of the strategic remainder, as visible turns do in *Walls and Strategy*?
4. **Fallbacks compared.** Section 2 gives one side of the comparison between random ballot and maximal lotteries as fallbacks. The other side, how manipulable each is when used as the fallback of a consensus procedure, is open.

## 7. Material for a follow-up

The CORE paper stays as it is, a standalone introduction to the method. What is new here belongs in a follow-up, once it is settled:

- the characterisation of the fallback from aggregation (Section 2), beside Gibbard's and Hylland's from strategy, and the electorate properties of random ballot;
- the martingale proposition (Section 3), from which the fair-call results, the rule that callers stand in the draw and the sortition result follow, and the reading of the veil as the unrevealed draw;
- CORE's exact place relative to Gibbard's theorems (Section 4), with the limit of what the theorems say about open deliberation;
- whatever comes of the questions in Section 6, in particular the sequential equilibrium and the call structure under sequential rationality.

## References

- Barberà, S. and Sonnenschein, H. (1978). Preference aggregation with randomized social orderings. *Journal of Economic Theory* 18, 244–254.
- Brandt, F., Geist, C. and Peters, D. (2017). Optimal bounds for the no-show paradox via SAT solving. *Mathematical Social Sciences* 90, 18–27.
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Diskin, A., Koppel, M. and Samet, D. (2011). Generalized Raiffa solutions. *Games and Economic Behavior* 73, 452–458.
- Dutta, B., Peters, H. and Sen, A. (2007). Strategy-proof cardinal decision schemes. *Social Choice and Welfare* 28, 163–179; erratum 30 (2008), 701–702.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Heitzig, J. and Simmons, F. W. (2012). Some chance for consensus: voting methods for which consensus is an equilibrium. *Social Choice and Welfare* 38, 43–57.
- Hylland, A. (1980). Strategy proofness of voting procedures with lotteries as outcomes and infinite sets of strategies. Mimeo, University of Oslo.
- McLennan, A. (1980). Randomized preference aggregation: additivity of power and strategy proofness. *Journal of Economic Theory* 22, 1–11.
- Raiffa, H. (1953). Arbitration schemes for generalized two-person games. In *Contributions to the Theory of Games II*, Princeton University Press, 361–387.
- *CORE: Consensus Or Random Exclusion* (`papers/CORE_13.md`); *Four Levels of Obstruction in Social Choice*, *Walls and Strategy*, *Cycles and Twists* (drafts); *Consistency as an Extension Problem*, *The Switch Between Fixed Point and No Fixed Point* (working notes), all in this repository.
