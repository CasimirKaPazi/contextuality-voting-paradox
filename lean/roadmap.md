# Lean roadmap

What is still to be formalised, and in which order. What is already checked is indexed in `README.md` in this folder. The items are grouped by three questions: what later work needs as a base, what is nearly finished, and which main claims of the project still rest on proofs by hand or on computation alone.

## In place

Each line names the main results already checked, by thread of the project roadmap (`notes/roadmap.md`).

- **A (consistency as non-contextuality).**
  - Theorem 2 (`Consistency.lean`).
  - Theorem 4 with the necessary direction of Lemma 3 (`JoinLotteries.lean`), and Lemma 3 in both directions with the coupling lemma behind it (`Couplings.lean`).
  - The reduction proposition of *Consistency as an Extension Problem*, Section 3c (`ConsistencyScenario.lean`).
  - The frame of scenarios and the four levels, with Proposition 1, division (`Scenarios.lean`).
- **B (where the symmetry goes).**
  - The isotropy lemma for any group action (`Isotropy.lean`).
  - The discrete degree for three alternatives, Lemmas 1–4 and Proposition 1 of *The Global Form*, Arrow's theorem as a degree (`GlobalForm.lean`).
  - The degree for strategy-proof rules, Lemmas 5–6 and Proposition 3 of *The Global Form*, the Gibbard–Satterthwaite theorem for three alternatives as a degree (`GlobalFormSP.lean`).
  - Lemma 2 and Propositions 1 and 3 of *Equivariant Obstructions* for local Pareto rules (`LocalPareto.lean`).
  - The real degree and Proposition 2 of *The Global Form*, for mixtures of dictatorships and anti-dictatorships and for every empirical model of Arrow's scenario with three alternatives (`GlobalFormReal.lean`, `RealDegreeBridge.lean`).
- **Arrow and Gibbard–Satterthwaite as scenarios.**
  - Theorems 5 and 5′ of *Four Levels* (`ProbabilisticArrow.lean`, `PathPinning.lean`, `ArrowGeneral.lean`, `ArrowBase.lean`).
  - Arrow's scenario as an instance of the frame: every empirical model is non-contextual (Theorem 5′), the global sections are the dictatorships (Arrow's theorem, derived from Theorem 5′), level 3 for the voters' permutations, and division (`ArrowScenario.lean`).
  - The Gibbard–Satterthwaite scenario, Proposition 1 to Corollary 2. Corollary 2 takes Gibbard's 1977 theorem as a hypothesis (`JointDraws.lean`, `Rankings.lean`, `GSScenario.lean`, `GSTopTwo.lean`, `GSCorollary.lean`).
  - Propositions 1 and 2 of *The Equality Criterion and Reversal*, the second with Gibbard's 1977 theorem as a hypothesis (`EqualityCriterion.lean`).
- **C (cycles and twists).**
  - Propositions 1–5 and remark (d) of *Cycles and Twists* (`ValueSpaces.lean`, `ProbLine.lean`, `CircleTournaments.lean`, `Nerve.lean`).
  - Propositions 1–3 of *Loops of Relations* (`LoopsOfRelations.lean`).
  - Propositions 1 and 2 of *Covers and Division*, with the bound and the K-fold cover, and the corollary (`Covers.lean`, `CoversDecomp.lean`).
- **D (strategy as a halting problem).**
  - Gibbard (1973), Lemma 2 and Theorem 3 (`Arrow.lean`, `Gibbard73.lean`, `Diagonal.lean`, `Dichotomy.lean`).
  - The corollary of *What Cannot Be Defined from Inside*: composite procedures (`Composition.lean`).
  - Theorem 6, with Gibbard's 1978 Corollary 2 as a hypothesis (`Lotteries.lean`).
  - Burial (`Burial.lean`).
  - The certificates of Proposition 4 (`RationalDiagonal.lean`).
  - Proposition 5 (`NonTight.lean`).
  - Proposition 5″, the tight form without a rational diagonal (`TightCounterexample.lean`).
  - Proposition 5‴, the exact criterion for three outcomes (`ThreeOutcomes.lean`), and the common frame for two-player forms (`TwoPlayer.lean`).
  - Proposition 7, approval with a veto (`ApprovalVeto.lean`).
  - The summary and its update rule behind Proposition 5′ (`SummaryAutomaton.lean`).
- **G (CORE).** The draw, the decomposition of holdings, the theorem for one dimension, the mean of the peaks with the members' value under efficiency, the mean rule, safe agreements (parts 1 and 2), the veto-kept floor and the stages of the call game (`CoreDraw.lean`); the call game as one tree, with existence of a subgame-perfect equilibrium in undominated votes, every equilibrium one Raiffa step, and uniqueness of the values (`CallGame.lean`, Markov strategies).
- **Strategic information.** Propositions 1–3, the Smith set, and the steps of Proposition 4 (`LeaderRule.lean`); Propositions 5 and 6, which derive the best replies from the weights of ties, and the counting of Proposition 4 for an abstract sequence of leaders (`StrategicInformation.lean`); Proposition 4 as one statement for the walk with memory, with ties (Proposition 7) and without, and the bridge from positions to utilities (`MemoryWalk.lean`).

## 1. Foundations to build on

These are definitions and toolkits that several later items need. Doing them first keeps later files from each bringing their own encoding.

1. **One frame for two-player game forms.**
   - In place: `TwoPlayer.lean`, on the definitions of `NonTight.lean`, with player 2's side through the transpose, strict Nash strategies, and the bridge to `SummaryAutomaton.lean`. `TightCounterexample.lean` uses it.
   - Not bridged: `RationalDiagonal.lean` (certificates for voting rules on lists of rankings) and `Gibbard73.lean` (n players, relations).
   - Proposition 5‴, Theorems A and B of *A tight form without a rational diagonal*, is in place in the frame (`ThreeOutcomes.lean`).
   - Proposition 7, approval with a veto, is in place for any number of players (`ApprovalVeto.lean`, with its own n-player notion of a strict Nash strategy).
   - Next: the assembly of Proposition 5′ (thread D).
2. **Lotteries and joint draws as a toolkit.**
   - In place: Lemma 3 in both directions and the coupling lemma (`Couplings.lean`).
   - In place as well: Strassen's theorem for a chain, on the positions of a ranking (`mono_iff_dom`).
   - Open: moving the couplings and kernels of `JointDraws.lean` next to them, if a second use appears.
   - Value: the reduction proposition of *Consistency as an Extension Problem*, Section 3c (conditions J and E), now in place (`ConsistencyScenario.lean`).
   - Effort: small.

## 2. Nearly finished: complete these

Nothing at the moment.

## 3. Main claims that still rest on proofs by hand or on computation

These are the results the project's claims stand on, by thread. Details below them are not listed.

- **A. The electorate scenario passes through all four levels** (*Consistency as an Extension Problem*, Sections 3c–3d). The claim, for three alternatives:
  - no deterministic rule from 8 voters;
  - no lottery rule drawn jointly from 9;
  - models without a global section at 8.

  The impossibility side is a certificate: three joins around the doubled Condorcet profile for lotteries, and a case split on ten profiles for deterministic rules. Checking these in Lean on top of `JoinLotteries.lean` is moderate. The existence side needs the models found by search as data, which is heavier.
- **B. Arrow's theorem as a degree, and the stages of the symmetry problem for three alternatives** (*The Global Form*, Propositions 1–3; *Equivariant Obstructions*, Propositions 1–4).
  - These are discrete and rest on Lemmas 1–3 of *The Global Form*, now in `GlobalForm.lean`. Lemmas 1–6 and Propositions 1 and 3 are there (`GlobalForm.lean`, `GlobalFormSP.lean`). Proposition 2 is there, for mixtures and, through Theorem 5′, for every empirical model of Arrow's scenario with three alternatives (`GlobalFormReal.lean`, `RealDegreeBridge.lean`). The real degree is the expected winding of every compatible joint draw (`RealDegreeWinding.lean`). Propositions 4 and 5 are in place (`GlobalFormLottery.lean`, `ContextualFraction.lean`, the latter with Gibbard 1977 as a hypothesis), with the bridge to the scenario of `GSScenario.lean` (`ContextualBridge.lean`). Of *Equivariant Obstructions*, Lemma 2 and Propositions 1 and 3 are in place for local Pareto rules (`LocalPareto.lean`). Next: Proposition 4 (real degrees of SD-SP unanimous lotteries in [0, 1], without Gibbard 1977). Not planned for now: stages 0 and 1 (the table of Section 2 and the midpoints). Effort: moderate.
  - For four alternatives, Theorem 10 (local rules have at most one voter of non-zero degree) and Proposition 14 rest on computations of the permutohedron's fillings. A certificate check would be large.
- **D. Proposition 5′: every totally tight form, and every game of perfect information, admits a rational diagonal.** The proof combines three parts:
  - the structure theorem of Boros, Gurvich, Makino and Papp, taken from the literature;
  - a reduction to at most seven outcomes;
  - two exact searches.

  The summary and the update rule are checked. Next:
  - state the theorem and the reduction in the frame of Item 1.1;
  - take the structure theorem as a hypothesis;
  - check the searches, a large step.

  Proposition 5‴, the exact criterion for three outcomes (Theorems A and B of the note *A tight form without a rational diagonal*), is checked (`ThreeOutcomes.lean`). Proposition 7, approval with a veto, is checked (`ApprovalVeto.lean`).
- **G. CORE.**
  - The proposition on concave loss (Section 3b): invertibility and positivity of distance matrices. Large.
  - The theorem that on a line the random ballot is the only strategy-proof rule that harms no one (Section 3h). It is moderate with the characterisation of Ehlers, Peters and Storcken as a hypothesis. Without it, it is large.
  - Cautious proposers (Section 3h): moderate.
  - Strassen's characterisation of safe agreements (Section 3f, part 3): large.
- **Strategic information: the statements about all methods** (`notes/strategic-information/`: the README, Section 2, *Bounds from Criteria*, *The Ballot Polytope*, *What a Ballot Reveals*, *Intensities and the Utilitarian Target*, *The Honest Axis*). These are short proofs by hand on which the comparison of methods now rests; none is checked. In the order in which they depend on each other:
  - The frame: types, ballots, a count as an additive map, the strategic count as a matrix M with whole entries acting on histograms. Small, and everything below uses it.
  - README, Section 2, Proposition (counts): the count of A is a function of the count of B on every profile exactly when the rows of M_A are combinations of the rows of M_B. The step from whole vectors in the kernel to the kernel over the rationals is the only work. Small to moderate. With it the Lemma (one voter). Small.
  - *Bounds from Criteria*, Lemma 1 (certifying the leader is membership of the margins in the row space; the proof uses a profile with all margins zero and two profiles h + v, h − v), Proposition 2 (the ballot determines the set of candidates preferred to the leader; 2^(m−1) count vectors), Proposition 3 (rank m − 1; a count of totals that certifies has the leader's row as its row space) and Corollary 5 (such a method keeps opposite voters equal). Moderate together; the independence of the m − 1 margins as functions on rankings is the part that takes work.
  - *Bounds from Criteria*, Proposition 4 (the odd functions in the row space have dimension d − e): rank and nullity of one linear map. Small.
  - *Bounds from Criteria*, Proposition 7 and Corollary 8 (a graph of comparisons; the number of ways of directing its edges without a cycle; the whole majority relation is needed to name the Condorcet winner). Moderate for the star and the complete graph, larger for a general graph because of the count of directions.
  - *The Ballot Polytope*, Proposition 2 (a unique maximiser of a linear function on the hull of finitely many points is a vertex, and every vertex is one) and Proposition 4 (central symmetry gives ballots for g and −g that add up to a constant; the Equality Criterion gives central symmetry). Small with Mathlib's extreme points, moderate without.
  - *What a Ballot Reveals*, Proposition 3 (at most m^k lotteries from k possibilities; under certainty one comparison at most): counting, small. Proposition 4 (a way of filling in the ballot that is always a best reply makes the method a dictatorship): the composition with the theorem of Gibbard and Satterthwaite, small on top of `Gibbard73.lean`, or on `GlobalFormSP.lean` for three alternatives. Proposition 2 (a revealed comparison has an edge parallel to e_i − e_j) needs the cones of a polytope and is larger.
  - *Intensities and the Utilitarian Target*, Proposition 1 (best replies do not change under λu + c) and Proposition 4 (certifying the leader leaves no room for intensities, from Proposition 3 of the bounds); *The Honest Axis*, Proposition 2 (scores 0 to k are within n/k of the best). Small each.

  Not planned here: Proposition 1 of *The Ballot Polytope* (the linear regime) as an analytic statement about beliefs; the notes use it as the definition of the regime. The computed parts (the smooth model, the tables of vertices) are not candidates.
- **The two theorems taken as hypotheses.**
  - Gibbard (1977), used in `GSCorollary.lean` and `EqualityCriterion.lean`.
  - Gibbard (1978), Corollary 2, used in `Lotteries.lean`.

  Each is large. Removing them would make Corollary 2 of the scenario note and Theorem 6 of *Walls and Strategy* unconditional.

## Not planned

- **The homotopy-theoretic results of *Equivariant Obstructions*:** Propositions 5, 5′ and 6, Theorem 7, Lemma 8 and Proposition 9. They use cup products, the Whitehead square and Steenrod squares on spheres, which Mathlib does not offer in usable form. The same holds for Proposition 6 of *Cycles and Twists* (comparison complexes as spheres, quotients as projective spaces).
- **The count over all 18,138 two-player game forms.** It would need a formal proof that the enumeration is complete. Items 1.1 and 3 (thread D) are the better targets.
