# Lean roadmap

What is still to be formalised, and in which order. What is already checked is indexed in `README.md` in this folder. The items are grouped by three questions: what later work needs as a base, what is nearly finished, and which main claims of the project still rest on proofs by hand or on computation alone.

## In place

Each line names the main results already checked, by thread of the project roadmap (`notes/roadmap.md`).

- **A (consistency as non-contextuality).**
  - Theorem 2 (`Consistency.lean`).
  - Theorem 4 with the necessary direction of Lemma 3 (`JoinLotteries.lean`).
  - The frame of scenarios and the four levels, with Proposition 1, division (`Scenarios.lean`).
- **B (where the symmetry goes).** The isotropy lemma for any group action (`Isotropy.lean`).
- **Arrow and Gibbard–Satterthwaite as scenarios.**
  - Theorems 5 and 5′ of *Four Levels* (`ProbabilisticArrow.lean`, `PathPinning.lean`, `ArrowGeneral.lean`, `ArrowBase.lean`).
  - The Gibbard–Satterthwaite scenario, Proposition 1 to Corollary 2. Corollary 2 takes Gibbard's 1977 theorem as a hypothesis (`JointDraws.lean`, `Rankings.lean`, `GSScenario.lean`, `GSTopTwo.lean`, `GSCorollary.lean`).
- **C (cycles and twists).**
  - Propositions 1–5 and remark (d) of *Cycles and Twists* (`ValueSpaces.lean`, `ProbLine.lean`, `CircleTournaments.lean`, `Nerve.lean`).
  - Propositions 1–3 of *Loops of Relations* (`LoopsOfRelations.lean`).
- **D (strategy as a halting problem).**
  - Gibbard (1973), Lemma 2 and Theorem 3 (`Arrow.lean`, `Gibbard73.lean`, `Diagonal.lean`, `Dichotomy.lean`).
  - Theorem 6, with Gibbard's 1978 Corollary 2 as a hypothesis (`Lotteries.lean`).
  - Burial (`Burial.lean`).
  - The certificates of Proposition 4 (`RationalDiagonal.lean`).
  - Proposition 5 (`NonTight.lean`).
  - The summary and its update rule behind Proposition 5′ (`SummaryAutomaton.lean`).
- **G (CORE).** The draw, the decomposition of holdings, the theorem for one dimension, the mean of the peaks with the members' value under efficiency, the mean rule, safe agreements (parts 1 and 2), the veto-kept floor and the stages of the call game (`CoreDraw.lean`).
- **Strategic information.** Propositions 1–3, the Smith set, and the steps of Proposition 4 (`LeaderRule.lean`); Propositions 5 and 6, which derive the best replies from the weights of ties, and the counting of Proposition 4 for an abstract sequence of leaders (`StrategicInformation.lean`).

## 1. Foundations to build on

These are definitions and toolkits that several later items need. Doing them first keeps later files from each bringing their own encoding.

1. **Arrow's scenario as an instance of `Scenarios.lean`.**
   - The Gibbard–Satterthwaite scenario is already an instance (`GSScenario.lean`). `ArrowGeneral.Model` is not yet: the step is to show that its models are the empirical models of a scenario in the frame.
   - Value: Theorems 5 and 5′ become statements about the frame, and the placements of the two scenarios at level 3 can be stated side by side.
   - Effort: small to moderate.
2. **One frame for two-player game forms.**
   - `NonTight.lean` (matrices with utilities in ℕ), `SummaryAutomaton.lean` (Finset-based), `RationalDiagonal.lean` (lists) and `Gibbard73.lean` (n players, relations) each define strategies, best replies and rational diagonals in their own way.
   - Work: a common definition of tightness, strict Nash strategies and rational diagonals for two players, with bridges from the existing files. `Rankings.lean` did the same for rankings.
   - Value: Propositions 5″, 5‴ and 7 and the assembly of Proposition 5′ (Sections 2 and 3) can then be stated once.
   - Effort: moderate.
3. **Lotteries and joint draws as a toolkit.**
   - The sufficient direction of Lemma 3: a joint draw exists when λ(a) ≥ μ(a) + ν(a) − 1 for every candidate. It is a transport argument of Hall type.
   - Moving the couplings and kernels out of `JointDraws.lean` into a file of their own.
   - Value: the reduction proposition of *Consistency as an Extension Problem*, Section 3c (conditions J and E), needs both directions of Lemma 3.
   - Effort: small to moderate.
4. **The discrete degree for three alternatives** (*The Global Form*).
   - What it is: a loop of a voter's rankings around the hexagon, and the winding of the social ranking along it.
   - Lemmas 1–3 of *The Global Form*:
     - invariance under IIA;
     - the degrees sum to the winding of the diagonal;
     - rigidity: under IIA every degree is −1, 0 or 1.
   - Value: thread B rests on these. They are the base of the following:
     - Arrow's theorem as a degree (Proposition 1 there);
     - Gibbard–Satterthwaite in the same form (Lemmas 5–6, Proposition 3);
     - the stages of *Equivariant Obstructions* for three alternatives (Propositions 1–4).
   - Effort: moderate. Everything is finite: six rankings, steps of one transposition.

## 2. Nearly finished: complete these

1. **Strategic Information, Proposition 4.** The steps are in `LeaderRule.lean`; the counting, for an abstract sequence of leaders, and the best replies in the finite corner (Proposition 6) are in `StrategicInformation.lean`. Left:
   - the walk itself: leaders and runners-up as the top two eligible tallies, so that the hypotheses of `walk_settles` and `settled_in` follow from the steps;
   - a bridge between the two encodings, positions in `LeaderRule.lean` and real utilities in `StrategicInformation.lean`.

   Effort: small to moderate.
2. **The corollary of *What Cannot Be Defined from Inside*** (`notes/alignment/undefinability.md`, Section 6). A procedure that composes finite game forms is again a finite game form, so Theorem 3 applies to it. This goes on top of `Dichotomy.lean`. Effort: small.
3. **Proposition 5″ of *Walls and Strategy*.** It concerns one explicit 6 × 6 form with three outcomes:
   - the form is tight and not dictatorial;
   - under every pair of strict preferences, each player has a strict Nash strategy.

   This is a finite check by `decide`, in the style of `RationalDiagonal.lean`. It is the counterexample that bounds Proposition 5′. Effort: small.
4. **The Equality Criterion, Propositions 1 and 2** (`notes/equality-criterion.md`).
   - Proposition 1 follows from Theorem 5′: with anonymity, which the criterion includes, a mixture of dictatorships is uniform random dictatorship, and that fails the criterion.
   - Proposition 2 follows from Gibbard (1977) in the same way, with the theorem as a hypothesis as in `GSCorollary.lean`; Pareto-optimality gives the unanimity that `cor2` needs.

   Effort: small.
5. **Covers and division, Proposition 1** (`notes/covers-and-division.md`). The sections of a loop are the sections of its k-fold cover fixed by ℤ/k. It extends `LoopsOfRelations.lean`. Proposition 2 and the corollary, the converse of division, are a moderate further step. Effort: small, then moderate.
6. **The reduction proposition of *Consistency as an Extension Problem*, Section 3c.** It needs only Item 1.3. Effort: small once Lemma 3 has both directions.
7. **The call game as one tree** (*CORE and the Formal Results*, Section 3g).
   - Its stages are checked.
   - Open: subgame perfection on the whole tree, and the uniqueness of the values when each proposer's best acceptable lotteries fix the others' values.

   Effort: moderate.

## 3. Main claims that still rest on proofs by hand or on computation

These are the results the project's claims stand on, by thread. Details below them are not listed.

- **A. The electorate scenario passes through all four levels** (*Consistency as an Extension Problem*, Sections 3c–3d). The claim, for three alternatives:
  - no deterministic rule from 8 voters;
  - no lottery rule drawn jointly from 9;
  - models without a global section at 8.

  The impossibility side is a certificate: three joins around the doubled Condorcet profile for lotteries, and a case split on ten profiles for deterministic rules. Checking these in Lean on top of `JoinLotteries.lean` is moderate. The existence side needs the models found by search as data, which is heavier.
- **B. Arrow's theorem as a degree, and the stages of the symmetry problem for three alternatives** (*The Global Form*, Propositions 1–3; *Equivariant Obstructions*, Propositions 1–4).
  - These are discrete and rest on Item 1.4.
  - For four alternatives, Theorem 10 (local rules have at most one voter of non-zero degree) and Proposition 14 rest on computations of the permutohedron's fillings. A certificate check would be large.
- **D. Proposition 5′: every totally tight form, and every game of perfect information, admits a rational diagonal.** The proof combines three parts:
  - the structure theorem of Boros, Gurvich, Makino and Papp, taken from the literature;
  - a reduction to at most seven outcomes;
  - two exact searches.

  The summary and the update rule are checked. Next:
  - state the theorem and the reduction in the frame of Item 1.2;
  - take the structure theorem as a hypothesis;
  - check the searches, a large step.

  Proposition 5‴, the exact criterion for three outcomes (Theorems A and B of the note *A tight form without a rational diagonal*), is proved by hand and is a moderate target. Proposition 7, approval with a veto, is small to moderate; it also bears on Section 3g of the CORE note.
- **G. CORE.**
  - The proposition on concave loss (Section 3b): invertibility and positivity of distance matrices. Large.
  - The theorem that on a line the random ballot is the only strategy-proof rule that harms no one (Section 3h). It is moderate with the characterisation of Ehlers, Peters and Storcken as a hypothesis. Without it, it is large.
  - Cautious proposers (Section 3h): moderate.
  - Strassen's characterisation of safe agreements (Section 3f, part 3): large.
- **The two theorems taken as hypotheses.**
  - Gibbard (1977), used in `GSCorollary.lean` and in Item 2.4.
  - Gibbard (1978), Corollary 2, used in `Lotteries.lean`.

  Each is large. Removing them would make Corollary 2 of the scenario note and Theorem 6 of *Walls and Strategy* unconditional.

## Not planned

- **The homotopy-theoretic results of *Equivariant Obstructions*:** Propositions 5, 5′ and 6, Theorem 7, Lemma 8 and Proposition 9. They use cup products, the Whitehead square and Steenrod squares on spheres, which Mathlib does not offer in usable form. The same holds for Proposition 6 of *Cycles and Twists* (comparison complexes as spheres, quotients as projective spaces).
- **The count over all 18,138 two-player game forms.** It would need a formal proof that the enumeration is complete. Items 1.2 and 3 (thread D) are the better targets.
