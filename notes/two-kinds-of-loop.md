# Two Kinds of Loop: Condorcet, the Liar, and Strategy

*A working note on how the impossibility results of social choice relate to self-reference, contextuality and topology. It records the current picture, which parts are established, which were checked by small computations, and which are conjecture.*

## Summary

- A Condorcet cycle and the Liar paradox are both loops that fail to close, but they fail in different ways. The Liar comes back **flipped**: its obstruction counts mod 2. A Condorcet cycle comes back **one floor higher**: its obstruction is an integer winding number.
- In the sheaf-theoretic sense of Abramsky and Brandenburger, a Condorcet cycle is contextual only when alternatives are placed on an **unbounded** line. On any finite line no valid model exists; on a circle the cycle is simply consistent.
- The Klein bottle of Livson, Pritam and Prokopenko has a single seam, and the seam is the Condorcet cycle, where the two windings +1 and −1 are identified. Orientation flips exactly when a loop crosses that seam. Forgetting which way is up turns the integer obstruction into a mod-2 one.
- Strategy lives on the **walls** between profiles that have a Condorcet winner and profiles that have a cycle. Gibbard–Satterthwaite says such walls cannot be avoided by any non-dictatorial rule.
- The outcome of strategic voting is not computable *from inside*: a voter who must predict a process that includes their own prediction faces a halting-type problem (Binmore 1987; Anderlini 1990). Combined with Gibbard's 1973 theorem this becomes exact: every game form with at least three outcomes is either dictatorial or has a voter for whom no program always finds a best reply. Arrow is a static diagonal; Gibbard opens a dynamic one.
- Randomness cuts the regress. Lotteries fill the hole in preference space, mixed strategies guarantee equilibria, and a random fallback is a point nobody can steer. In CORE, the remaining regress moves into deliberation, where it is lived through in time rather than computed.

## 1. Aggregation as gluing

Cover a space with overlapping patches and put local data on each patch. The data agree on every overlap. Can they be glued into one global object that restricts to each patch? When they cannot, the situation is *contextual*: locally consistent, globally impossible. The Penrose triangle is the standard image.

Vocabulary: a *section* is data on a patch; a *global section* is data on the whole that restricts correctly; *no-signalling* is the requirement that two patches tell the same story about their overlap. Without no-signalling the data disagree locally, and the gluing question does not arise.

For preference aggregation the patches are the pairs of alternatives, the data say which of the two is placed above the other, and a global section is one placement of all alternatives. A Condorcet cycle — a beats b, b beats c, c beats a — is fine on every pair and impossible as a whole.

## 2. The shape of the value space decides everything

Encode alternatives as measurements whose outcomes are positions in some value space, and the pairs decided by majority as contexts. Then:

- **Finite line** (a ladder with a top rung): *no valid model exists.* The context {a,b} says a is above the bottom rung; the context {c,a} says a is below the top rung; their overlaps disagree. More decisively: whatever occupies the highest occupied rung must, by the cycle, be beaten by something higher. Pruning removes values from the ends until nothing remains. This holds for every finite line and every total cycle on any number of alternatives.
- **Circle**: the cycle is *consistent*, globally. Place a, b, c around a ring, each slightly ahead of the next. This is rock-paper-scissors.
- **Unbounded line** (integers or reals): the contexts agree on overlaps, because an alternative could sit anywhere, yet no global placement exists. Only here is the Condorcet cycle *strongly contextual*.

So the impossibility depends on asking for a linear order with no ends. Read through Lawvere: the map "one step up" has no fixed point on an unbounded line, but on a finite ladder "one step up, stop at the top" always has one — the top rung. *(The finite-line result was checked by computation; the Lawvere reading is interpretation.)*

**Consequence.** The machinery of sheaf-theoretic contextuality — Čech cohomology invariants, logical Bell inequalities, the completeness theorem for non-contextual polytopes — is built for finite outcome sets. In every finite encoding a Condorcet cycle is either locally inconsistent or not contextual at all, so this machinery has nothing to detect. The obstruction has to be described differently.

## 3. The staircase: winding number

Above a circle stands an infinite spiral staircase, one floor per turn. The staircase is the unbounded line, coiled; projecting it down gives the circle. *Lifting* a path means choosing the matching path on the staircase.

Walk a → b → c → a on the circle and follow the lift:

- **Transitive preferences**: up, up, then down. The walk returns to a on the same floor. The loop closes upstairs, so a ranking exists.
- **Condorcet cycle**: every step goes up. The walk returns to a one floor higher. Closed below, open above.

The number of floors gained is the **winding number**: 0 for every strict order, +1 and −1 for the two Condorcet cycles. A ranking exists exactly when it is zero. Topologically this is first cohomology of a loop with integer coefficients — an integer read off by going once around a hole.

## 4. The twist: the Liar

For the Liar, replace the staircase by a two-sheeted cover with a half-twist, like the edge of a Möbius band. Once around and true has become false; twice around and it is restored. The obstruction counts mod 2. In Abramsky's treatment the Liar cycle of length four is the PR box, which he describes as a discrete Möbius strip; the cohomological witnesses of contextuality are of this kind.

So there are two loop obstructions:

| | Liar | Condorcet |
|---|---|---|
| Going around once | flips | climbs one floor |
| Obstruction counts in | mod 2 | integers |
| Needs | two values | an unbounded order |
| Fixed-point-free map | negation (order 2) | shift (infinite order) |

## 5. Where the Klein bottle comes from

Strict preferences over three alternatives form an annulus whose two boundary circles are the two Condorcet cycles (winding +1 and −1). Livson, Pritam and Prokopenko treat a cycle as one contradictory object — "every alternative is preferred to itself" — identified with its own reverse. Gluing the two boundary circles with the required twist gives a Klein bottle (Theorem 4 of their paper); with cycles realised as faces, the real projective plane.

A computation on the annulus (six triangles, one per strict order) settles how orientation behaves. Of the six possible ways of gluing the two rims, three give a torus and three a Klein bottle. The annulus itself is orientable, and in every Klein gluing **each seam edge flips orientation**, while in every torus gluing none does. Therefore:

> A loop of social preferences on the Klein bottle reverses orientation exactly when it passes through the contradictory object an odd number of times.

The seam is the place where winding +1 and winding −1 are identified — where the direction of the staircase is forgotten. If up and down cannot be told apart, the only thing left to count is odd or even. This is the precise sense in which the integer obstruction becomes a mod-2 one.

An earlier, looser formulation — "the non-orientability class *is* the winding number mod 2" — mixes two types: winding belongs to a single relation, orientation to a loop of relations. The statement above is the correct version.

Two further facts fit the same picture. In the bit encoding used by Livson and Prokopenko (comparisons read around the triangle), transitivity says the three bits are *not all equal*; for n alternatives this holds on every triangle, since a tournament is transitive exactly when it has no 3-cycle. Not-all-equal is unchanged when every bit flips, i.e. when every preference reverses, and the two forbidden patterns form one orbit of that flip. Identifying a cycle with its reverse is dividing out this built-in symmetry. After the division, a strict order up to reversal is determined by which alternative sits in the middle, and a cycle is the case with no middle. Separately, the gluing that yields the Klein bottle is not the naive comparison-by-comparison reversal (that gives a torus) but reversal together with reversing the order of composition along a chain — the way reversal acts in an opposite category.

## 6. Strategy lives on the walls

The space of profiles divides into regions where the staircase closes (a Condorcet winner exists) and regions where it does not (a cycle). The winding number cannot change gradually; it stays constant inside a region and can only jump where some pairwise comparison is exactly tied. The ties are walls.

An elementary fact makes this precise. Suppose the sincere profile has a Condorcet winner x and some group prefers y. They already rank y above x, so no change of ballots helps y against x: y can never become the Condorcet winner. Their only lever is to make x lose to some third alternative, creating a cycle, and to hope the cycle is resolved in favour of y (*burying* x). For every rule that elects the Condorcet winner when there is one, manipulation from a sincere winner works only by pushing the profile across a wall.

A tie-breaker settles a fixed cycle. It does not settle the problem, because the profile is not fixed: it is produced by voters who know the rule, so the output feeds back into the input. Gibbard–Satterthwaite says that unless all the walls belong to one voter — the dictator — some voter somewhere stands on a wall and can step across. The standard proofs work by locating the pivotal voter, the one whose single ballot change flips the outcome; this voter plays the role of the diagonal element.

## 7. Inside and outside: the strategy cannot be computed

The rule is a finite lookup table and always halts. The *strategy* is different. A voter deciding how to vote must predict an outcome that depends on everyone's choices, including predictions of their own prediction. Seen from outside, a finite voting game is a finite object whose equilibria an analyst can list. Seen from inside, the predictor is part of what is predicted.

This is a theorem in game theory, though not usually stated for voting:

- Binmore (1987) modelled players as Turing machines simulating one another and argued that a machine can predict its opponents perfectly, or participate in the game, but not both; even a halting oracle does not help against another oracle machine.
- Anderlini (1990): no Turing machine always plays the correct strategy given its opponent's choice.
- Nachbar and Zame (1996): in many discounted repeated games there are computable strategies with no computable best response.
- Morgenstern's Holmes and Moriarty is the classical version; formalised, Holmes's best-reply function is not computable, an instance of the halting problem.

Prokopenko and co-authors list three ingredients for undecidable dynamics: program–data duality, access to an infinite medium, and the ability to implement negation. All three are present once voters strategise. The ballot (data) is chosen by running the rule (program) on a profile containing that ballot; "whatever is expected to win, make it lose" is the Liar machine; and the infinite medium is the unbounded space of reasoning procedures. Arrow, by contrast, aggregates a given profile and has no self-application. Hence:

- **Arrow is a static diagonal.** Finite, it yields a contradiction (the forced cycle), not undecidability. Genuine non-computability enters only with infinitely many voters, where non-dictatorial rules exist but none is computable (Mihara 1997).
- **Gibbard opens a dynamic diagonal.** The rule's wall guarantees that some voter's best ballot depends on the others'; the diagonal turns that dependence into non-computability. *Gibbard supplies the wall; the halting problem lives on it.* This can be stated exactly.

### The dichotomy, stated exactly

*Setting.* A game form g assigns an outcome to every profile of strategies (ballots); there are finitely many players, strategies and outcomes. A *strategist* for voter i is a program that receives the source code of all participating programs and outputs a ballot. A strategist is *universally correct* for preference P if it halts on every input and always outputs a best reply, with respect to P, to the ballots the other programs actually output.

**Lemma (diagonal).** If voter i with preference P has no P-dominant strategy, then no program is universally correct for i at P.

*Proof.* No ballot is dominant, so for each ballot b there is a profile r(b) of the others' ballots against which b is not a best reply; fix one such choice for every b (a finite table). Given any candidate strategist M, let every other voter k run the program D_k: read all source codes, run M on them, and when M outputs b, output the k-th entry of r(b). If M halts with b, the others play r(b), against which b is not a best reply. If M does not halt, it fails by definition. ∎

**Theorem.** Let g be a game form with at least three possible outcomes. Either g is dictatorial, or some voter at some preference has no universally correct strategist.

*Proof.* Gibbard (1973): every straightforward game form — one giving every voter, at every preference, a dominant strategy — with at least three possible outcomes is dictatorial. If g is not dictatorial, it is not straightforward, so some voter at some preference has no dominant strategy. Apply the lemma. ∎

This is the dichotomy in exact form: either one fixed point decides everything (the dictator, or a rule with only two outcomes), or there is a participant for whom the result of strategic reasoning cannot be computed in advance. The lemma is the same diagonal argument as Binmore's and Anderlini's. The added observation is that Gibbard's hypothesis, straightforwardness, is exactly the condition under which no participant ever needs to model another, and its failure is exactly where the diagonal applies.

*Scope.*
- In the lemma the opposing programs D_k are arbitrary; they need not act on sincere preferences. A stronger version requires them to be *rational in the actual play*: each opponent has a fixed preference and casts a best reply to what the others actually cast. (They cannot be required to be universally correct, since by the same lemma such programs need not exist.) The diagonal survives if there are opponent preferences such that, for every ballot b of voter i, some profile of mutually best-responding opponent ballots makes b a wrong choice. This is a finite condition and was checked by exhaustive search: it holds, for suitable preferences, under plurality, Borda, instant runoff and Black's rule with two or three voters and three alternatives, and in every one of the 18,138 non-dictatorial two-player game forms with three strategies each and three outcomes. Dictatorial and two-outcome controls give no cases, as they must. A general proof is not yet available.
- The stronger version depends on the notion of rationality. In sequential procedures with perfect information, such as "one voter vetoes an alternative, the other then picks from the remaining two", the diagonal survives Nash-style rationality, because the opponent's choices off the actual path are unconstrained. Under *sequential* rationality, where the later voter must choose its preferred option at every point, backward induction gives the first voter a computable correct move in every case. Turn-taking with visible moves cuts the loop: the later mover reacts instead of simulating. The halting-type obstruction belongs to simultaneous choice, which is how ballots are cast in all standard voting rules.
- What is non-computable is the best-reply *function*: no single program is right against all opponents. Any single play is computable — for a fixed tuple of halting programs, running them gives the outcome. This is the inside/outside distinction made exact.
- If the strategist may randomise and best replies are judged in expectation, the deterministic diagonal fails, because the opponents cannot predict the coin. This is the formal counterpart of the coin that cuts the regress (Section 8).

*For CORE.* Random dictatorship gives every voter a dominant strategy — naming the true favourite — so the lemma has nothing to act on at the fallback: no participant needs to model anyone there. In the deliberation, where participants bargain over lotteries, dominant strategies generally do not exist, and the lemma applies. The regress is relocated, not removed.

Halting versus looping is visible in practice. In iterative voting, where voters repeatedly best-respond to the current outcome, plurality with deterministic tie-breaking converges, while several rules such as Copeland and Ranked Pairs admit best-response cycles (Meir and co-authors).

## 8. Filling in the hole

The same move resolves each layer:

- **Preferences.** A cycle has no centre on the circle. The uniform lottery over the cycle sits at the centre of the filled-in disc. The profile's own distribution over orders is always a consistent global object; the contradiction appears only when a deterministic answer is demanded pair by pair. (Every profile satisfies p(a≻b) + p(b≻c) + p(c≻a) ≤ 2, Boole's condition for the cycle; the Condorcet profile sits exactly on it, and majority rounding pushes it to 3.)
- **Strategies.** With pure strategies, best responses can chase each other around a circle with no fixed point, as in rock-paper-scissors. Mixed strategies fill the circle into a disc, Brouwer's theorem gives a fixed point, and a Nash equilibrium exists.
- **Reasoning.** If Holmes knows Moriarty will flip a coin, Holmes can do no better than flip one too, and the regress ends. Reflective oracles — oracles that answer some queries randomly — let idealised reasoners model each other without paradox.

**For CORE.** The random fallback is the coin that cuts the regress. Random dictatorship is strategyproof (Gibbard 1977), so there is no wall at the fallback and nobody needs to simulate anyone in order to face it. The lever is not destroyed; it moves into deliberation, where participants bargain over which lottery to accept. There the regress is not computed in advance but lived through in time — matching the observation of Abramsky, Levin, Stepney and co-authors that time unfolds the paradoxes of self-reference into a process.

## 9. Status of the claims

**Established (cited results).** Arrow; Gibbard–Satterthwaite; Gibbard's characterisation of strategyproof random rules; Livson–Prokopenko on forced total cycles and on Arrow and Gödel; Livson–Pritam–Prokopenko on non-orientability; Abramsky–Brandenburger, Abramsky–Carù and Abramsky (2020) on contextuality, disagreement and logical Bell inequalities; Binmore, Anderlini, Nachbar–Zame on non-computable strategies; Fishburn, Kirman–Sondermann and Mihara on infinite electorates; Meir et al. on iterative voting.

**Shown here by elementary argument and small computation.** A Condorcet cycle admits no valid finite-line model, is consistent on a circle, and is strongly contextual only on an unbounded line. The obstruction is the integer winding number. On the three-alternative Klein bottle, orientation flips exactly at the seam, which is the identified Condorcet cycle. From a sincere Condorcet winner, manipulation is possible only by creating a cycle. Transitivity on every triangle is a not-all-equal constraint, invariant under global reversal. Every non-dictatorial game form with at least three outcomes has a voter for whom no program is a universally correct strategist (Gibbard 1973 plus the diagonal lemma, Section 7), with opponents allowed to be arbitrary programs; with opponents required to be rational in the actual play, verified exhaustively for small cases, and shown to fail for sequential procedures under sequential rationality.

**Interpretation and conjecture.** Lawvere's theorem as the common frame (negation for the Liar, shift for Condorcet). Arrow as a static and Gibbard as a dynamic diagonal. The pivotal voter as the diagonal element. The reading of CORE's fallback as what cuts the strategic regress.

**Not supported.** Calling the Condorcet majority relation a "social PR box" holds only in the unbounded-line encoding. In binary encodings, including judgment aggregation, majority produces a single assignment that violates a constraint, which is not contextuality. Encodings that record only "chosen or not" from each menu (Zeng and Zahn 2015) classify ordinary transitive pairwise choice as contextual as well, and cannot distinguish a cycle from an order. In the Contextuality-by-Default framework, binary "does a win?" variables make a Condorcet majority look like context-dependent marginals rather than contextuality.

## Open questions

1. Prove the rational-opponent version of the dichotomy in Section 7 for all non-dictatorial simultaneous game forms with at least three outcomes (exhaustive search on small cases found no counterexample), and determine what survives when strategists may randomise.
2. Extend the seam picture beyond three alternatives, using the appendix of Livson–Pritam–Prokopenko: is non-orientability still located exactly at the contradictory objects, and how do cycles on sub-triangles enter?
3. Find a formal frame in which the Liar (negation, mod 2) and Condorcet (shift, integers) are two instances of one Lawvere-type statement, with the mod-2 reduction as a map between them.
4. Characterise which aggregation rules make the strategic regress terminate (halting) and which can loop, beyond the known iterative-voting results, and where a random fallback places a rule.

## References

**Social choice and topology**
- Arrow, K. J. (1963). *Social Choice and Individual Values*, 2nd ed. Yale University Press.
- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41(4), 587–601.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45(3), 665–681.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10(2), 187–217.
- Livson, O. and Prokopenko, M. (2025). Comparing and contrasting Arrow's impossibility theorem and Gödel's incompleteness theorem. arXiv:2504.06589.
- Livson, O. and Prokopenko, M. (2025). Arrow's impossibility theorem as a generalisation of Condorcet's paradox. arXiv:2510.09076.
- Livson, O., Pritam, S. and Prokopenko, M. (2026). The non-orientable topology of Condorcet's paradox. arXiv:2601.07283.
- Abramsky, S. (2014). Arrow's theorem by arrow theory. arXiv:1401.4585.
- Dietrich, F. and List, C. (2007). Arrow's theorem in judgment aggregation. *Social Choice and Welfare* 29, 19–33.
- Kirman, A. P. and Sondermann, D. (1972). Arrow's theorem, many agents, and invisible dictators. *Journal of Economic Theory* 5, 267–277.
- Mihara, H. R. (1997). Arrow's theorem and Turing computability. *Economic Theory* 10, 257–276.

**Contextuality**
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Abramsky, S. (2017). Contextuality: at the borders of paradox. In *Categories for the Working Philosopher*, Oxford University Press. arXiv:2011.04899.
- Abramsky, S. and Carù, G. (2019). Non-locality, contextuality and valuation algebras: a general theory of disagreement. *Phil. Trans. R. Soc. A* 377, 20190036. arXiv:1911.03521.
- Abramsky, S. (2020). Classical logic, classical probability, and quantum mechanics. arXiv:2010.13326.
- Abramsky, S., Barbosa, R. S., Kishida, K., Lal, R. and Mansfield, S. (2015). Contextuality, cohomology and paradox. CSL 2015. arXiv:1502.03097.
- Carù, G. (2017). On the cohomology of contextuality. QPL 2016, EPTCS 236.
- Kishida, K. (2023). Gödel, Escher, Bell: contextual semantics of logical paradoxes. In *Samson Abramsky on Logic and Structure in Computer Science and Beyond*, Springer.
- Zeng, W. and Zahn, P. (2015). Contextuality and the weak axiom in the theory of choice. arXiv:1512.02668.
- Kujala, J. V. and Dzhafarov, E. N. (2016). Proof of a conjecture on contextuality in cyclic systems with binary variables. *Foundations of Physics* 46, 282–299.

**Self-reference, computability and strategy**
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- Binmore, K. (1987). Modeling rational players, part I. *Economics and Philosophy* 3, 179–214.
- Anderlini, L. (1990). Some notes on Church's thesis and the theory of games. *Theory and Decision* 29, 19–52.
- Nachbar, J. H. and Zame, W. R. (1996). Non-computable strategies and discounted repeated games. *Economic Theory* 8, 103–122.
- Prokopenko, M., Harré, M., Lizier, J., Boschetti, F., Peppas, P. and Kauffman, S. (2019). Self-referential basis of undecidable dynamics: from the Liar paradox and the halting problem to the edge of chaos. *Physics of Life Reviews* 31, 134–156.
- Fallenstein, B., Taylor, J. and Christiano, P. (2015). Reflective oracles: a foundation for classical game theory. arXiv:1508.04145.
- Meir, R., Polukarov, M., Rosenschein, J. S. and Jennings, N. R. (2017). Acyclic games and iterative voting. *Artificial Intelligence* 252, 100–122. arXiv:1606.05837.
- Abramsky, S., Banzhaf, W., Caves, L., Levin, M., Machado, P., Ofria, C., Stepney, S. and White, R. (2025). Open questions about time and self-reference in living systems. arXiv:2508.11423.
