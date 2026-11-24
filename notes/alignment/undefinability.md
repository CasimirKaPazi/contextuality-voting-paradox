# What Cannot Be Defined from Inside

*Working note for thread T1 of the alignment roadmap. It restates Theorems 3 and 6 of* Walls and Strategy *as a statement about shared goals, makes their hypotheses explicit, adds one elementary corollary on revising rules, and marks what the statement does not reach. The theorems are cited from that draft; the corollary is proved here; the reading in terms of goals and definability is interpretation.*

## 1. The claim to be made precise

The alignment roadmap starts from the view that no goal shared by everyone can be conclusively defined: any definition could be turned to someone's advantage. The claim is not that no good outcome exists. It is that no fixed definition, applied by the participants themselves, secures one. This note asks how much of that social choice can state exactly.

What it can state concerns definitions that are *procedures*: fixed ways of turning what the participants say and do into an outcome. That a shared goal must take this form is the modelling step the roadmap leaves open (Section 2 there); it is assumed here.

## 2. Setting

A **game form** has finitely many participants, each with a finite set of strategies, and assigns to each profile of strategies one of finitely many outcomes, or, in the version with chance, a lottery over them. A strategy is a pure strategy in the game-theoretic sense, so sequential procedures are included, with contingency plans as strategies. A participant has a preference over outcomes (an ordering, possibly with ties), or a utility scale in the version with lotteries.

A strategy is **dominant** if it is a best reply to every profile of the others' strategies; the form is **straightforward** if every participant has a dominant strategy at every preference, and **dictatorial** if some participant can force every outcome. These are Gibbard's definitions.

A **strategist** for a participant is a program that receives the programs of all participants and outputs a strategy. It is **universally correct** at a preference if on every input it halts with a best reply to what the other programs output on that input.

## 3. The statement

**Theorem 3 of *Walls and Strategy*.** Every game form with at least three possible outcomes is dictatorial, or some participant at some preference has no universally correct strategist. *(Checked in Lean from Gibbard's definitions: `lean/Dichotomy.lean`.)*

**Theorem 6 of *Walls and Strategy*.** Every non-dictatorial game form with lotteries as outcomes has a participant at some utility scale without a universally correct strategist, or is straightforward and at some assignment of utility scales yields no ex ante Pareto optimal lottery in dominant strategies. *(Checked in Lean with Gibbard's 1978 Corollary 2 as an explicit hypothesis: `lean/Lotteries.lean`.)*

**Reading.** A shared goal defined as a procedure over the participants' own reports or actions has three ways out, and each has a price:

- **one participant decides**: the symmetry between participants is broken;
- **some participant cannot compute their best course** from inside, by any program that is right against all others;
- **chance settles part of the decision** and dominant strategies are restored, but then the procedure is in general inefficient ex ante: it ignores intensities of preference and the possibilities of compromise.

These are the three placements of *Where the Symmetry Goes* at the level of procedures: in the rule, in a regress, in a lottery.

## 4. From inside and from outside

The second way out is easy to misread. In a finite game the best-reply function is a definite mathematical object, and an analyst outside the game can list its equilibria. For any fixed tuple of halting programs the outcome is computed by running them. What does not exist is one program, run by a participant whose own computation is part of what is being predicted, that is right against every opponent (*Walls and Strategy*, "What the theorem does not say").

So the right course exists, but cannot be computed by those whose computation it concerns. This is the precise sense in which a goal may exist and yet not be definable: definable from outside, not from inside. The shape is that of Tarski's undefinability of truth, in which truth holds in a model and cannot be defined in a language that is part of it, rather than that of Gödel's incompleteness. *(Interpretation. Whether the analogy has been drawn before in the literature on computability and games is not checked.)*

The same distinction explains why the theorems do not exclude every defined goal. A goal stated on true utilities with an interpersonal scale, such as their sum, is well defined. It falls under the theorems as soon as it has to be pursued through what the participants report or do, and the standpoint from which it could be applied directly, with the true utilities in view, is one that no participant has.

## 5. Two senses of exploitation

"Any definition could be turned to someone's advantage" has two exact forms, and the theorems join them.

- **Manipulation.** Without a dominant strategy, a participant can gain, at some profile, by a strategy other than the one that would be best elsewhere: for voting rules, by misreporting (Gibbard 1973, Satterthwaite 1975).
- **Anticipation.** Any fixed way of acting under the procedure can be predicted and answered. In the proof of Lemma 2 the others run the participant's own program and reply to its output with a profile against which it is wrong.

Gibbard's theorem turns non-dictatorship into the first; Lemma 2 turns the first into the second. The diagonal step is shallow and known: it is the negative half of Canning's (1992) Theorem 3. The depth of the statement lies in Gibbard's theorem.

## 6. Revising the rule does not escape

A natural response is to let the participants revise the rule. The revision is itself a procedure, and the dichotomy applies to the whole.

**Corollary.** Let h be a game form whose outcomes are game forms g₁, …, g_k among the same participants, and let the composite procedure be: play h, then play the form g_j that h selects, each participant seeing the result of h. If the composite procedure can reach at least three outcomes, it is dictatorial or some participant at some preference has no universally correct strategist. The same holds for any finite depth of such composition. *(Proved here.)*

*Proof.* A strategy in the composite procedure is a strategy s_i in h together with a strategy t_i^j in each g_j, a contingency plan for every rule that may be selected. These sets are finite, and the composite assigns to each profile the outcome g_{h(s)}(t^{h(s)}), one of finitely many. So the composite procedure is a game form in Gibbard's sense, and Theorem 3 applies to it. For greater depth, compose repeatedly. ∎

The composite can be dictatorial while no g_j is, for instance when h is decided by one participant. The corollary says only that the dichotomy survives at the level of the whole. It is the exact form, for fixed procedures, of "resolved at one level, reappearing one level up". A process with no bound on the depth of revision is not a game form in this sense, and the corollary says nothing about it.

## 7. Rational others, and two conditions under which the barrier can vanish

Lemma 2 lets the others' programs be arbitrary. If they are required to be rational, each with a fixed preference and playing a best reply in the play that occurs, the barrier remains on many forms but not all (*Walls and Strategy*, Propositions 4 to 5‴):

- it remains on every two-player form that is not tight, and on every totally tight form and game of perfect information (by computer-assisted search);
- it can vanish on tight forms with a **common veto**, an outcome that either participant can impose. With three outcomes this is the only way it can vanish (Proposition 5‴); with four or more it is open.

Separately, it can vanish when moves are taken **in visible turns** and rationality is sequential: in the procedure in which one participant vetoes and the other then picks, backward induction gives the first a correct and computable choice in every case (*Walls and Strategy*, "Simultaneity").

Both conditions bear on consensus procedures. A fallback that anyone can invoke resembles a common veto, and deliberation in visible turns has less of the obstruction than a simultaneous vote. In CORE the fallback that anyone can invoke is a random exclusion, which imposes a lottery rather than an outcome, so Proposition 5‴ does not apply to it directly. For lotteries the simplest case is settled (*Walls and Strategy*, Proposition 7): in approval with a veto, where a lottery settles ties among commonly approved proposals, a fixed fallback removes the barrier against rational others for any number of participants, since approving exactly what is worth more than the fallback is always right. A fallback that reads ideals declared along with the votes brings it back. Whether CORE's random exclusion behaves like a fixed fallback depends on whether what follows the exclusion is fixed; this remains a question for thread T3. *(The first two statements are proved or computed; the rest is interpretation.)*

## 8. What the statement does not reach

- **Changing goals.** Preferences are fixed during play. Goals that change through the interaction are outside the theorems.
- **Open deliberation.** Outcomes and strategies are finite and given in advance. A deliberation in which proposals may introduce options that were on no list is not a game form. The theorems bound every way of formalising it as one, and say nothing about the open process itself (*CORE and the Formal Results*, Section 4).
- **Unbounded revision.** The corollary of Section 6 covers any finite depth, not a process without bound.
- **From goals to procedures.** That a goal shared by everyone must be a procedure over reports is assumed (Section 1).

Nor does the statement say that no good outcome exists, that strategic behaviour is always harmful, or that chance is the right exit. It says that a fixed procedure cannot avoid all three costs, and that revising it by another fixed procedure does not change this.

## 9. Open points

1. Check whether the reading of Section 4, existence from outside and non-computability from inside as undefinability in Tarski's sense, has a precedent, for instance in the literature following Binmore (1987) and Anderlini (1990).
2. Formalise the corollary of Section 6 in Lean on top of `lean/Dichotomy.lean`. It needs only that the composite of finite game forms is a finite game form.
3. Does the rational-opponent barrier survive composition? Composition introduces visible turns, which by Section 7 can remove it. Which composites keep it is not settled.
4. State the analogue of the corollary for Theorem 6: a composite of procedures with lotteries as outcomes is again such a procedure, so the trade-off between regress and ex ante efficiency applies to the whole.

## References

References marked † were cited from memory and have not yet been checked against the originals.


- Anderlini, L. (1990). Some notes on Church's thesis and the theory of games. *Theory and Decision* 29, 19–52.
- Binmore, K. (1987). Modeling rational players, part I. *Economics and Philosophy* 3, 179–214.
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41, 587–601.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10, 187–217.†
- Tarski, A. (1936). Der Wahrheitsbegriff in den formalisierten Sprachen. *Studia Philosophica* 1, 261–405.†
