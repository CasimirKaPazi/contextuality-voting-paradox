# Walls and Strategy

## Why best replies in voting cannot be computed from inside

*Draft, November 2026.*

## Abstract

A voting rule on a finite electorate is a finite table, and nothing about it is undecidable. Strategy is different: a voter's best ballot depends on the ballots of others, who in turn predict the voter's. We combine Gibbard's 1973 theorem with a diagonal argument, in substance Canning's 1992 theorem on computable rationality: every game form with at least three outcomes is either dictatorial or leaves some player, at some preference, without any program that always computes a best reply. The combination is checked in the Lean proof assistant from Gibbard's definitions, his theorem included. With opponents required to be rational in the actual play, the diagonal is Canning's condition that some player lacks a strict Nash strategy. It persists for every two-player game form that is not tight, for every totally tight form and every game of perfect information (by a reduction to at most seven outcomes and exact computer searches), and for plurality, Borda, instant runoff and Black's rule with two and three voters. It fails on some tight forms: a 6 × 6 form with three outcomes, in which either player can impose the same outcome, leaves each player a strict Nash strategy under every pair of strict preferences. For three outcomes such a common veto is necessary, and an exact criterion decides the rest. For sequential procedures under sequential rationality the diagonal disappears. Manipulation from a sincere Condorcet winner works only by crossing a wall into a cycle. With lotteries as outcomes, Gibbard's 1978 theorem gives the price of escaping: a non-dictatorial procedure either keeps the computability barrier or is inefficient ex ante. We draw the consequence for consensus procedures with a random fallback.

## 1. Introduction

Arrow's theorem is often compared with Gödel's incompleteness theorem. One mismatch stands in the way: a social welfare function on a finite electorate is a finite table, and nothing about it is undecidable. Arrow's diagonal is static and yields a contradiction. This paper locates undecidability where it does occur, in strategy. The Gibbard–Satterthwaite theorem guarantees situations in which voters must model one another, and there the halting problem applies in full.

- **Walls** (Section 2). Profiles divide into regions with and without a Condorcet winner. Manipulation from a sincere Condorcet winner is possible only by crossing into a cycle, and every deterministic rule must break the symmetry of a cycle from outside the profile.
- **The dichotomy** (Section 3). Every game form with at least three outcomes is dictatorial or has a player without a universally correct strategist (Theorem 3). The diagonal step is shallow and known (Canning 1992); the depth lies in Gibbard's theorem. Both are checked in Lean. Against rational opponents the diagonal survives on every two-player form that is not tight (Proposition 5) and, with computer searches, on every totally tight form and every game of perfect information (Proposition 5′). It fails on some tight forms with a common veto (Proposition 5″); for three outcomes Proposition 5‴ says exactly when.
- **Randomisation** (Section 4). Chance removes the barrier at each level, but with lotteries as outcomes only at the cost of ex ante efficiency (Theorem 6). A consensus procedure with a random fallback confines the barrier to deliberation and gives it a computable floor.

The companion paper *Cycles and Twists* treats the topology of a single Condorcet cycle (winding number, parity, the Klein bottle). *Four Levels of Obstruction in Social Choice* places the aggregation theorems in a hierarchy of obstructions.

We distinguish throughout between cited theorems, statements proved here, statements verified by computation, and interpretation. Alternatives, strict preferences, profiles and majority tournaments are as in *Cycles and Twists*, Section 2.

## 2. Walls

Fix the number of voters. The set of profiles is divided into regions according to the majority tournament. The winding number of each triangle of alternatives (*Cycles and Twists*, Section 4) is constant on each region and can change only where some pairwise majority changes, which with continuous weights is a tie. We call these loci *walls*.

**Proposition 1.** Let x be the Condorcet winner of a profile and let S be a set of voters each of whom prefers z to x. No change of the ballots of S makes z a Condorcet winner.

*Proof.* The members of S already rank z above x, so no change of their ballots increases the number of voters ranking z above x. Since x beats z, it still does. ∎

This fact is known in the literature on Condorcet methods. It is closely related to the *Condorcification* results of Durand, Mathieu and Noirie: for a large class of rules, electing the Condorcet winner whenever one exists makes a rule at most as manipulable by coalitions as before, while profiles with a Condorcet winner can still be manipulated under Condorcet rules. The proof does not use that ballots are strict; the formal version (`lean/Burial.lean`) allows ties and any numbers of voters and alternatives. Its consequence is that under any rule electing the Condorcet winner when one exists, a manipulation starting from a sincere Condorcet winner can succeed only by producing a profile without one: the manipulators make x lose to some third alternative ("burying" x) and rely on the resolution of the resulting cycle. Manipulation from a sincere winner is the act of moving a profile across a wall. Within a profile that already has a cycle, manipulation can also work without crossing a wall, by steering how the rule's tie-breaking resolves the cycle; the cycle is the region from which strategy cannot be excluded.

**Observation (the symmetry break is forced).** Let a rule be anonymous (it ignores the names of voters) and neutral (it commutes with renaming alternatives), and consider the profile {abc, bca, cab}. The cyclic renaming a → b → c → a maps this profile to itself, with the three ballots exchanged among the voters. An anonymous and neutral rule must therefore return an outcome fixed by the renaming. No alternative is fixed by it. Hence no deterministic rule on three alternatives and three voters is both anonymous and neutral. The argument uses only the two symmetries involved, invariance under rotating the three voters and commuting with the cyclic renaming, and the formal version (`lean/ProfileFacts.lean`) assumes only these. The renaming does fix exactly one lottery, the uniform one. Moulin (1983) determined in general for which numbers of voters and alternatives anonymous, neutral and deterministic rules exist.

Geometrically: the cyclic symmetry rotates the cycle, and a deterministic outcome is a projection onto a single alternative, which no rotation leaves in place. Every deterministic rule therefore contains a choice that breaks the symmetry — a tie-breaking order, an agenda, a status quo, the cut of *Cycles and Twists*, Section 4 — and this choice is made from outside the profile. Only the centre of the disc, the uniform lottery, is symmetric.

A fixed symmetry break is a fixed point that voters can aim at. A strategic ballot acts as a second, competing break: it moves the profile across a wall so that the rule's break resolves the resulting cycle in the voter's favour. Competing breaks cannot be ordered without a further break. This regress is the geometric form of the computability barrier of Section 3.

A rule for resolving cycles settles any fixed profile. It does not settle the problem, because the profile is produced by voters who know the rule. The Gibbard–Satterthwaite theorem states that for every non-dictatorial rule with at least three outcomes some voter stands at some profile where a change of ballot is profitable. This is where the output of the rule re-enters its input. Arrow's theorem has no such feedback: it concerns the aggregation of a given profile.

## 3. Strategy is not computable from inside

A voting rule on a finite electorate is a finite table. The preceding results concern that table. A voter choosing a ballot faces a different object: the outcome depends on the others' ballots, which depend on their predictions of the voter's own. Binmore (1987) modelled players as machines that simulate one another and argued that such a machine can predict its opponents or take part in the game, but not both. Anderlini (1990) proved that no Turing machine always plays a correct strategy against an opponent machine; Nachbar and Zame (1996) proved a related result for repeated games. Canning (1992) made the argument exact for finite games. Against all computable opponents, a computable player can be complete and rational in a class of games exactly when it has a dominant strategy in each (his Theorem 3). Against opponents that are themselves rational, it can be so exactly when it has a *strict Nash strategy*, a strategy that is a best reply to every best reply to it (his Theorem 5). We combine the first result with Gibbard's theorem and study the second for game forms.

Programs that read each other's source code are also the setting of *program equilibrium* (Tennenholtz 2004, after McAfee, Howard and Rubinstein). There a profile of programs is an equilibrium if no player gains by submitting a different program, and the equilibrium payoffs are exactly the feasible and individually rational ones. The two questions differ: program equilibrium asks for programs that are best against each other, Lemma 2 below for one program that is right against every opponent. Halpern and Pass treat players as machines whose computation has a cost, in which case Nash equilibria can fail to exist. Prasad shows that best-response functions need not be computable even in finite games whose equilibria are computable; there the obstruction comes from computable real payoffs, here from opponents who simulate the player.

**Game forms.** A game form g has finitely many players, each with a finite set of strategies, and assigns to each strategy profile one of finitely many outcomes. A strategy is *dominant* for a player with a given preference over outcomes if it is a best reply to every profile of the others' strategies. A game form is *straightforward* if every player has a dominant strategy at every preference ordering of the outcomes (orderings may contain ties), and *dictatorial* if some player has, for each outcome, a strategy that produces it whatever the others do. These are Gibbard's definitions. A strategy here is a pure strategy in the game-theoretic sense, so sequential procedures are included, with contingency plans as strategies.

**Theorem (Gibbard 1973).** Every straightforward game form with at least three possible outcomes is dictatorial.

**Strategists.** A *strategist* for player i is a program that receives the source code of the programs of all players and outputs a strategy for i. It is *universally correct* at preference P if on every input it halts and outputs a best reply, with respect to P, to the strategies that the other programs output on that input.

**Lemma 2.** If player i has no dominant strategy at P, then no strategist is universally correct for i at P.

*Proof.* For each strategy b of i choose a profile r(b) of the others' strategies to which b is not a best reply; this exists because b is not dominant. Let M be any strategist for i. For each other player k let D_k be the program that runs M on the input it has received and, if M outputs b, outputs the k-th component of r(b). On the input consisting of M and the programs D_k: if M halts with b, the others play r(b) and b is not a best reply; if M does not halt, it fails. ∎

Lemma 2 is the negative half of Canning's Theorem 3, stated for one player of a game form at one preference; the programs D_k are his "demon" algorithm. The proof is included because the formal version isolates its single assumption.

The lemma is checked in Lean in an abstract form (`lean/Diagonal.lean`). Programs enter only through what they output on each input, and the single computational assumption is that for every map f from ballots to counter-profiles there is an input on which the other programs run the strategist and answer with f of its output. No fixed-point theorem of computability is needed, and halting matters only because the strategist might not halt. The depth of Theorem 3 therefore lies in Gibbard's theorem, not in the diagonal step.

Gibbard's theorem itself is formalised as well (`lean/Gibbard73.lean`), following his Section 3 with his definitions: orderings that may contain ties, outcomes that are the range of the game form, finitely many outcomes and players, strategy sets of any size. Its input, Arrow's theorem in the form Gibbard uses, is `lean/Arrow.lean`. Theorem 3 then follows from the two in a few lines (`lean/Dichotomy.lean`), so the dichotomy is checked from Gibbard's definitions to the conclusion.

**Theorem 3.** Let g be a game form with at least three possible outcomes. Either g is dictatorial, or some player at some preference has no universally correct strategist.

*Proof.* If g is not dictatorial it is not straightforward, so some player at some preference lacks a dominant strategy. Apply Lemma 2. ∎

Straightforwardness is the condition under which no participant needs to model any other. Gibbard's theorem says this is available to everyone only under dictatorship. Theorem 3 adds that where it fails, the modelling cannot in general be completed. It is Gibbard's theorem composed with Canning's: Gibbard turns non-dictatorship into the absence of a dominant strategy, and Canning turns that into the absence of a universally correct program.

**What the theorem does not say.** For any fixed tuple of halting programs, the outcome is computed by running them. What does not exist is one program that is right against all opponents: the best-reply function, not any single play, is non-computable. An outside analyst of a finite game can list its equilibria; the obstruction concerns a participant whose own computation is part of what is to be predicted.

**Rational opponents.** In Lemma 2 the opposing programs are arbitrary. One may require that they be rational: each opponent k has a fixed preference Q_k and, in the play that occurs, uses a best reply to the strategies actually used. (They cannot be required to be universally correct, since by Lemma 2 such programs need not exist.) Say that g admits a *rational diagonal* for player i if there are preferences P for i and Q_k for the others such that for every strategy b of i there is a profile c of the others' strategies with (1) each c_k a best reply under Q_k to b and the rest of c, and (2) b not a best reply to c under P. The opponents then run M, read off b and play c; each is rational in the play that occurs, and M is wrong.

With two players this is Canning's condition. At fixed preferences P and Q, a rational diagonal for i exists exactly when i has no strict Nash strategy: for every b, some best reply of the opponent to b makes b wrong. The opponent program is Canning's "imp", a rational algorithm that makes its opponent wrong whenever it can do so at no cost to itself. With more players the opponents' replies must also form an equilibrium among themselves, as in Canning's remark on the reduced game. The question below is therefore whether, for every non-dictatorial game form with at least three outcomes, preferences can be chosen so that some player has no strict Nash strategy.

**Proposition 4 (computed).** A rational diagonal exists for

- plurality, Borda, instant runoff and Black's rule with three alternatives and two or three voters, ballots being strict rankings and ties broken by a fixed order;
- every one of the 18,138 non-dictatorial two-player game forms with three strategies per player in which all three outcomes occur.

Dictatorial and two-outcome game forms admit none, as Theorem 3 requires.

The search uses strict preferences for all players, and this restriction is what gives the rational-opponent version content. Gibbard's preference orderings allow ties. If the opponents may be indifferent among all outcomes, every strategy is a best reply for them, any profile r(b) is played by rational opponents, and the rational-opponent version reduces to Lemma 2. The open question is therefore whether opponents with *strict* preferences always suffice.

*Verification.* Exhaustive search. For the four rules, the witnesses found by the search (the preferences and a counter-profile for each ballot of the first voter) are checked in Lean (`lean/RationalDiagonal.lean`); the game-form count would also need a proof that the enumeration is complete, and is not formalised. ∎

**Tightness.** A two-player game form is *tight* if for every set S of outcomes, player 1 can force an outcome in S or player 2 can force an outcome outside S. Tight forms are exactly the forms that have an equilibrium in pure strategies for every assignment of preferences (Edmonds and Fulkerson 1970 for zero-sum preferences; Gurvich 1975 in general). A form is the normal form of a game of perfect information exactly when it is tight and rectangular, every outcome filling a box of strategy pairs (Gurvich; another proof by Abdou 1998).

**Proposition 5.** Every two-player game form that is not tight admits a rational diagonal with strict preferences, for each player.

*Proof.* Choose S such that player 1 cannot force S and player 2 cannot force its complement. Let player 1 rank the outcomes in S above all others, and let player 2 have the reverse order. Against a row b, a best reply of player 2 gives an outcome outside S, since row b does not lie inside S. In that column some row reaches S, since the column does not lie outside S. So b is not a best reply. ∎

The proof is formalised (`lean/NonTight.lean`). What remains is therefore the tight forms, which include the normal forms of games of perfect information and veto procedures. On a tight form every pair of preferences has an equilibrium, so a diagonal can only work through ties: the opponent must be indifferent between strategies yielding the same outcome, and at least one of them must refute. This is exactly the room Canning's imp needs. Exhaustive searches found no tight counterexample among two-player forms of sizes 4 × 4 with three outcomes (14.3 million forms up to relabelling), 3 × 5 with three and 3 × 4 with four outcomes, and among the three-player forms 2 × 2 × 2 and 2 × 2 × 3. In all tight forms of sizes 3 × 3 and 3 × 4 with three outcomes and 3 × 3 with four, a diagonal of one shape exists: player i ranks first an outcome x it cannot force, and the opponent ranks x last. Larger forms behave differently (Proposition 5″).

**Totally tight forms.** A form is *totally tight* if all its 2 × 2 subforms are tight. The class contains the normal forms of stopping games, in which play runs along a path and the player to move at a node may stop with that node's outcome, but not all games of perfect information. Boros, Gurvich, Makino and Papp show that deleting rows and columns holding a single outcome reduces a totally tight form either to one cell, exactly for the stopping games, or to an irreducible core. Every core has the same effectivity function: on three key outcomes each player forces any two and no single one. They describe the cores block by block.

**Proposition 5′ (computer-assisted).** Every non-dictatorial totally tight two-player game form, and every non-dictatorial game of perfect information, admits a rational diagonal with strict preferences. Moreover some player i has no strict Nash strategy under some ranking P, with the opponent's ranking either the reverse of P or P with its top moved to the bottom. In both cases i's favourite outcome is the opponent's least favourite.

*Proof outline.* For a player i and rankings P and Q, record for each strategy of i the pair (y, M): y is the opponent's favourite outcome against it, and M the best outcome for i in the columns where y occurs. The strategy is refuted exactly when M is better than y, so whether i lacks a strict Nash strategy depends only on the set of these pairs. For three outcomes a short argument by hand shows that one of four configurations, alternating between the players and between the two kinds of opponent order, always works. For any number of outcomes the same four configurations form a chain, and merging two adjacent outcomes reduces a smallest counterexample to at most seven outcomes; merging keeps a form totally tight and a tree a tree. The remaining cases are settled by exact searches. For totally tight forms, adding a row or column with a single outcome changes the set of pairs by a rule that does not refer to the rest of the form, and the structure theorem of Boros, Gurvich, Makino and Papp (every totally tight form is a single cell or a core with such lines added, with a block description of the cores) makes the search finite. For games of perfect information, the sets of pairs compose at each node of the tree, and the closure of the leaves under composition is finite. Details, scripts and the search counts: working note *The rational diagonal on totally tight game forms*, `scripts/strategy/rational_diagonal/`. ∎

No simple rule for which player works has been found: choosing the owner of the first node, the player who forces more outcomes, or a choice keyed to the outcome that appears last, works in most stopping games but not in all. On a core the loop of refutation is present at once, as in rock–paper–scissors among the three key outcomes; on a stopping game it is built node by node. *(The last sentence is interpretation.)*

**A common veto.** If both players force single outcomes, they force the same one, since a constant row and a constant column meet in a cell. Call such an outcome a *common veto*: either player can impose it. A form with a common veto is tight, since every set of outcomes or its complement contains the veto.

**Proposition 5″.** The following form, with rows for player 1 and outcomes a, b, c, is tight and not dictatorial, and under every pair of strict preferences each player has a strict Nash strategy. So neither player admits a rational diagonal.

```
c c c c c c
c b a b a a
c b c b b b
c b a c c a
c c a a a a
c b a b c b
```

*Proof.* Tightness holds because of the common veto c. For player 1 and each of the 36 pairs of strict preferences, a strict Nash strategy can be named with a one-line reason; the form is isomorphic to its transpose, so the same holds for player 2. The table is in the working note *A tight form without a rational diagonal*, and `scripts/strategy/rational_diagonal/tight_counterexample.py` checks it. ∎

**Proposition 5‴ (three outcomes).** Let a non-dictatorial two-player form have three outcomes.
- Without a common veto, some player has no strict Nash strategy under some P, with the opponent's order the reverse of P or its rotation.
- With a common veto c, read the player's strategies as rows. The player has no rational diagonal exactly when it has a row whose c-cells lie only in columns that are constant c, and, for each ordering x, y of the other two outcomes, a row holding only x and c whose c-cells lie in columns without x, and a row holding y whose y-cells lie in columns without x (or a row of the first kind without y). These are five conditions.

*Proof.* By hand, in the working note *A tight form without a rational diagonal*, Section 5; neither part uses tightness. ∎

So with three outcomes, a tight form can deny the rational diagonal only through a shared fallback that either player can impose. Every strategy then meets that fallback, and the constant lines make it safe against refutation. *(Interpretation.)* Whether forms with four or more outcomes can deny it at all is open; local searches over 7 × 7 forms with four outcomes found no example.

An example under Borda with two voters: voter 1 prefers a to b to c, voter 2 prefers b to c to a. To each of the six ballots of voter 1, voter 2 has a best reply against which voter 1 would have done better with a different ballot. The situation is matching pennies embedded in the rule.

**Simultaneity.** The rational diagonal depends on the notion of rationality. Consider the procedure in which player 1 vetoes one of three alternatives and player 2, seeing the veto, picks one of the other two. If player 2 need only use a best reply in the normal form, a rational diagonal exists for player 1 (for 12 of the 36 pairs of strict preferences), because player 2's choices after vetoes that do not occur are unconstrained. If player 2 must choose its preferred alternative after every veto (sequential rationality), backward induction gives player 1 a correct and computable choice in all 36 cases. Observed moves taken in turn remove the obstruction: the later mover reacts and does not need to simulate. Moulin's dominance-solvable voting schemes, which include voting by veto, kingmaker procedures and binary agendas under sophisticated voting, are the general class in which iterated elimination of dominated strategies settles play. The barrier of Theorem 3 belongs to simultaneous choice, which is how ballots are cast under all standard voting rules.

**Rationality refers to itself.** Canning also shows that the notion of a rational program cannot be fixed once and for all. Let R(B) be the programs that play a best reply whenever an opponent from B comes to a decision. Enlarging B shrinks R(B), so R reverses inclusion. Iterating from the set of all programs gives an increasing sequence of odd stages inside a decreasing sequence of even stages. Between them lie sets of programs within which some member is complete and rational against every member, for games with strict Nash strategies. But no such set is largest, and different choices select different equilibria (his Theorem 7 and the remarks after it). An order-reversing map iterated is the Liar's flip (*Cycles and Twists*, Section 4). Here it acts on concepts of rationality, its two limits do not meet, and choosing a set between them is a symmetry break that settles which equilibrium is played. *(The reading is interpretation; the facts are Canning's.)*

**Static and dynamic diagonals.** Prokopenko and co-authors identify three ingredients of undecidable dynamics: program–data duality, an infinite medium and negation. Aggregation of a fixed profile has negation (reversal of a preference) and, as the bit encoding of *Cycles and Twists*, Section 5, shows, a diagonal — in the profile {abc, bca, cab} each voter departs from the cycle at a different pair, and majority returns the complement — but no program–data duality and no infinite medium. The result is a contradiction in a finite object. Non-computability appears on the aggregation side only for infinite electorates, where non-dictatorial Arrovian rules exist but none is computable (Mihara 1997). Strategic voting has all three ingredients: a ballot is data produced by running the rule on a profile containing that ballot, a strategist can be answered by its negation, and the space of programs is unbounded. *(The classification of Arrow as a static and Gibbard as a dynamic diagonal is interpretation.)*

Whether strategic adjustment settles or cycles has been studied directly in iterative voting, where voters in turn make best replies to the current outcome. Convergence holds for plurality with deterministic tie-breaking under suitable restrictions and fails for other rules (Meir et al.).

## 4. Randomisation

The same move removes the obstruction at each of the levels considered.

*Preferences.* A cycle has no centre on the circle; the disc it bounds has one. The uniform lottery over a cycle, and more generally the profile's own distribution over orders, is a consistent object (*Cycles and Twists*, Section 3, remark b). The contradiction arises from requiring a deterministic answer pair by pair.

*Strategies.* Pure best replies may chase each other around a cycle without a fixed point. Mixed strategies replace the cycle by a simplex, and Brouwer's theorem gives an equilibrium (Nash).

*Reasoning.* The construction in Lemma 2 requires the opponents to predict the strategist's output. If the strategist may use private randomness and best replies are judged in expectation, the construction fails. Fallenstein, Taylor and Christiano show that machines with access to a suitably randomised ("reflective") oracle can reason about one another consistently.

*Rules.* Gibbard (1977) showed that a strategy-proof rule using chance is a mixture of unilateral and duple rules; with ex post efficiency it is random dictatorship. Under random dictatorship every voter has a dominant strategy, naming a favourite. Lemma 2 has no purchase there: no voter needs to model any other.

**Lotteries as outcomes.** Gibbard (1978) extends the 1973 theorem to game forms that assign a lottery over alternatives to each strategy profile, with players holding utility scales and evaluating lotteries by expected utility. Such a game form is straightforward if every player has a dominant strategy at every utility scale. His theorem states that a straightforward game form is, with each player restricted to the strategies that are dominant on an open set of utility scales, a probability mixture of game forms each of which is unilateral (only one player influences the outcome) or duple (only two alternatives are possible). His second corollary states that a straightforward game form which, at every assignment of utility scales, has a profile of dominant strategies yielding a lottery that is Pareto optimal ex ante, is dictatorial.

Lemma 2 does not depend on what the outcomes are; it applies unchanged with lotteries as outcomes and utility scales as preferences, the strategists remaining deterministic. Hence:

**Theorem 6.** Let g be a non-dictatorial game form with lotteries as outcomes. Then at least one of the following holds: (i) some player at some utility scale has no universally correct strategist; (ii) g is straightforward, and at some assignment of utility scales no profile of dominant strategies yields an ex ante Pareto optimal lottery.

*Proof.* If g is not straightforward, Lemma 2 gives (i). If it is, Gibbard's second corollary gives (ii). ∎

Chance in the outcome therefore removes the barrier of Theorem 3 only at the price Gibbard identified. A procedure in which nobody needs to model anybody is a mixture of unilateral and duple procedures and is in general inefficient ex ante: random dictatorship ignores intensities of preference and all possibilities of compromise. Any non-dictatorial procedure that reliably recovers those gains has a participant whose best reply cannot be computed in general. Among non-dictatorial procedures, ex ante efficiency in dominant strategies and freedom from the strategic regress exclude each other. For decision schemes on cardinal utilities the corresponding characterisation is Hylland's theorem: a strategy-proof scheme satisfying a weak unanimity condition is a random dictatorship (Hylland 1980; proof published by Dutta, Peters and Sen).

**Three placements of the symmetry.** The observation of Section 2 can be extended into a reading of the whole section *(interpretation)*. A finite total order has no non-trivial symmetry, while the Condorcet profile carries a rotation without fixed point. An aggregation that respects this rotation must send it somewhere. If the target keeps a fixed-point-free symmetry (a cyclic order, or truth values with negation), Lawvere's condition holds and the obstruction appears in the output as a paradox. If the target is rigid, the rule must break the symmetry itself, by a tie-breaker, an agenda or a dictator. If the target keeps the symmetry but every self-map has a fixed point, as on the simplex of lotteries, self-reference becomes consistent — as in Scott's models, Nash equilibria and reflective oracles — and the price is chance and, by Theorem 6, ex ante inefficiency. This is developed in the companion note *Where the Symmetry Goes*.

**Consequence for consensus procedures with a random fallback.** Consider a procedure in which participants deliberate towards a unanimously accepted proposal, possibly a lottery, and random dictatorship applies if none is found (the CORE proposal; compare Heitzig, Simmons and Constantino). The fallback is straightforward, so the strategic regress has a floor that nobody can move and nobody needs to predict. In the deliberation itself, where participants in effect bargain over lotteries with the fallback as the disagreement point, dominant strategies generally do not exist and Lemma 2 applies. This is case (i) of Theorem 6, accepted in exchange for the ex ante gains that the fallback alone forgoes. Such a procedure does not escape Gibbard's theorems. It confines the non-computable part to an open-ended process and gives that process a computable floor. By the observation on simultaneity, a deliberation conducted in visible turns has less of the obstruction than a simultaneous vote. This is consistent with the suggestion of Abramsky, Levin, Stepney and co-authors that time unfolds the paradoxes of self-reference into a process. *(Interpretation.)*

## 5. Relation to other work

*Computability.* Canning (1992) is the closest prior result: Lemma 2 is the negative half of his Theorem 3, and the rational diagonal is his condition of Theorem 5, the absence of a strict Nash strategy. What is added here is the combination with Gibbard's theorem for game forms, the lottery version, and the question whether strict preferences always produce the condition. Nachbar (1997) and Foster and Young (2001) show related tensions between prediction and optimisation in repeated games. Besides Binmore, Anderlini and Nachbar–Zame on games, Mihara on infinite electorates, program equilibrium (Tennenholtz), machine games with costly computation (Halpern and Pass) and the computability of equilibria of finite games with real payoffs (Prasad), there is a large literature on the complexity of computing manipulations (starting with Bartholdi, Tovey and Trick), which concerns the difficulty of a well-defined finite problem and is distinct from Theorem 3.

*Tight game forms.* Edmonds and Fulkerson, Gurvich and co-authors characterise the two-player game forms with pure equilibria for all preferences as the tight ones, and study structured subclasses such as totally tight forms and veto voting; Proposition 5 reduces the rational-opponent question to this class, and Proposition 5′ uses the structure theorem of Boros, Gurvich, Makino and Papp for the totally tight ones. Proposition 5″ answers the question negatively for tight forms in general. Gurvich and Naumova compute, on tight forms with strict preferences, equilibria in which one player uses a *lexicographically safe* strategy computed from its own preference alone. A strict Nash strategy must be a best reply to every best reply of the opponent; wherever the searches of Section 3 found a rational diagonal on a tight form, the lexicographically safe strategy of the player concerned is therefore not one.

*Formal proofs.* Nipkow formalised Arrow's theorem and the Gibbard–Satterthwaite theorem for social choice functions in Isabelle, and Holliday, Norman and Pacuit built a framework for voting theory in Lean. We have not found a formalisation of Gibbard's theorem for game forms with his definitions before `lean/Gibbard73.lean`.

*Topology and diagonals.* Baryshnikov and Root (2024) give a topological proof of the Gibbard–Satterthwaite theorem, in which each voter carries one oriented cycle of the profile space and the dictator is the one voter of degree one; strategy-proofness enters there only through monotonicity, so the topology captures the wall that Gibbard–Satterthwaite shares with Arrow, not the regress of Section 3. Livson and Prokopenko relate Arrow's theorem to incompleteness through diagonalisation; the static and dynamic diagonals of Section 3 separate their setting from the one here.

*Companion papers.* *Cycles and Twists* gives the winding number and the location of non-orientability; *Four Levels of Obstruction in Social Choice* places Arrow's theorem and its relatives in a hierarchy of obstructions.

## 6. Status and open problems

| Statement | Status | Lean |
|---|---|---|
| Proposition 1 (burial) | proved, known; holds with ties | `Burial.lean` |
| Observation in Section 2 (no anonymous, neutral deterministic rule at the Condorcet profile) | proved, elementary; general case Moulin 1983 | `ProfileFacts.lean`, with only the two symmetries used |
| Symmetry breaks as competing fixed points, regress | interpretation | |
| Lemma 2 | proved here; the negative half of Canning (1992), Theorem 3 | `Diagonal.lean` |
| Gibbard (1973) | cited | `Gibbard73.lean`, with `Arrow.lean` |
| Theorem 3 (dichotomy) | proved here from Gibbard 1973 and Lemma 2; we have not found the combination with Gibbard's theorem stated elsewhere | `Dichotomy.lean` |
| Proposition 4 (rational diagonal) | computed, small cases | `RationalDiagonal.lean`, certificates for the four rules |
| Proposition 5 (forms that are not tight) | proved here | `NonTight.lean` |
| Tight forms up to 4 × 4 and 3 × 5: no counterexample, one shape of diagonal | computed, small cases | |
| Proposition 5′ (totally tight forms; games of perfect information) | proved here, by hand for three outcomes; for more, a proved reduction to at most seven outcomes and exact computer searches; for forms with a core, it rests on the published description of cores | |
| Proposition 5″ (a tight form without a rational diagonal) | proved here, checkable by hand; computed independently | |
| Proposition 5‴ (three outcomes: common veto necessary, exact criterion) | proved here; checked against brute force | |
| Sequential example (veto then pick) | computed | `RationalDiagonal.lean`, the count 12 of 36 |
| Theorem 6 (lotteries: regress or ex ante inefficiency) | proved here from Gibbard 1978 and Lemma 2 | `Lotteries.lean`, with Gibbard's Corollary 2 as an assumed hypothesis |
| Common Lawvere frame; static versus dynamic diagonal; reading of random fallback | interpretation | |

**Open problems.**

1. *Rational diagonal on tight forms.* For two players with strict preferences the answer is no in general (Proposition 5″), yes for totally tight forms and games of perfect information (Proposition 5′), and settled for three outcomes (Proposition 5‴). Open: whether a form with four or more outcomes can lack a rational diagonal, and if so whether it needs a common veto; whether tight forms with the recombination property of the working note always admit one; veto voting, monotone bargaining and the Jordan forms as tight classes to settle; a hand proof of Proposition 5′ beyond three outcomes. For three or more players the question is open beyond the small cases searched.
2. *Randomised strategists.* What form of Theorem 3, if any, holds when strategists randomise? The existence of mixed equilibria suggests that the barrier becomes one of computing or coordinating on an equilibrium.
3. *Aggregation without closure.* Characterise procedures that are not total functions from profiles to outcomes (open-ended deliberation with a fallback) in the terms used here: which obstructions do they avoid, and which do they relocate?

## References

- Abdou, J. (1998). Rectangularity and tightness: a normal form characterization of perfect information extensive game forms. *Mathematics of Operations Research* 23, 553–567.
- Abramsky, S. et al. (2025). Open questions about time and self-reference in living systems. arXiv:2508.11423.
- Anderlini, L. (1990). Some notes on Church's thesis and the theory of games. *Theory and Decision* 29, 19–52.
- Bartholdi, J., Tovey, C. and Trick, M. (1989). The computational difficulty of manipulating an election. *Social Choice and Welfare* 6, 227–241.
- Baryshnikov, Y. and Root, J. (2024). A topological proof of the Gibbard–Satterthwaite theorem. *Economics Letters* 234, 111447. arXiv:2309.03123.
- Binmore, K. (1987). Modeling rational players, part I. *Economics and Philosophy* 3, 179–214.
- Boros, E., Gurvich, V., Makino, K. and Papp, D. (2010). Acyclic, or totally tight, two-person game forms: characterization and main properties. *Discrete Mathematics* 310, 1135–1151. Preprint: DIMACS Technical Report 2008-10.
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Durand, F., Mathieu, F. and Noirie, L. (2016). Can a Condorcet rule have a low coalitional manipulability? *ECAI 2016*, 707–715.
- Dutta, B., Peters, H. and Sen, A. (2007). Strategy-proof cardinal decision schemes. *Social Choice and Welfare* 28, 163–179; erratum 30 (2008), 701–702.
- Edmonds, J. and Fulkerson, D. R. (1970). Bottleneck extrema. *Journal of Combinatorial Theory* 8, 299–306.
- Fallenstein, B., Taylor, J. and Christiano, P. (2015). Reflective oracles: a foundation for classical game theory. arXiv:1508.04145.
- Foster, D. P. and Young, H. P. (2001). On the impossibility of predicting the behavior of rational agents. *PNAS* 98, 12848–12853.
- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41, 587–601.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Gurvich, V. A. (1975). Solution of positional games in pure strategies. *USSR Computational Mathematics and Mathematical Physics* 15(2), 74–87.
- Gurvich, V. and Naumova, M. (2023). Computing lexicographically safe Nash equilibria in finite two-person games with tight game forms given by oracles. *Discrete Applied Mathematics* 340, 53–68.
- Halpern, J. Y. and Pass, R. (2015). Algorithmic rationality: game theory with costly computation. *Journal of Economic Theory* 156, 246–268.
- Heitzig, J., Simmons, F. W. and Constantino, S. M. (2024). Fair group decisions via non-deterministic proportional consensus. *Social Choice and Welfare*.
- Holliday, W. H., Norman, C. and Pacuit, E. (2021). Voting theory in the Lean theorem prover. arXiv:2110.08453.
- Hylland, A. (1980). Strategy proofness of voting procedures with lotteries as outcomes and infinite sets of strategies. Mimeo, University of Oslo.
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- Livson, O. and Prokopenko, M. (2025). Comparing and contrasting Arrow's impossibility theorem and Gödel's incompleteness theorem. arXiv:2504.06589.
- Meir, R., Polukarov, M., Rosenschein, J. S. and Jennings, N. R. (2017). Acyclic games and iterative voting. *Artificial Intelligence* 252, 100–122.
- Mihara, H. R. (1997). Arrow's theorem and Turing computability. *Economic Theory* 10, 257–276.
- Moulin, H. (1979). Dominance solvable voting schemes. *Econometrica* 47, 1337–1352.
- Moulin, H. (1983). *The Strategy of Social Choice*. North-Holland.
- Nachbar, J. H. (1997). Prediction, optimization, and learning in repeated games. *Econometrica* 65, 275–309.
- Nachbar, J. H. and Zame, W. R. (1996). Non-computable strategies and discounted repeated games. *Economic Theory* 8, 103–122.
- Nipkow, T. (2009). Social choice theory in HOL: Arrow and Gibbard–Satterthwaite. *Journal of Automated Reasoning* 43, 289–304.
- Prasad, K. (2009). The rationality/computability trade-off in finite games. *Journal of Economic Behavior and Organization* 69, 17–26.
- Prokopenko, M. et al. (2019). Self-referential basis of undecidable dynamics: from the Liar paradox and the halting problem to the edge of chaos. *Physics of Life Reviews* 31, 134–156.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10, 187–217.
- Tennenholtz, M. (2004). Program equilibrium. *Games and Economic Behavior* 49, 363–373.
- *Cycles and Twists*; *Four Levels of Obstruction in Social Choice* (companion drafts, this repository).
