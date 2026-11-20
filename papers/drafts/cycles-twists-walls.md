# Cycles, Twists and Walls

## Intermediate results on the common form of the social choice impossibilities

*Draft, November 2026.*

## Abstract

It is often suggested that the impossibility theorems of social choice (Arrow, Gibbard–Satterthwaite) belong to the same family as the Liar paradox, Gödel's incompleteness and the halting problem. We make part of this precise and mark where it fails. First, we treat a Condorcet cycle as a local-to-global problem in the sense of sheaf-theoretic contextuality and show that the answer depends on the shape of the space in which alternatives are placed: on a bounded line no valid model exists, on a circle the cycle is consistent, and only on an unbounded line is the cycle contextual. Its obstruction is an integer winding number, where the Liar's is a parity. Second, we locate the non-orientability found by Livson, Pritam and Prokopenko: on the three-alternative Klein bottle, orientation reverses exactly at the seam formed by the Condorcet cycle, where the two directions of winding are identified. Third, we show that strategy carries a genuine halting-type obstruction: by Gibbard's 1973 theorem and a diagonal argument, every game form with at least three outcomes is either dictatorial or leaves some voter without any program that always computes a best reply. The static impossibility (Arrow) is a finite contradiction; the dynamic one (Gibbard) is a computability barrier. Randomisation removes the obstruction at each level, at a price: by Gibbard's 1978 theorem, a non-dictatorial procedure with lotteries as outcomes either retains the computability barrier or is inefficient ex ante. Results are elementary; several are verified by exhaustive computation on small cases, and open problems are stated.

## 1. Introduction

Three statements are commonly made together.

1. Arrow's theorem and the Gibbard–Satterthwaite theorem are "like" Gödel's theorem.
2. All of these are instances of Lawvere's fixed-point theorem, or of a topological obstruction.
3. Randomised or open-ended procedures escape them.

Each has support in the literature. Livson and Prokopenko formalise a correspondence between Arrow and Gödel in which profiles aggregating to complete Condorcet cycles play the role of Gödel sentences; they show that such cycles are forced whenever Arrow's other conditions hold; and, with Pritam, that the contradiction corresponds to the non-orientability of a surface. Abramsky gives a categorical form of Arrow's theorem and, separately, a general theory of contextuality in which the Liar cycle appears as a discrete Möbius strip. Gibbard characterises the strategy-proof randomised rules.

What is missing is an account of how these pieces fit, and in particular of two mismatches. Arrow's theorem concerns finite objects: a social welfare function on a finite electorate is a finite table, and nothing about it is undecidable. And a Condorcet cycle does not look like the Liar: the Liar flips a truth value, while a cycle climbs an order.

This paper reports three intermediate results that address these mismatches.

- **The obstruction of a Condorcet cycle is a winding number** (Sections 3–4). It is integer-valued and requires an unbounded order. It is not detected by the finite machinery of contextuality.
- **The parity obstruction arises by forgetting direction** (Section 5). Identifying a cycle with its reverse turns the integer into a parity, and this is where non-orientability sits.
- **Undecidability enters with strategy, not with aggregation** (Sections 6–7). Arrow's diagonal is static and yields a contradiction. Gibbard's theorem guarantees a situation in which voters must model one another, and there the halting problem applies in full.

Section 8 shows that randomisation plays the same role at each level, and what this implies for consensus procedures with a random fallback.

We distinguish throughout between cited theorems, statements proved here, statements verified by exhaustive computation on small cases, and interpretation.

## 2. Setting

**Alternatives and preferences.** Let X be a finite set of at least three alternatives. A *strict preference* is a linear order on X. A *tournament* on X assigns to each pair {x, y} one of x ≻ y or y ≻ x. A tournament is *transitive* if it is a linear order; otherwise it contains a 3-cycle. For three alternatives there are eight tournaments: six linear orders and two cycles.

**Profiles and majority.** A profile is a list of strict preferences, one per voter. The *majority tournament* of a profile (with an odd number of voters) puts x ≻ y when more voters rank x above y than the reverse. A profile has a *Condorcet cycle* if its majority tournament is not transitive.

**Local-to-global language.** Following Abramsky and Brandenburger, a *scenario* consists of a set of variables, a set O of possible values, and a family of *contexts*, each a set of variables considered together. A (possibilistic) *model* assigns to each context C a non-empty set S(C) of allowed joint values of the variables in C. The model is *compatible* (no-signalling) if, whenever two contexts share a variable, they allow the same set of values for it. A *global section* is an assignment of values to all variables whose restriction to every context C lies in S(C). A compatible model with no global section is *strongly contextual*.

**Encoding a tournament.** Given a tournament T on X and a value set O with a binary relation "x is placed above y", written x ▷ y, take the alternatives as variables and the pairs {x, y} as contexts. A model *realises T* if, for every pair with x ≻ y in T, S({x, y}) is a non-empty set of value pairs (u, v) with u ▷ v. A global section is then a placement of all alternatives in O that respects T.

Three value spaces are considered:

- the **bounded line**: O totally ordered with u ▷ v iff u > v, where every non-empty subset used has a maximum (in particular, any finite chain);
- the **circle**: O = ℝ/ℤ with u ▷ v iff u − v, reduced to (−½, ½], lies in (0, ½) — "u is less than half a turn ahead of v";
- the **unbounded line**: O = ℝ (or ℤ) with u ▷ v iff u > v.

## 3. The value space decides the nature of the obstruction

Let T contain a directed cycle a₁ ≻ a₂ ≻ … ≻ aₙ ≻ a₁, n ≥ 3.

**Proposition 1 (bounded line).** No compatible model on a bounded line realises T.

*Proof.* Suppose one does. By compatibility each alternative aᵢ on the cycle has a well-defined non-empty set Mᵢ of allowed values. Let m be the maximum of M₁ ∪ … ∪ Mₙ, attained in Mᵢ. Consider the context {aᵢ₋₁, aᵢ} (indices mod n), in which aᵢ₋₁ ≻ aᵢ. Since m ∈ Mᵢ, some allowed pair has aᵢ at m, and then aᵢ₋₁ is at a value strictly above m, which belongs to Mᵢ₋₁. This contradicts maximality. ∎

So on a bounded line the cycle is not "locally fine, globally impossible": the local pieces already fail to agree on their overlaps. Whatever occupies the top must be beaten by something higher.

**Proposition 2 (circle).** On the circle, T restricted to the cycle has a global section.

*Proof.* Place aᵢ at −i/n. Then aᵢ − aᵢ₊₁ = 1/n ∈ (0, ½) for n ≥ 3, including the closing step from aₙ to a₁. ∎

This is the rock–paper–scissors arrangement. On a circle there is nothing paradoxical about a cycle.

**Proposition 3 (unbounded line).** On the unbounded line, the model with S({x, y}) = {(u, v) : u > v} for every pair with x ≻ y is compatible and has no global section. It is strongly contextual.

*Proof.* Every alternative is allowed every value in every context containing it, so the model is compatible. A global section would give real numbers with u₁ > u₂ > … > uₙ > u₁. ∎

**Remarks.**

(a) *Finite methods do not see the obstruction.* The cohomological invariants of contextuality, logical Bell inequalities and the completeness theorem for the non-contextual polytope are formulated for finite outcome sets. By Proposition 1, any finite linear value set gives no model at all. Encodings with binary outcomes fare no better: recording for each pair only which alternative wins gives a single global assignment that violates transitivity, which is a constraint violation and not contextuality; recording for each menu which alternatives are chosen makes transitive and cyclic choice patterns alike fail to glue. The Condorcet obstruction becomes contextuality only when transitivity is built into the geometry of an unbounded value space.

(b) *A classical bound.* For three alternatives and any profile, the fractions of voters satisfy p(a ≻ b) + p(b ≻ c) + p(c ≻ a) ≤ 2, since each linear order satisfies at most two of the three statements. This is an instance of Boole's conditions of possible experience (a logical Bell inequality). The profile {abc, bca, cab} attains the bound with 2/3 on each pair. Majority rounds each 2/3 to 1 and so produces the value 3. The profile itself is a consistent global object — a distribution over linear orders. The contradiction is created by deciding each pair separately and deterministically.

(c) *Reading through Lawvere.* Lawvere's theorem implies that self-application into a space is obstructed when the space has a self-map without fixed points. On the unbounded line, "one step up" has none. On a bounded line, "one step up, stopping at the top" always has one. Proposition 1 is that fixed point. *(Interpretation.)*

## 4. The winding number

The unbounded line covers the circle: the map ℝ → ℝ/ℤ wraps the line around the circle like a spiral staircase over its ground plan. A placement on the circle *lifts* if it is the image of a placement on the line that realises the same tournament.

Let alternatives a, b, c be placed on the circle so that all three pairs are comparable. For each step of the closed walk a → b → c → a, let d be the difference (current minus next), reduced to (−½, ½). Define

  w = d(a,b) + d(b,c) + d(c,a).

Since the walk closes, w is an integer.

**Proposition 4.** For three alternatives, w = 0 if the realised tournament is transitive, and w = +1 or −1 if it is one of the two cycles. A circle placement lifts to the line if and only if w = 0.

*Proof.* If the tournament is the cycle a ≻ b ≻ c ≻ a, all three differences lie in (0, ½), so w ∈ (0, 3/2) and hence w = 1; the reverse cycle gives −1. If the tournament is transitive, two differences have one sign and the third the other, so w lies strictly between −1 and 1 and hence w = 0. A lift exists exactly when the three lifted steps sum to zero on the line, which is w = 0. ∎

So a ranking exists exactly when a loop that closes on the circle also closes on the staircase. A Condorcet cycle returns one floor higher. The obstruction is an element of the first cohomology of the triangle with integer coefficients.

This is the integer, combinatorial counterpart of a known decomposition. Jiang, Lim, Yao and Ye decompose real-valued pairwise comparison data on a graph orthogonally into a gradient part (a consistent ranking; on complete data, the Borda count), a curl part (cycles on triangles) and a harmonic part (cycles not visible on any triangle). Saari's profile coordinates separate, for three candidates, the components on which all methods agree from the reversal components, which distinguish positional rules, and the Condorcet components, which carry the cycles. The winding number is the sign-level shadow of the curl and harmonic parts: it records whether the cyclic part of the pairwise data dominates on a triangle.

**Comparison with the Liar.** The Liar cycle x₁ = x₂, …, xₙ₋₁ = xₙ, xₙ = ¬x₁ is obstructed in the same way with a different cover: a two-sheeted cover with a half twist. Going around once exchanges true and false; twice restores them. Its obstruction lies in cohomology with coefficients mod 2.

| | Liar cycle | Condorcet cycle |
|---|---|---|
| Going around once | flips the value | climbs one level |
| Obstruction | parity (ℤ/2) | winding number (ℤ) |
| Values needed | two | an unbounded order |
| Fixed-point-free map | negation, of order two | shift, of infinite order |
| Finite contextuality tools | apply | do not apply |

The two are loops of the same kind over different covers. Section 5 shows how one becomes the other.

**The point at infinity.** The line is also the circle with one point removed. In that view a cycle must pass through the missing point: one of its steps leaves at +∞ and returns at −∞, and w counts these passages with sign. Choosing where to cut the circle open decides which step of a cycle is broken, and so who wins; in voting this is the power of an agenda or a tie-breaking order. A cut is an absolute frame of reference imposed on the alternatives from outside the profile. *(Interpretation.)*

## 5. Where non-orientability sits

Livson, Pritam and Prokopenko model strict preferences on three alternatives by a simplicial complex: the six vertices are the strict comparisons x ≺ y, and three comparisons span a triangle when a single strict order contains them. The six orders give six triangles forming an annulus. Its two boundary circles are the two Condorcet cycles, the triples of comparisons with winding +1 and −1. They then treat a cycle as one contradictory object, in which every alternative is preferred to itself, and identify it with its reverse. Gluing the two boundary circles accordingly gives a Klein bottle; filling the cycle in as a face gives the real projective plane. Given Arrow's other conditions, they show that non-dictatorship corresponds to non-orientability.

We ask where on this surface orientation is lost.

**Proposition 5 (computed).** The annulus is orientable. Of the six ways of identifying its two boundary circles by a bijection of vertices, three yield a torus and three a Klein bottle. Fix an orientation of the annulus. In each Klein bottle gluing, every edge of the seam joins two triangles whose orientations disagree; in each torus gluing, none does.

*Verification.* Exhaustive computation on the six-triangle complex. ∎

**Corollary.** On the Klein bottle, a closed path of strict orders reverses orientation exactly when it crosses the seam an odd number of times.

The seam is the Condorcet cycle, and it is the place where winding +1 and winding −1 have been declared the same. Reversing every preference sends w to −w; a surface on which a cycle equals its reverse has no consistent distinction between up and down on the staircase of Section 4. What survives of an integer when its sign is forgotten along a loop is its parity. In this sense the parity obstruction of the Liar and the non-orientability of the preference surface are the integer obstruction of Section 4 with the direction of winding forgotten.

Two remarks support this reading.

(a) *Transitivity is "not all equal".* Read the three comparisons around the triangle as bits. The six orders are exactly the triples that are not constant; the two cycles are 000 and 111. For n alternatives the same holds on every triple, since a tournament is transitive exactly when it has no 3-cycle. The not-all-equal constraint is invariant under flipping all bits, that is, under reversing all preferences, and the two forbidden triples form one orbit. Identifying a cycle with its reverse is dividing by a symmetry the constraint already has. It is also not a linear constraint mod 2, unlike the equations of a Liar cycle, which is a further reason the standard cohomological tools for contextuality do not transfer directly.

(b) *The gluing reverses composition.* Reversing each comparison separately (x ≺ y to y ≺ x) is one of the three torus gluings. The Klein bottle arises when reversal also reverses the order in which comparisons are chained, as reversal acts in an opposite category: the chain 1 ≺ 2 ≺ 3 read as (12, 23) is matched with (32, 21). We reconstructed the gluing from the worked example in Livson et al.; it coincides with one of the three Klein bottle gluings.

The statement "non-orientability is winding mod 2" should not be read as an identity of invariants: winding belongs to a single tournament, orientation to a loop of them. The corollary is the correct form.

The same reduction is visible in the homology of the surfaces. The annulus has first homology ℤ: one integer hole, around which the winding is counted. Gluing the two Condorcet cycles orientably gives the torus, with first homology ℤ ⊕ ℤ; gluing them with the reversal gives the Klein bottle, with ℤ ⊕ ℤ/2, so that one of the two integer classes has become a class of order two. Filling the identified cycle in as a face gives the real projective plane, whose first homology is ℤ/2 alone: no integer class remains, only parity. Unlike the torus, neither the Klein bottle nor the projective plane has a second integral homology class; neither bounds an inside.

## 6. Walls

Fix the number of voters. The set of profiles is divided into regions according to the majority tournament. The winding number of Section 4 is constant on each region and can change only where some pairwise majority changes, which with continuous weights is a tie. We call these loci *walls*.

**Proposition 6.** Let x be the Condorcet winner of a profile and let S be a set of voters each of whom prefers z to x. No change of the ballots of S makes z a Condorcet winner.

*Proof.* The members of S already rank z above x, so no change of their ballots increases the number of voters ranking z above x. Since x beats z, it still does. ∎

This fact is known in the literature on Condorcet methods. Its consequence is that under any rule electing the Condorcet winner when one exists, a manipulation starting from a sincere Condorcet winner can succeed only by producing a profile without one: the manipulators make x lose to some third alternative ("burying" x) and rely on the resolution of the resulting cycle. Manipulation from a sincere winner is the act of moving a profile across a wall. Within a profile that already has a cycle, manipulation can also work without crossing a wall, by steering how the rule's tie-breaking resolves the cycle; the cycle is the region from which strategy cannot be excluded.

**Observation (the symmetry break is forced).** Let a rule be anonymous (it ignores the names of voters) and neutral (it commutes with renaming alternatives), and consider the profile {abc, bca, cab}. The cyclic renaming a → b → c → a maps this profile to itself, with the three ballots exchanged among the voters. An anonymous and neutral rule must therefore return an outcome fixed by the renaming. No alternative is fixed by it. Hence no deterministic rule on three alternatives and three voters is both anonymous and neutral. The renaming does fix exactly one lottery, the uniform one. Moulin (1983) determined in general for which numbers of voters and alternatives anonymous, neutral and deterministic rules exist.

Geometrically: the cyclic symmetry rotates the cycle, and a deterministic outcome is a projection onto a single alternative, which no rotation leaves in place. Every deterministic rule therefore contains a choice that breaks the symmetry — a tie-breaking order, an agenda, a status quo, the cut of Section 4 — and this choice is made from outside the profile. Only the centre of the disc, the uniform lottery, is symmetric.

A fixed symmetry break is a fixed point that voters can aim at. A strategic ballot acts as a second, competing break: it moves the profile across a wall so that the rule's break resolves the resulting cycle in the voter's favour. Competing breaks cannot be ordered without a further break. This regress is the geometric form of the computability barrier of Section 7.

A rule for resolving cycles settles any fixed profile. It does not settle the problem, because the profile is produced by voters who know the rule. The Gibbard–Satterthwaite theorem states that for every non-dictatorial rule with at least three outcomes some voter stands at some profile where a change of ballot is profitable. This is where the output of the rule re-enters its input. Arrow's theorem has no such feedback: it concerns the aggregation of a given profile.

## 7. Strategy is not computable from inside

A voting rule on a finite electorate is a finite table. The preceding results concern that table. A voter choosing a ballot faces a different object: the outcome depends on the others' ballots, which depend on their predictions of the voter's own. Binmore (1987) modelled players as machines that simulate one another and argued that such a machine can predict its opponents or take part in the game, but not both. Anderlini (1990) proved that no Turing machine always plays a correct strategy against an opponent machine; Nachbar and Zame (1996) proved a related result for repeated games. We combine this argument with Gibbard's theorem.

**Game forms.** A game form g has finitely many players, each with a finite set of strategies, and assigns to each strategy profile one of finitely many outcomes. A strategy is *dominant* for a player with a given preference over outcomes if it is a best reply to every profile of the others' strategies. A game form is *straightforward* if every player has a dominant strategy at every preference ordering of the outcomes (orderings may contain ties), and *dictatorial* if some player has, for each outcome, a strategy that produces it whatever the others do. These are Gibbard's definitions. A strategy here is a pure strategy in the game-theoretic sense, so sequential procedures are included, with contingency plans as strategies.

**Theorem (Gibbard 1973).** Every straightforward game form with at least three possible outcomes is dictatorial.

**Strategists.** A *strategist* for player i is a program that receives the source code of the programs of all players and outputs a strategy for i. It is *universally correct* at preference P if on every input it halts and outputs a best reply, with respect to P, to the strategies that the other programs output on that input.

**Lemma 7.** If player i has no dominant strategy at P, then no strategist is universally correct for i at P.

*Proof.* For each strategy b of i choose a profile r(b) of the others' strategies to which b is not a best reply; this exists because b is not dominant. Let M be any strategist for i. For each other player k let D_k be the program that runs M on the input it has received and, if M outputs b, outputs the k-th component of r(b). On the input consisting of M and the programs D_k: if M halts with b, the others play r(b) and b is not a best reply; if M does not halt, it fails. ∎

**Theorem 8.** Let g be a game form with at least three possible outcomes. Either g is dictatorial, or some player at some preference has no universally correct strategist.

*Proof.* If g is not dictatorial it is not straightforward, so some player at some preference lacks a dominant strategy. Apply Lemma 7. ∎

Straightforwardness is the condition under which no participant needs to model any other. Gibbard's theorem says this is available to everyone only under dictatorship. Theorem 8 adds that where it fails, the modelling cannot in general be completed.

**What the theorem does not say.** For any fixed tuple of halting programs, the outcome is computed by running them. What does not exist is one program that is right against all opponents: the best-reply function, not any single play, is non-computable. An outside analyst of a finite game can list its equilibria; the obstruction concerns a participant whose own computation is part of what is to be predicted.

**Rational opponents.** In Lemma 7 the opposing programs are arbitrary. One may require that they be rational: each opponent k has a fixed preference Q_k and, in the play that occurs, uses a best reply to the strategies actually used. (They cannot be required to be universally correct, since by Lemma 7 such programs need not exist.) Say that g admits a *rational diagonal* for player i if there are preferences P for i and Q_k for the others such that for every strategy b of i there is a profile c of the others' strategies with (1) each c_k a best reply under Q_k to b and the rest of c, and (2) b not a best reply to c under P. The opponents then run M, read off b and play c; each is rational in the play that occurs, and M is wrong.

**Proposition 9 (computed).** A rational diagonal exists for

- plurality, Borda, instant runoff and Black's rule with three alternatives and two or three voters, ballots being strict rankings and ties broken by a fixed order;
- every one of the 18,138 non-dictatorial two-player game forms with three strategies per player in which all three outcomes occur.

Dictatorial and two-outcome game forms admit none, as Theorem 8 requires.

*Verification.* Exhaustive search. ∎

An example under Borda with two voters: voter 1 prefers a to b to c, voter 2 prefers b to c to a. To each of the six ballots of voter 1, voter 2 has a best reply against which voter 1 would have done better with a different ballot. The situation is matching pennies embedded in the rule.

**Simultaneity.** The rational diagonal depends on the notion of rationality. Consider the procedure in which player 1 vetoes one of three alternatives and player 2, seeing the veto, picks one of the other two. If player 2 need only use a best reply in the normal form, a rational diagonal exists for player 1 (for 12 of the 36 pairs of strict preferences), because player 2's choices after vetoes that do not occur are unconstrained. If player 2 must choose its preferred alternative after every veto (sequential rationality), backward induction gives player 1 a correct and computable choice in all 36 cases. Observed moves taken in turn remove the obstruction: the later mover reacts and does not need to simulate. The barrier of Theorem 8 belongs to simultaneous choice, which is how ballots are cast under all standard voting rules.

**Static and dynamic diagonals.** Prokopenko and co-authors identify three ingredients of undecidable dynamics: program–data duality, an infinite medium and negation. Aggregation of a fixed profile has negation (reversal of a preference) and, as the bit encoding of Section 5 shows, a diagonal — in the profile {abc, bca, cab} each voter departs from the cycle at a different pair, and majority returns the complement — but no program–data duality and no infinite medium. The result is a contradiction in a finite object. Non-computability appears on the aggregation side only for infinite electorates, where non-dictatorial Arrovian rules exist but none is computable (Mihara 1997). Strategic voting has all three ingredients: a ballot is data produced by running the rule on a profile containing that ballot, a strategist can be answered by its negation, and the space of programs is unbounded. *(The classification of Arrow as a static and Gibbard as a dynamic diagonal is interpretation.)*

Whether strategic adjustment settles or cycles has been studied directly in iterative voting, where voters in turn make best replies to the current outcome. Convergence holds for plurality with deterministic tie-breaking under suitable restrictions and fails for other rules (Meir et al.).

## 8. Randomisation

The same move removes the obstruction at each of the levels considered.

*Preferences.* A cycle has no centre on the circle; the disc it bounds has one. The uniform lottery over a cycle, and more generally the profile's own distribution over orders, is a consistent object (Section 3, remark b). The contradiction arises from requiring a deterministic answer pair by pair.

*Strategies.* Pure best replies may chase each other around a cycle without a fixed point. Mixed strategies replace the cycle by a simplex, and Brouwer's theorem gives an equilibrium (Nash).

*Reasoning.* The construction in Lemma 7 requires the opponents to predict the strategist's output. If the strategist may use private randomness and best replies are judged in expectation, the construction fails. Fallenstein, Taylor and Christiano show that machines with access to a suitably randomised ("reflective") oracle can reason about one another consistently.

*Rules.* Gibbard (1977) showed that a strategy-proof rule using chance is a mixture of unilateral and duple rules; with ex post efficiency it is random dictatorship. Under random dictatorship every voter has a dominant strategy, naming a favourite. Lemma 7 has no purchase there: no voter needs to model any other.

**Lotteries as outcomes.** Gibbard (1978) extends the 1973 theorem to game forms that assign a lottery over alternatives to each strategy profile, with players holding utility scales and evaluating lotteries by expected utility. Such a game form is straightforward if every player has a dominant strategy at every utility scale. His theorem states that a straightforward game form is, with each player restricted to the strategies that are dominant on an open set of utility scales, a probability mixture of game forms each of which is unilateral (only one player influences the outcome) or duple (only two alternatives are possible). His second corollary states that a straightforward game form which, at every assignment of utility scales, has a profile of dominant strategies yielding a lottery that is Pareto optimal ex ante, is dictatorial.

Lemma 7 does not depend on what the outcomes are; it applies unchanged with lotteries as outcomes and utility scales as preferences, the strategists remaining deterministic. Hence:

**Theorem 10.** Let g be a non-dictatorial game form with lotteries as outcomes. Then at least one of the following holds: (i) some player at some utility scale has no universally correct strategist; (ii) g is straightforward, and at some assignment of utility scales no profile of dominant strategies yields an ex ante Pareto optimal lottery.

*Proof.* If g is not straightforward, Lemma 7 gives (i). If it is, Gibbard's second corollary gives (ii). ∎

Chance in the outcome therefore removes the barrier of Theorem 8 only at the price Gibbard identified. A procedure in which nobody needs to model anybody is a mixture of unilateral and duple procedures and is in general inefficient ex ante: random dictatorship ignores intensities of preference and all possibilities of compromise. Any non-dictatorial procedure that reliably recovers those gains has a participant whose best reply cannot be computed in general. Among non-dictatorial procedures, ex ante efficiency in dominant strategies and freedom from the strategic regress exclude each other.

**Three placements of the symmetry.** The observation of Section 6 can be extended into a reading of the whole section *(interpretation)*. A finite total order has no non-trivial symmetry, while the Condorcet profile carries a rotation without fixed point. An aggregation that respects this rotation must send it somewhere. If the target keeps a fixed-point-free symmetry (a cyclic order, or truth values with negation), Lawvere's condition holds and the obstruction appears in the output as a paradox. If the target is rigid, the rule must break the symmetry itself, by a tie-breaker, an agenda or a dictator. If the target keeps the symmetry but every self-map has a fixed point, as on the simplex of lotteries, self-reference becomes consistent — as in Scott's models, Nash equilibria and reflective oracles — and the price is chance and, by Theorem 10, ex ante inefficiency. This is developed in the companion note *Where the Symmetry Goes*.

**Consequence for consensus procedures with a random fallback.** Consider a procedure in which participants deliberate towards a unanimously accepted proposal, possibly a lottery, and random dictatorship applies if none is found (the CORE proposal; compare Heitzig, Simmons and Constantino). The fallback is straightforward, so the strategic regress has a floor that nobody can move and nobody needs to predict. In the deliberation itself, where participants in effect bargain over lotteries with the fallback as the disagreement point, dominant strategies generally do not exist and Lemma 7 applies. This is case (i) of Theorem 10, accepted in exchange for the ex ante gains that the fallback alone forgoes. Such a procedure does not escape Gibbard's theorems. It confines the non-computable part to an open-ended process and gives that process a computable floor. By the observation on simultaneity, a deliberation conducted in visible turns has less of the obstruction than a simultaneous vote. This is consistent with the suggestion of Abramsky, Levin, Stepney and co-authors that time unfolds the paradoxes of self-reference into a process. *(Interpretation.)*

## 9. Relation to other work

*Arrow and Gödel.* Livson and Prokopenko's Self-Reference Systems relate Arrow's theorem to incompleteness through diagonalisation; their sequel shows that total cycles are forced; the paper with Pritam gives the orientability formulation. Sections 4–5 add the distinction between integer and parity obstructions and the location of the orientation reversal. Jiang, Lim, Yao and Ye's combinatorial Hodge decomposition and Saari's profile coordinates are the real-valued, established forms of the decomposition behind Section 4. Tanaka relates Arrow's theorem to Brouwer's; Baryshnikov and Chichilnisky give topological proofs and obstructions of a different kind (Chichilnisky's concerns the non-existence of a continuous symmetric aggregation, an obstruction depending on the number of voters and distinct from the one here).

*Contextuality.* Abramsky and Brandenburger's framework, the cohomological invariants of Abramsky, Mansfield, Barbosa and of Carù, the general theory of disagreement of Abramsky and Carù, and the logical Bell inequalities of Abramsky and Hardy are all formulated for finite outcome sets. Abramsky's categorical account of Arrow's theorem notes a common structure with contextuality without a reduction; Section 3 explains part of the distance. Zeng and Zahn apply the framework to individual choice. Kishida recasts contextuality as a semantics of logical paradoxes, which is the natural place to look for a common frame.

*Computability.* Besides Binmore, Anderlini and Nachbar–Zame on games, and Mihara on infinite electorates, there is a large literature on the complexity of computing manipulations (starting with Bartholdi, Tovey and Trick), which concerns the difficulty of a well-defined finite problem and is distinct from Theorem 8.

## 10. Status and open problems

| Statement | Status |
|---|---|
| Propositions 1–4 (value spaces, winding) | proved here, elementary |
| Proposition 5 and corollary (seam) | computed, three alternatives |
| Proposition 6 (burial) | proved, known |
| Observation in Section 6 (no anonymous, neutral deterministic rule at the Condorcet profile) | proved, elementary; general case Moulin 1983 |
| Symmetry breaks as competing fixed points, regress | interpretation |
| Lemma 7, Theorem 8 (dichotomy) | proved here from Gibbard 1973 and a standard diagonal argument; we have not found the combination stated elsewhere |
| Proposition 9 (rational diagonal), sequential example | computed, small cases |
| Theorem 10 (lotteries: regress or ex ante inefficiency) | proved here from Gibbard 1978 and Lemma 7 |
| Common Lawvere frame; static versus dynamic diagonal; reading of random fallback | interpretation |

**Open problems.**

1. *Rational diagonal in general.* Does every non-dictatorial simultaneous game form with at least three outcomes admit a rational diagonal? No counterexample exists among two-player forms with three strategies each.
2. *Randomised strategists.* What form of Theorem 8, if any, holds when strategists randomise? The existence of mixed equilibria suggests that the barrier becomes one of computing or coordinating on an equilibrium.
3. *More alternatives.* For n > 3, is orientation reversal on the surfaces of Livson, Pritam and Prokopenko again located exactly at the contradictory objects, and how do cycles on sub-triples enter?
4. *One statement for both loops.* Find a formulation, presumably of Lawvere type, of which the Liar (negation, parity) and the Condorcet cycle (shift, integers) are instances, with reduction mod 2 as a map between them.
5. *Aggregation without closure.* Characterise procedures that are not total functions from profiles to outcomes (open-ended deliberation with a fallback) in the terms used here: which obstructions do they avoid, and which do they relocate?

## References

- Abramsky, S. (2014). Arrow's theorem by arrow theory. arXiv:1401.4585.
- Abramsky, S. (2017). Contextuality: at the borders of paradox. In *Categories for the Working Philosopher*, Oxford University Press. arXiv:2011.04899.
- Abramsky, S. (2020). Classical logic, classical probability, and quantum mechanics. arXiv:2010.13326.
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Abramsky, S. and Carù, G. (2019). Non-locality, contextuality and valuation algebras: a general theory of disagreement. *Phil. Trans. R. Soc. A* 377, 20190036.
- Abramsky, S. and Hardy, L. (2012). Logical Bell inequalities. *Physical Review A* 85, 062114.
- Abramsky, S., Mansfield, S. and Barbosa, R. S. (2012). The cohomology of non-locality and contextuality. QPL 2011, EPTCS 95.
- Abramsky, S. et al. (2025). Open questions about time and self-reference in living systems. arXiv:2508.11423.
- Anderlini, L. (1990). Some notes on Church's thesis and the theory of games. *Theory and Decision* 29, 19–52.
- Arrow, K. J. (1963). *Social Choice and Individual Values*, 2nd ed. Yale University Press.
- Bartholdi, J., Tovey, C. and Trick, M. (1989). The computational difficulty of manipulating an election. *Social Choice and Welfare* 6, 227–241.
- Baryshnikov, Y. (1993). Unifying impossibility theorems: a topological approach. *Advances in Applied Mathematics* 14, 404–415.
- Binmore, K. (1987). Modeling rational players, part I. *Economics and Philosophy* 3, 179–214.
- Carù, G. (2017). On the cohomology of contextuality. QPL 2016, EPTCS 236.
- Chichilnisky, G. (1980). Social choice and the topology of spaces of preferences. *Advances in Mathematics* 37, 165–176.
- Fallenstein, B., Taylor, J. and Christiano, P. (2015). Reflective oracles: a foundation for classical game theory. arXiv:1508.04145.
- Gibbard, A. (1973). Manipulation of voting schemes: a general result. *Econometrica* 41, 587–601.
- Gibbard, A. (1977). Manipulation of schemes that mix voting with chance. *Econometrica* 45, 665–681.
- Gibbard, A. (1978). Straightforwardness of game forms with lotteries as outcomes. *Econometrica* 46, 595–614.
- Heitzig, J., Simmons, F. W. and Constantino, S. M. (2024). Fair group decisions via non-deterministic proportional consensus. *Social Choice and Welfare*.
- Jiang, X., Lim, L.-H., Yao, Y. and Ye, Y. (2011). Statistical ranking and combinatorial Hodge theory. *Mathematical Programming* 127, 203–244.
- Kishida, K. (2023). Gödel, Escher, Bell: contextual semantics of logical paradoxes. In *Samson Abramsky on Logic and Structure in Computer Science and Beyond*, Springer.
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- Livson, O. and Prokopenko, M. (2025). Comparing and contrasting Arrow's impossibility theorem and Gödel's incompleteness theorem. arXiv:2504.06589.
- Livson, O. and Prokopenko, M. (2025). Arrow's impossibility theorem as a generalisation of Condorcet's paradox. arXiv:2510.09076.
- Livson, O., Pritam, S. and Prokopenko, M. (2026). The non-orientable topology of Condorcet's paradox. arXiv:2601.07283.
- Meir, R., Polukarov, M., Rosenschein, J. S. and Jennings, N. R. (2017). Acyclic games and iterative voting. *Artificial Intelligence* 252, 100–122.
- Mihara, H. R. (1997). Arrow's theorem and Turing computability. *Economic Theory* 10, 257–276.
- Moulin, H. (1983). *The Strategy of Social Choice*. North-Holland.
- Nachbar, J. H. and Zame, W. R. (1996). Non-computable strategies and discounted repeated games. *Economic Theory* 8, 103–122.
- Prokopenko, M. et al. (2019). Self-referential basis of undecidable dynamics: from the Liar paradox and the halting problem to the edge of chaos. *Physics of Life Reviews* 31, 134–156.
- Saari, D. G. (2011). Geometry of voting. In *Handbook of Social Choice and Welfare* II, ch. 27, Elsevier.
- Satterthwaite, M. A. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory* 10, 187–217.
- Tanaka, Y. (2006). On the equivalence of the Arrow impossibility theorem and the Brouwer fixed point theorem. *Applied Mathematics and Computation* 172, 1303–1314.
- Zeng, W. and Zahn, P. (2015). Contextuality and the weak axiom in the theory of choice. arXiv:1512.02668.
