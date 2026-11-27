# Instant Runoff and BTR-Plurality under a Common Rationale

*Working note, part of [Strategic Information](README.md), first draft. It compares a Condorcet method from the bottom-two-runoff family with instant runoff, for three candidates, under the rationale of [The Common Rationale](rationale.md) as extended to ranked methods in [Instant Runoff and Plurality](irv-plurality.md). Both methods take the same ranked ballots and differ only in the counting, so the pair tests stage 2 alone. Conventions as in the README. The checks are in `scripts/information/btr_three.py` (the corner), `btr_smooth.py` (the smooth model) and `btr_bits.py` (stage 2 in bits).*

## 1. The method

The bottom-two-runoff family goes back to BTR-IRV, proposed by Rob LeGrand in 2006: the two options with the fewest first preferences meet, the pairwise loser is eliminated, its ballots pass to their next preferences, and this repeats until one option remains (cited, Electowiki). A Smith-set member can never be eliminated in a runoff against a candidate outside the Smith set, so the method satisfies the Condorcet and Smith criteria (cited). BTR-score orders the candidates by their total scores and lets the two lowest meet in pairwise runoffs, the winner facing the next candidate up until one remains (Hiveism 2024).

Here the redistribution of ballots is read as part of the instant-runoff half of BTR-IRV, not of the bottom-two runoff. **BTR-plurality** therefore keeps the initial count: the candidates are ordered once by first preferences, and the two lowest still in the race meet in a pairwise runoff on the full rankings until one remains. With a fixed order this is a sequential pairwise agenda from the bottom up, in which the candidate with the most first preferences enters last; it is Smith-efficient for any initial order, by the argument above. With three candidates BTR-plurality and BTR-IRV coincide, since after the first runoff only two candidates are left. Ties are taken as for BTR-score in *Equality of Voters and Alternatives*, Section 7: a pairwise tie goes to the candidate higher in the order, and equal counts of first preferences are ordered by voters drawn at random, each by their own ranking. They play no part below. In the Ballot Front Finder Lab (https://github.com/CasimirKaPazi/Ballot-Front-Finder-Lab) BTR-plurality is defined by `ballots("rank") >> btr(firsts, margins)`; the other methods of these notes are among the lab's default methods.

**Stage 1.** Both methods take rankings, m! ballots. The count of BTR-plurality is the first preferences and the pairwise margins. With three candidates these determine the whole histogram of rankings, and instant runoff has the same count there ([README](README.md), Section 2), so at stage 1 the two methods do not differ for three candidates. Plurality embeds in both through the first preferences. Like instant runoff, BTR-plurality fails the Equality Criterion: without a Condorcet winner its outcome depends on the order by first preferences, which a ballot and its reverse can change (README, Section 6).

## 2. Polls and pivot events

A poll for BTR-plurality names the order by first preferences (top T, middle M, bottom B), the expected winner S of the first runoff between M and B (the other is o), the expected winner L of S against T, and Wo, the winner of o against T. Two events are weighed, as for instant runoff:

- **F**, the final runoff between S and T is tied: a ballot counts for whichever of S, T it ranks higher;
- **E′**, the first runoff between M and B is tied: a ballot ranking S above o makes the winner L, one ranking o above S makes it Wo.

The ties that would change the order by first preferences are neglected in the corner, as the ties that change the eliminated candidate beyond E are neglected for instant runoff. Remaining ties between ballots are broken towards the sincere ranking.

## 3. Best replies

**Proposition 1 (corner).** A best reply ranks the preferred of S and T above the other, ranks S above o exactly when the voter prefers L to Wo, and ranks o and T sincerely. *(Proved.)*

*Proof.* The first two follow from F and E′. For o and T: the two constraints fix S against T and S against o. If S stands above both or below both, o against T is free and the tie-break makes it sincere. If L = Wo, E′ decides nothing and the tie-break makes the whole ballot sincere. Otherwise S may stand between the two, as T > S > o (the voter prefers T to S and L to Wo) or o > S > T (S to T and Wo to L). Going through the three remaining polls (L, Wo) = (S, T), (S, o), (T, o): for (S, T) each of the two ballots requires both a preference and its reverse between S and T; for (S, o) a voter who preferred the candidate the ballot puts last to the one it puts first would have cyclic preferences; for (T, o) the ballot's order of o and T is the voter's own preference between them. ∎

The first preference is not chosen for its own sake in the corner; it follows from where S has to stand. Of all best replies computed, one in twelve has a first preference other than the voter's favourite (*computed*). The final pair is ranked sincerely on every ballot, as under instant runoff.

## 4. Self-confirming polls

A poll is self-confirming if the strategic ballots reproduce the order T > M > B by first preferences, S beating o, L winning S against T, and Wo winning o against T (all strictly).

**Proposition 2.** In the corner, the winner L of every self-confirming poll is the Condorcet winner. *(Proved.)*

*Proof.* Let c be the Condorcet winner. The final pair is ranked sincerely, so if c is S or T it wins the final and c = L. Otherwise c = o. By Proposition 1, o and T are ranked sincerely, so Wo = c. At E′ every voter who prefers c to L ranks o above S, and these are a majority, so o beats S, which contradicts the poll. ∎

On random profiles (101 voters, 300 per model) the computations agree: no self-confirming poll elects another candidate, and none exists without a Condorcet winner. As for instant runoff, the corner often has no self-confirming poll at all, in 88 of 269 profiles with a Condorcet winner under impartial culture and 34 of 298 in the spatial model, about as often as for instant runoff (a third and a seventh): the forced changes of first preferences move the order that the corner treats as fixed. The results do not depend on the relative weight of F and E′. *(Computed.)*

So in the corner the two methods agree in the worst case: both elect the Condorcet winner wherever they have a self-confirming poll.

## 5. The smooth model

In the smooth model of *Instant Runoff and Plurality*, Section 6 (Dirichlet beliefs over the ballot shares, all pivot events weighed, polls moved towards the best replies, ten starting polls, 101 voters, 40 profiles per model), the counts are (*computed*):

| | | IRV: another winner | IRV: no run comes to rest | BTR: another winner | BTR: no run comes to rest |
|---|---|---|---|---|---|
| impartial culture (36 with a Condorcet winner) | s = 85 | 3 | 1 | 12 | 0 |
| | s = 20 | 2 | 3 | 2 | 4 |
| spatial (40 with a Condorcet winner) | s = 85 | 1 | 0 | 1 | 0 |
| | s = 20 | 2 | 0 | 1 | 1 |

Without a Condorcet winner (four profiles, impartial culture) both come to rest in every case. In the spatial model the two methods are alike. Under impartial culture with sharp beliefs, BTR-plurality comes to rest on another candidate in a third of the profiles with a Condorcet winner, instant runoff in one twelfth.

A case shows how. In one profile the Condorcet winner C beats A with 50.5 per cent of the sincere ballots, and the three candidates have a third of the first preferences each. At a resting poll C's first preferences have fallen to 2 per cent: its supporters rank B first, which puts C at the bottom of the order, where it meets A in the first runoff, and on the strategic ballots A beats C with 58 per cent. A Condorcet method guarantees the Condorcet winner on the ballots it receives; with a narrow sincere margin, the strategic ballots of a shared poll need not contain one. *(Computed case; interpretation.)* Whether these resting polls are true equilibria or slow parts of the dynamics, and how they depend on the margin of the Condorcet winner, is open.

## 6. Stage 2 in bits

Both methods take the same ballots, so a poll (a vector of expected ballot shares) is the same object for both, and the ballots can be compared at one and the same poll. At the resting IRV poll, the resting BTR poll, and each method at its own poll (*computed*, `btr_bits.py`, 4000 voters, 10 to 20 polls per setting):

- in the spatial model with s = 85 neither ballot is a function of the other on average, but at more than half of the polls both are: H(BTR | IRV) and H(IRV | BTR) are 0.08 to 0.16 bits, zero at 11 to 14 of 17 to 20 polls;
- in the other settings each carries 0.26 to 0.51 bits that the other lacks, and the two are of similar size, except at the resting BTR polls under impartial culture with s = 85, where the BTR ballot carries 1.95 bits against 2.53 and H(IRV | BTR) = 0.85 to 0.92 bits against H(BTR | IRV) = 0.27 to 0.32.

Both ballots depend on intensities (H(ballot | ranking) of 0.03 to 0.43 bits). *(Computed.)*

## 7. The order for this pair

In the corner the two methods are alike in the worst case: every self-confirming poll elects the Condorcet winner (Proposition 2 here, Proposition 3 of *Instant Runoff and Plurality*). Their strategic ballots differ, BTR moving the comparison of the two candidates in the first runoff, instant runoff the first preferences. In the smooth model the pair is unordered at stage 2 by a roughly symmetric margin, and in the worst case instant runoff is ahead under impartial culture with sharp beliefs, the two alike otherwise. A Condorcet method does not lie above instant runoff under this rationale. *(From the propositions and computations; interpretation.)*

## 8. Open questions

1. The resting polls of Section 5 at which BTR-plurality loses the Condorcet winner: exact fixed points or slow dynamics, and their dependence on the Condorcet winner's margin and on the precision.
2. Four or more candidates, where BTR-plurality and BTR-IRV differ and the order by first preferences carries more of the outcome.
3. Other initial orders (by score, as in BTR-score, or by approval), which change what the first stage asks of the ballot.
4. BTR-plurality against plurality, the step that adds the runoffs to the same initial count.

## References

- Electowiki, *Bottom-Two-Runoff IRV*. https://electowiki.org/wiki/Bottom-Two-Runoff_IRV (revisions consulted through search; LeGrand 2006 as cited there).
- Hiveism (2024). Four levels of voting methods. Substack, 15 June 2024. https://hiveism.substack.com/p/four-levels-of-voting-methods
