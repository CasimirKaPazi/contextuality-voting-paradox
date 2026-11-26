# Instant Runoff and Plurality under a Common Rationale

*Working note, part of [Strategic Information](README.md), first draft. It compares instant runoff (IRV) with plurality for three candidates under the rationale of [The Common Rationale](rationale.md), extended to the pivot events of a ranked method. Conventions as in the README. The checks are in `scripts/information/irv_three.py` (the corner), `irv_smooth.py` (the smooth model) and `irv_bits.py` (stage 2 in bits).*

## 1. Polls and pivot events for instant runoff

Under instant runoff each voter ranks the candidates; the candidate with the fewest first preferences is eliminated, its ballots pass to their next choice, and with three candidates the remaining two meet in a final decided by majority. A ballot can matter in two kinds of event (Eggers and Nowacki 2024, cited, who list three *second-round* and nine *first-round* pivot events for three candidates): a tie in the final, where the ballot counts for whichever finalist it ranks higher, and a tie for elimination in the first round, where only its first preference counts.

The common rationale needs a poll that says which events are likely. For instant runoff a poll names the candidate e expected to be eliminated, the two finalists L (expected winner) and R, the finalist r who is closer to e in first preferences (the other finalist is o), and W, the winner of the final between o and e that would follow if r were eliminated instead. Two events are weighed:

- **F**, the final between L and R is tied;
- **E**, r and e are tied for elimination. A first preference for r keeps r in, and L wins; a first preference for e keeps e in, and W wins; a first preference for o changes nothing.

As with (T), the *corner* is the case in which one event is infinitely more likely than the other and decides first (*F before E*, or *E before F*); between the corners the two are weighed with a finite ratio. Remaining ties between ballots are broken towards the voter's sincere ranking, standing for the less likely events. This is an assumption made here; it plays the part of (T) and is not derived from a model of uncertainty. *F before E* is the analogue of (T): the race between the two front-runners is the closest one. The term *pushover* below is Eggers and Nowacki's: a first preference for a weak candidate given to make that candidate the opponent in the final.

## 2. Stage 1

Plurality embeds in instant runoff: a vote for x is written as any ranking with x first, and the plurality count is the count of first preferences ([README](README.md), Section 2). The converse fails, since a plurality ballot cannot say anything about the final.

## 3. Best replies and what the ballots carry

**Proposition 1 (best replies, F before E).** Under F before E, a best reply ranks the preferred of L and R above the other. Among such ballots, the first preference goes to r if the voter prefers L to W, to e if the voter prefers W to L, and to o if that is allowed and E is not decisive for the voter (in particular when W = L).

*Proof.* At F a ballot counts for whichever finalist it ranks higher, so the first event fixes the order of L and R. At E the value of a first preference for r is half of u_L − u_W, for e half of u_W − u_L, for o zero; the best allowed first preference follows. ∎

**Proposition 2 (stage 2, F before E).** For every poll, the final count of the strategic IRV ballots between L and R is N(L > R) against N(R > L). So the strategic plurality count at the poll (L, R), which is the same pair of numbers (*Plurality and Approval*, Proposition 1), is a function of the strategic IRV count: plurality uses no more strategic information than instant runoff. *(Proved, from Proposition 1; the poll (L, e, R, r, W) of instant runoff is matched with the plurality poll (L, R).)*

The strategic IRV count carries more: its first preferences show who gives up their favourite for r or for e. With E before F the order of L and R is no longer sincere on every ballot: of the best replies computed, 12.5 per cent rank the finalists against the voter's preference, and 3.5 to 3.7 per cent with equal weights (*computed*). Proposition 2 then fails as stated.

## 4. Self-confirming polls

A poll is self-confirming if the strategic ballots reproduce it: e strictly last and r strictly below o in first preferences, L beating R in the final, and W the winner of o against e.

**Proposition 3.** With three candidates and F before E, the winner L of every self-confirming poll is the Condorcet winner. In particular there is no self-confirming poll without a Condorcet winner.

*Proof.* L beats R, since the final count is sincere (Proposition 2). Suppose e beats L. If W = e, every voter who prefers e to L puts e first: whatever the order of L and R, a ballot with e first is allowed, and it gains half of u_e − u_L over r first and is better than o first, which gains nothing. So e has more than half of the first preferences and is not last. If W = o and r = L, every voter who prefers R to L puts e first (gaining half of u_R − u_L, where R first gains nothing and L first may not stand above R), and every other voter puts L first; R gets no first preference and cannot stand above L. If W = o = L, then r = R and E is not decisive for anybody, so every ballot is sincere; then W, the winner of L against e, is e, a contradiction. So L beats e as well. ∎

Plurality's winners include every candidate that beats another (*Plurality and Approval*, Proposition 2), so the winners of self-confirming IRV polls are among plurality's, and with an odd number of voters the inclusion is strict whenever there is a Condorcet winner, since one of the other two candidates beats the other. On random profiles (101 voters, 400 profiles per model), self-confirming IRV polls elected the Condorcet winner in every case with F before E and with E before F, and in all but one spatial profile with equal weights; there were none without a Condorcet winner (*computed*).

**Existence.** Unlike approval, instant runoff often has no self-confirming poll even when a Condorcet winner exists: in 120 of 359 such profiles under impartial culture and 60 of 398 in the spatial model, with F before E (63 in the spatial model with the other weights). The failure is a pushover that undoes itself. Take a profile with Condorcet winner L, a poll with r = L and W = R: the supporters of R see that a first preference for e makes R the winner if L is eliminated, and since a first preference for R itself does nothing at E, they all move it to e. R then has no first preferences and is the one eliminated, which contradicts the poll. In the corner a first preference for o has no value at all, because the event in which o's own elimination is at stake has been neglected; as soon as o's support falls, that event is no longer negligible. So the corner, which suffices for approval, is too coarse for instant runoff: its equilibria involve close three-way races in the first round. *(Interpretation of computed cases.)*

## 5. The order for this pair

In the corner F before E, with three candidates: plurality uses no more strategic information than instant runoff (Proposition 2), and wherever instant runoff has a self-confirming poll it elects the Condorcet winner, which plurality need not (Proposition 3). For the majority target plurality lies below instant runoff, as it lies below approval. Where instant runoff has no self-confirming poll, its worst case has to be read from the dynamics of the polls, as for approval without a Condorcet winner ([README](README.md), Section 7, question 1). *(From Propositions 2 and 3.)*

Earlier work points to the limits of the corner. For the two-round majority runoff, Bouton and Gratton (2015) characterise large-election equilibria in which the Condorcet winner may not even reach the second round (cited), and Bouton (2013) finds equilibria of runoff elections in which the Condorcet winner gets no votes (cited from a working-paper version). Eggers and Nowacki (2024) compute best replies with Dirichlet beliefs over the vote shares and iterated polls, which converge under instant runoff to an interior fixed point (cited). Sections 6 and 7 test the conclusions in such a smooth model, where three-way races in the first round carry weight.

## 6. A smooth model

The corner keeps two events and drops the rest. In a smooth model every voter weighs all events through one belief about the other ballots, as in Eggers and Nowacki (2024): the poll is a vector v of expected ballot shares, the other ballots are believed to have shares drawn from a Dirichlet distribution centred near v with precision s, and a ballot is valued by the expected utility of the winner when it is added with a small weight (here 0.002, about 500 voters). Plurality is treated the same way with its three ballots. Polls move as in Eggers and Nowacki: the new poll is the old one moved by 5 per cent towards the shares of the best replies. A run counts as *settled* if the poll's winner stays the same over the last 100 of 300 rounds and no share moves by more than 0.03 over them; this approximates a self-confirming poll. Runs start from ten polls: the sincere ballots, polls concentrated on each pair of front-runners, and three random polls. *(Computed throughout, `scripts/information/irv_smooth.py`; 101 voters, 40 profiles per model, s = 85, the baseline of Eggers and Nowacki, and s = 20.)*

**Worst case.** With a Condorcet winner, some settled IRV run elects another candidate in 1 or 2 of 40 spatial profiles and in 2 or 3 of 36 under impartial culture. Under plurality this happens in 22 to 29 of 40 spatial profiles and in all 36 under impartial culture. The conclusion of Proposition 3 survives as a strong tendency, not as a law: the exceptions are the kind of equilibrium found by Bouton and Gratton for the majority runoff.

**Existence.** No IRV run settled in at most 3 of the 36 profiles with a Condorcet winner, against a third of them in the corner. The pushover of Section 4 no longer undoes every poll, since a falling first-preference count makes the event in which o is eliminated count again. Without a Condorcet winner (four profiles, all under impartial culture) IRV runs settled in every case, so the second half of Proposition 3 is an artefact of the corner.

**Stage 2.** At the settled IRV polls, between 1.2 and 2.0 per cent of the best replies rank the two finalists against the voter's preference, so the strategic IRV count no longer gives N(L > R) exactly, and the plurality count of the smooth model is not exactly (N(L > R), N(R > L), 0) either. Proposition 2 therefore holds only approximately here, and whether plurality's strategic count is a garbling of instant runoff's is not decided by these computations. A quantitative comparison, such as the mutual information between profile and strategic count ([README](README.md), Section 2), is the natural next measure.

*Reading.* Between the corner and the smooth model the picture is stable in its main line: instant runoff's settled outcomes are nearly always the Condorcet winner where plurality's often are not. What changes is that the exact statements of the corner become frequencies. *(Interpretation.)*

## 7. Stage 2 in bits

By the lemma of the [README](README.md), Section 2, Blackwell's order at a poll holds exactly when the plurality ballot is a function of the IRV ballot, voter by voter, and the conditional entropy H(β_plur | β_IRV) measures how far it fails. The entropies are estimated from 4000 voters drawn from the culture of each profile, at polls of the smooth model of Section 6 reached from the sincere ballots (*computed*, `scripts/information/irv_bits.py`; 15 to 20 polls per model and precision). The capacities of stage 1 are log₂ 6 = 2.58 bits for a ranking and log₂ 3 = 1.58 bits for a name. The polls of the two methods have to be matched, and two matchings are used.

**Each method at its own settled poll.** The strategic IRV ballot carries 2.0 to 2.6 bits (close to its capacity under impartial culture, where sincere rankings already carry 2.58), the plurality ballot 0.9 to 1.0 bit, nearly the single comparison of the corner. H(β_plur | β_IRV) is 0.03 to 0.10 bits on average (at most 0.31 at one poll); it is zero at 14 of 20 spatial polls with s = 85 and at almost none under impartial culture. H(β_IRV | β_plur) is 1.0 to 1.6 bits. The two methods settle on the same winner at 12 to 19 of the polls.

**The plurality poll given by the first preferences of the IRV poll** (the matching induced by stage 1). Here the first round is often a close race of three, and the plurality ballot carries 1.1 to 1.6 bits; H(β_plur | β_IRV) rises to 0.08 to 0.33 bits. Most of it concerns intensities: the plurality ballot is not a function of the ranking (H(β_plur | ranking) is 0.09 to 0.34 bits), and given both the IRV ballot and the ranking 0.07 to 0.27 bits remain. A voter deserting a favourite in a three-way race weighs how much better the favourite is, and that decision is information about intensities that a ballot close to the ranking does not record.

*Reading.* Away from the corner neither strategic ballot is a function of the other, so the pair is not ordered by Blackwell's order in the strict sense of the [README](README.md), Section 3. In bits the asymmetry is large: instant runoff's ballot carries one to one and a half bits that plurality's lacks, plurality's carries a few hundredths to a third of a bit that instant runoff's lacks, mostly about intensities. Together with the worst case of Section 6, instant runoff is ahead of plurality on both steps of the comparison, but by a margin rather than by dominance. *(Interpretation.)*

## 8. Open questions

1. The smooth model of Section 6 with exact fixed points instead of settled runs, more profiles and starting polls, and a binomial model of mistakes as in Laslier: what do the exceptions to Proposition 3 look like, and how does their frequency depend on the precision?
2. More than three candidates: the events multiply with the order of eliminations. Is there a corner in which the strategic IRV count still contains the final count of the two front-runners?
3. Approval against instant runoff: both elect the Condorcet winner at every self-confirming poll in their corners, and their strategic counts carry different information (the leader's row for approval, the final pair and the shifts of first preferences for instant runoff). Are they comparable in Blackwell's order?
4. The order of the README, Section 3, is strict; Section 7 shows a pair that it leaves unordered by a small margin. Should the order allow a tolerance in bits, and how would that combine with the worst case?

## References

- Bouton, L. (2013). A theory of strategic voting in runoff elections. *American Economic Review* 103(4), 1248–1288.
- Bouton, L. and Gratton, G. (2015). Majority runoff elections: strategic voting and Duverger's hypothesis. *Theoretical Economics* 10, 283–314.
- Eggers, A. C. and Nowacki, T. (2024). Susceptibility to strategic voting: a comparison of plurality and instant-runoff elections. *Journal of Politics*. doi:10.1086/726943. Read in the version of 23 April 2023 (https://tobiasnowacki.com/files/strategicvoting.pdf).
