# Outline of a Follow-up to the CORE Paper

*Working note for thread G of the roadmap. The CORE paper (`papers/CORE_13.md`) stays a standalone introduction to the method. The working note* CORE and the Formal Results *(`notes/core-connection.md`) collects what has been found since, section by section, as it was found. This note proposes how that material would be arranged as a paper, records which parts are settled and which are not, and lists what is still missing before drafting. It is a plan, not a draft: no claim is made here that is not in the working note.*

## 1. What the follow-up would say

One sentence: CORE's fallback is the hidden variable of random dictatorship made physical, and everything CORE adds is negotiation over how much of that draw to reveal before acting.

The paper would develop this in three movements.
- **The draw.** The fallback is singled out from strategy and from aggregation. The draw is a martingale, from which the paper's fair-call results follow. What participants hold is the endowment plus what groups capture along the way.
- **Safety.** On a line with losses proportional to distance no one can be harmed, and the agreement is the mean of the ideals. Beyond the line, the agreements that harm no one with concave utilities are exactly the poolings of the call, and the mean is the least risky of them. Attitudes to risk decide who can agree with whom.
- **The protocol.** With a uniformly drawn proposer the call is a game solved backwards, one Raiffa step per group. Proposals can sit inside the call, worked out by nested proposer groups. Private attitudes cost nothing, private ideals bring the barrier back, and the remaining design choice is between protecting each member and protecting the group against obstruction.

## 2. Proposed structure

Section numbers in brackets refer to *CORE and the Formal Results*.

1. **Introduction.** CORE in brief, and the three movements above.
2. **The fallback** [2]. Random ballot from strategy-proofness (Gibbard, Hylland) and from full independence with unanimity and anonymity (*Four Levels*, Theorems 5 and 5′). The negative result: consistency and participation for joint draws do not single it out, since every scoring rule satisfies them.
3. **The draw** [3, 3a].
   - The martingale proposition, with the paper's fair-call results, the caller in the draw and sortition as corollaries.
   - The decomposition of holdings into the endowment plus the weighted surpluses of the groups. Every shortfall comes from groups formed without a participant.
4. **What rational groups can do to others** [3b, 3c].
   - The rational floor as a linear program between the paper's floor and the endowment.
   - The theorem for one dimension with losses proportional to distance.
   - Strictly concave loss: nothing to agree on.
   - Mixed curvature: the members at the edges decide.
5. **Safe agreements** [3d, 3e, 3f].
   - On a line with linear loss every efficient agreement has the mean of the ideals as its value.
   - Beyond the line: the mean rule, the reflection of the ideals through the mean, and safety by Jensen's inequality.
   - The safe class as the poolings of the call (Strassen), with the mean as its least risky member. The outcome as the expected ideal of the eventual dictator given partial information about the draw.
   - The five bargaining rules against this class (computed).
6. **The call as a game** [3g, 3i].
   - Random recognition and one Raiffa step per group.
   - Proposals inside the call, with nested proposer groups and the proposition on what the protocol keeps.
   - The value of an exclusion as the only entry for harm. The trade-off between a kept veto and robustness against a stubborn member, with the floor veto when floors can be checked.
7. **Information** [3h].
   - Cautious proposers and the mean when only attitudes are private.
   - With private ideals: the average voting rule and its equilibrium, and the theorem that on a line the random ballot is the only strategy-proof rule that harms no one.
8. **CORE and the impossibility theorems** [4]. The dichotomy of *Walls and Strategy*, the floor that can be computed from inside, and the limit of what the theorems say about open deliberation.
9. **Open questions** [6].

Appendix: the computations, with scripts and the settings of every table.

## 3. Scope decisions (proposed)

- **Kept out of the follow-up.** The reading of bargaining in terms of fixed points and cycles [5] and the contextuality framing of Section 2 of the working note stay in the repository's other notes. The follow-up would point to them in one paragraph. Its readers are likely to come from mechanism design and bargaining, for whom the obstruction language is a detour.
- **Interpretation kept short and marked.** The reading of the veil as the unrevealed draw, the advice to put averages on the table, and the separation of ideals from attitudes in deliberation appear as remarks, not as results.
- **The sequential variant.** The follow-up would present the paper's sequential variant as it is. The one-shot, veto-kept and floor-veto variants would be treated as variants, with the trade-off stated, without choosing among them. Choosing is a design decision for the CORE method, not a result.

## 4. Status of the material

**Settled (proved, or computed with an exact method):**
- the martingale and the decomposition of holdings (both also checked in Lean);
- the rational floor as a linear program;
- the theorem for one dimension (also checked in Lean) and the proposition on concave loss;
- the mean of the peaks on a line;
- the mean rule beyond the line (also checked in Lean);
- safe agreements as poolings;
- the call game with complete information;
- cautious proposers with private attitudes;
- the line theorem with private ideals, from the characterisation of Ehlers, Peters and Storcken by fixed probabilistic ballots (Theorem 4.1 and Proposition 5.2 of their paper, checked against the original), with exact grid computations as an independent check;
- the properties of proposals inside the call, and the veto-kept induction (the induction also checked in Lean).

**Settled with a caveat:**
- *The criterion of mixed curvature* [3c] is proved for two and three members and for the construction. Beyond that it is computed.

**Computed only, on small instances (three to eight participants, few instances at the larger sizes):**
- every comparison of rules and variants: how often outsiders are harmed, the gains, and the cost of a stubborn member;
- for six to eight participants [3i, larger groups]: no harm in the line and plane families at any size; with unstructured utilities the share harmed under sequential exclusion grows to about a third; the kept and floor vetoes match the sequential gains in the spatial families, while with unstructured utilities they fell behind at six and seven participants.

Beyond eight participants, nothing has been computed, and larger groups are not pursued further: the comparisons are illustrations, not a basis for asymptotic claims.

**Open:**
- a closed form of the rational floor beyond the line;
- the call game with private ideals;
- how deliberation can make stated positions credible;
- the sizes of proposer groups;
- a rule that protects excluded members and is robust against a stubborn member when floors cannot be checked.

## 5. Before drafting

1. *Done:* the characterisation of Ehlers, Peters and Storcken used in Section 3h is checked against their paper (Theorem 4.1, formula (12), Proposition 5.2), and the proof there is written in their terms.
2. *Done up to eight participants:* the comparisons of Sections 3d and 3i, with a single proposer, for six to eight participants. The harm in unstructured utilities grows with the group, and the spatial families stay free of harm. Not pursued beyond that.
3. *Done:* the martingale and the fair call, the decomposition of holdings, the veto-kept induction and the mean rule's safety are checked in Lean (`lean/CoreDraw.lean`), all from one induction on the size of the stage. So is the theorem for one dimension. Safe agreements as poolings are not formalised.
4. Settle the notation once. The working note uses e, h, c, s and G for endowment, holding, call, surplus and floor, D for the eventual dictator and R(S) for the outcome law from a group (Section 3b).
5. Choose the title and the relation to the first paper. The working title is *CORE II: The Draw, Safe Agreements and the Call as a Game*.
