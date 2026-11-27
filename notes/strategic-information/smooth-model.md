# The Smooth Model across Methods

*Working note, part of [Strategic Information](README.md), first draft. The corners in which the pair notes prove their statements are separate assumptions for each method; only a smooth model of beliefs is one rationale for all of them, and the worst case of the order is defined there ([The Common Rationale](rationale.md), Section 1; README, Section 3). This note runs five methods in one such model on the same profiles, for three candidates: plurality, approval, Borda, instant runoff and BTR-plurality. Everything here is computed (`scripts/information/smooth_methods.py`; the kinds of ballots at rest in `additive_smooth.py`); conventions as in the README.*

## 1. The model

The model is that of *Instant Runoff and Plurality*, Section 6, after Eggers and Nowacki (2024). A poll for a method is a vector of expected shares of its ballots: three names, eight approval ballots, six rankings. Every voter believes the other ballots to have shares drawn from a Dirichlet distribution around the poll, with precision s, and casts the ballot with the highest expected utility when it is added with weight 0.002 (about 500 voters). Ties between ballots go to the most sincere one. The poll then moves 5 per cent towards the shares of these best replies, for 300 rounds. A run *comes to rest* if the winner of the poll is the same over the last 100 rounds and no share moved by more than 0.03 over them; its last poll is a *resting poll* and stands for a self-confirming poll.

Runs start from ten polls per method (seven for plurality): a sincere one, polls concentrated on each pair of front-runners, and three random ones. For approval, which has no sincere ballot, the sincere start approves the candidates above the voter's mean utility. The profiles are the same for all methods: 101 voters, 40 profiles under impartial culture with random utilities (36 of them with a Condorcet winner) and 40 in a two-dimensional spatial model (all with a Condorcet winner), each with s = 85, the baseline of Eggers and Nowacki, and with the vaguer s = 20. The polls of different methods are not matched: each method is taken at its own resting polls.

## 2. The worst case

For each profile, the worst case of a method is the worst winner over its resting polls (README, Section 3). The table counts the profiles at which that winner is not the one the target asks for, and in brackets the profiles with no resting poll.

**Majority target** (profiles with a Condorcet winner: 36 and 40):

| | impartial, s = 85 | impartial, s = 20 | spatial, s = 85 | spatial, s = 20 |
|---|---|---|---|---|
| Plurality | 36 (0) | 36 (0) | 22 (0) | 29 (0) |
| Approval | 5 (0) | 7 (2) | 1 (1) | 2 (1) |
| Borda | 3 (1) | 3 (1) | 2 (2) | 2 (0) |
| Instant runoff | 3 (1) | 2 (3) | 1 (0) | 2 (0) |
| BTR-plurality | 12 (0) | 2 (4) | 1 (0) | 1 (1) |

**Utilitarian target** (all 40 profiles; the winner asked for is the candidate with the largest total utility):

| | impartial, s = 85 | impartial, s = 20 | spatial, s = 85 | spatial, s = 20 |
|---|---|---|---|---|
| Plurality | 40 | 40 | 24 | 30 |
| Approval | 5 | 5 | 3 | 0 |
| Borda | 4 | 4 | 0 | 1 |
| Instant runoff | 6 | 5 | 2 | 3 |
| BTR-plurality | 17 | 6 | 4 | 1 |

With ten starting polls the resting polls found are not all there are, so the counts are lower bounds. With 40 profiles, differences of two or three profiles between methods are within what another sample would change.

## 3. Over the runs

The share of the runs at rest that elect the Condorcet winner and the utilitarian winner, and the mean total utility of the winner on the scale where the average candidate is 0 and the best is 1. The runs are not a sample of anything: the starting polls are chosen, and the methods have different ones. The figures describe where each method tends to come to rest.

| | Runs at rest | Condorcet winner elected (per cent) | Utilitarian winner elected (per cent) | Mean utility |
|---|---|---|---|---|
| Plurality | 269 to 280 of 280 | 74, 74, 86, 81 | 60, 61, 81, 79 | 0.56, 0.58, 0.88, 0.86 |
| Approval | 332 to 353 of 400 | 89, 83, 99, 94 | 91, 90, 93, 100 | 0.90, 0.93, 0.99, 1.00 |
| Borda | 249 to 338 of 400 | 91, 92, 93, 96 | 91, 92, 100, 96 | 0.95, 0.96, 1.00, 1.00 |
| Instant runoff | 341 to 374 of 400 | 94, 97, 100, 96 | 85, 92, 95, 92 | 0.86, 0.94, 1.00, 0.98 |
| BTR-plurality | 251 to 361 of 400 | 90, 96, 100, 100 | 75, 87, 91, 98 | 0.69, 0.84, 0.99, 1.00 |

(In each cell: impartial culture with s = 85 and s = 20, then spatial with s = 85 and s = 20.)

## 4. What changes from the corners

**Approval.** In the corner the only self-confirming poll has the Condorcet winner as leader (*Plurality and Approval*, Proposition 2). In the smooth model 5 to 7 of the 36 profiles with a Condorcet winner under impartial culture have a resting poll with another winner, and 1 or 2 of 40 in the spatial model. In the three cases looked at, the Condorcet winner's margins are narrow (one to five voters in 101) and the winner is the candidate with the largest total utility. The voters' ballots show why: at the resting polls about half of the ballots under impartial culture approve two candidates and half one (a third and two thirds in the spatial model), and which a voter does depends on intensities once more than one race carries weight. The direction is visible in the spatial model: with sharp beliefs approval's runs elect the Condorcet winner in 99 per cent and the utilitarian winner in 93 per cent, with vague beliefs in 94 and 100 per cent. Approval moves from the majority target towards the utilitarian one as the beliefs leave the corner. Without a Condorcet winner, where the corner has no self-confirming poll at all, approval comes to rest in 3 or 4 of the 4 profiles.

**Borda.** In the corner no poll confirms itself (*Borda and Score*, Proposition 3). In the smooth model 62 to 85 per cent of the runs come to rest, and the resting polls elect the Condorcet winner and the utilitarian winner about as often as those of any other method here. Between 17 and 43 per cent of the ballots at rest are not the sincere ranking. The corner's result was that the runner-up is always overtaken by a middle candidate; with three candidates and beliefs of some width the voters stop burying before that happens.

**Plurality.** Nearly every run comes to rest, and where it does depends on the start: at every profile under impartial culture, and at more than half of the spatial ones, some resting poll elects a candidate other than the one asked for, under each of the two targets. This is the corner's result (a self-confirming poll for every pair of which one beats the other) carried over unchanged.

**Instant runoff and BTR-plurality.** As in their notes. BTR-plurality under impartial culture with sharp beliefs is the one case in which a method other than plurality misses a target at many profiles (12 of 36 and 17 of 40), and only 251 of its 400 runs come to rest there.

## 5. Reading

Under one rationale, with three candidates:

- Plurality's worst case is worse than that of the other four under both targets, at every setting, by a wide margin. This is the one comparison of this note that is as clear in the smooth model as in the corners, where plurality's strategic count is also contained in approval's, instant runoff's and BTR-plurality's.
- The other four are not ordered. Their worst cases differ by a few profiles in 40, in changing directions. Over the runs, instant runoff and BTR-plurality tend to come to rest at the Condorcet winner more often than approval and Borda do, and approval and Borda at the utilitarian winner more often than those two, and the difference between the two groups is the difference between the two targets.

This is the picture the notes set out to make precise (README, Section 1): one method below the frontier, without any trade-off, and four at it, where the choice between them is a choice of target. That the corners gave sharper orders among the four (approval and instant runoff exactly on the Condorcet winner, Borda with no resting place) was a property of the corners. *(Interpretation; three candidates, forty profiles per setting.)*

## 6. Open questions

1. More profiles and more starting polls, to turn the counts of Section 2 into frequencies with a known error; and exact fixed points in place of resting polls.
2. Four and more candidates. The supplementary vote and BTR-IRV differ from instant runoff and BTR-plurality only there, and the dark horses of Borda's corner need a fourth candidate.
3. The dependence on the precision: as s grows, do approval's resting polls approach the corner's, with the Condorcet winner at every one?
4. Stage 2 for all five at their resting polls, in ranks and in bits, to set beside these worst cases.
5. The same table in the Ballot Front Finder Lab, where strategies are learned instead of computed from a model of beliefs.

## References

- Eggers, A. C. and Nowacki, T. (2024). Susceptibility to strategic voting: a comparison of plurality and instant-runoff elections. *Journal of Politics*. doi:10.1086/726943. Read in the version of 23 April 2023.
