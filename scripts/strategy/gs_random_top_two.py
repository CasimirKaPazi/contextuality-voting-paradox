"""Without unanimity the Gibbard–Satterthwaite scenario has contextual models already for one voter
(note *Gibbard–Satterthwaite as a Scenario*, Section 4).  The 'random top two' scheme gives the
voter's first and second choice with probability 1/2 each.  Checked for m = 3, 4, 5:
it is SD-strategy-proof, and it is not a mixture of the deterministic strategy-proof schemes of one
voter (the range rules, 'the best element of a fixed set S').  The second claim has a short proof
(note, Section 4): a set S missing two alternatives a, b would give a choice outside the top two on a
ballot starting with a, b, so only S with at least m - 1 elements carry weight; the second choice b
under top choice a is drawn only by S = all but a, so each of these m sets has weight 1/2, which sums
to m/2 > 1.  The script checks the first claim exactly and the second by a floating-point LP."""
import itertools, numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
for m in (3, 4, 5):
    R = list(itertools.permutations(range(m)))
    L = {r: {x: (F(1, 2) if x in r[:2] else F(0)) for x in range(m)} for r in R}
    sdsp = all(sum(L[r][x] for x in r[:t]) >= sum(L[s][x] for x in r[:t])
               for r in R for s in R for t in range(1, m))
    sets = [S for k in range(1, m + 1) for S in itertools.combinations(range(m), k)]
    rows = [[1 if next(y for y in r if y in S) == x else 0 for S in sets] for r in R for x in range(m)]
    rhs = [float(L[r][x]) for r in R for x in range(m)]
    res = linprog(np.zeros(len(sets)), A_eq=rows + [[1] * len(sets)], b_eq=rhs + [1], bounds=(0, None), method="highs")
    print(f"m={m}: SD-strategy-proof {sdsp}; mixture of range rules {res.status == 0}")
