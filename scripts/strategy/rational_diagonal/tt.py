"""Totally tight (TT) forms: every 2x2 subform has a constant line.
Test the rational diagonal and a strengthened invariant T(g) usable for induction
over adding constant lines:
 T(g): for every player k and outcome a there is a working (i, P, Q) with
       (i == k and top(P) != a) or (i != k and bottom(Q) == a)."""
import sys, collections
from itertools import product, permutations, combinations
from diag2 import rows_of, dictator
from recipes_core import works_PQ
m1, m2, k = map(int, sys.argv[1:4])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def TT(g):
    for r1, r2 in combinations(range(m1), 2):
        for c1, c2 in combinations(range(m2), 2):
            A, B, C, D = g[r1*m2+c1], g[r1*m2+c2], g[r2*m2+c1], g[r2*m2+c2]
            if not (A == B or C == D or A == C or B == D): return False
    return True
cnt = collections.Counter(); ex = {}
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs) or not TT(g): continue
    cnt["TT nondictatorial"] += 1
    W = []
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)
        for P in prefs:
            for Q in prefs:
                if works_PQ(R, P, Q): W.append((i, P, Q))
    if not W: cnt["no diagonal"] += 1; ex.setdefault("nodiag", g); continue
    Tok = all(any((i == kk and P[0] != a) or (i != kk and Q[-1] == a) for i, P, Q in W)
              for kk in (0, 1) for a in outs)
    if not Tok: cnt["T fails"] += 1; ex.setdefault("Tfail", g)
print(m1, m2, k, dict(cnt))
for key, g in ex.items(): print(key, [" ".join(g[a*m2:(a+1)*m2]) for a in range(m1)])
