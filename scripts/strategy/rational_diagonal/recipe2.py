import sys
from diag2 import rows_of, dictator
from recipes_core import works_PQ
from itertools import product, permutations
m1, m2, k = map(int, sys.argv[1:4])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def tobottom(P): return P[1:] + P[:1]
cnt = {"rev": 0, "tobottom": 0, "either": 0}; tot = 0; ex = None
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs): continue
    tot += 1
    r = t = False
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)
        for P in prefs:
            r = r or works_PQ(R, P, P[::-1])
            t = t or works_PQ(R, P, tobottom(P))
    if not r: cnt["rev"] += 1
    if not t:
        cnt["tobottom"] += 1
        if ex is None: ex = g
    if not (r or t): cnt["either"] += 1
print(m1, m2, k, tot, cnt)
if ex: [print("  ", " ".join(ex[a*m2:(a+1)*m2])) for a in range(m1)]
