import sys, collections
from diag2 import rows_of, dictator
from recipes_core import works_PQ
from itertools import product, permutations, combinations
m1, m2, k = map(int, sys.argv[1:4])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def forces(R, A): return any(set(r) <= A for r in R)
def tight(g):
    R1 = rows_of(g, m1, m2, 0); R2 = rows_of(g, m1, m2, 1)
    for r in range(k+1):
        for A in combinations(outs, r):
            A = set(A)
            if not forces(R1, A) and not forces(R2, set(outs) - A): return False
    return True
c = collections.Counter(); ex = {}
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs) or not tight(g): continue
    R1 = rows_of(g, m1, m2, 0); R2 = rows_of(g, m1, m2, 1)
    free = [x for x in outs if not forces(R1, {x}) and not forces(R2, {x})]
    if not free:
        c["no free outcome"] += 1; ex.setdefault("nofree", g); continue
    ok = False
    for x in free:
        for i in (0, 1):
            R = rows_of(g, m1, m2, i)
            for P in prefs:
                if P[0] != x: continue
                if works_PQ(R, P, P[::-1]) or works_PQ(R, P, P[1:] + P[:1]): ok = True
    c["free, recipe works" if ok else "free, recipe fails"] += 1
    if not ok: ex.setdefault("fail", g)
print(m1, m2, k, dict(c))
for kk, g in ex.items(): print(kk, [" ".join(g[a*m2:(a+1)*m2]) for a in range(m1)])
