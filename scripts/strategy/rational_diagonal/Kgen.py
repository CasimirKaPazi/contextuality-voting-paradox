import sys, collections
from itertools import product, permutations, combinations
from diag2 import rows_of, dictator
from recipes_core import works_PQ
m1, m2, k = map(int, sys.argv[1:4]); outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def forces(R, A): return any(set(r) <= A for r in R)
def tight(g):
    R1 = rows_of(g, m1, m2, 0); R2 = rows_of(g, m1, m2, 1)
    for r in range(k+1):
        for A in combinations(outs, r):
            A = set(A)
            if not forces(R1, A) and not forces(R2, set(outs) - A): return False
    return True
st = collections.Counter(); ex = None
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs) or not tight(g): continue
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)
        for x in outs:
            if forces(R, {x}): continue
            w = any(works_PQ(R, P, Q) for P in prefs if P[0] == x for Q in prefs if Q[-1] == x)
            st[w] += 1
            if not w and ex is None: ex = (g, i, x)
print(m1, m2, k, dict(st))
if ex:
    g, i, x = ex; print("i", i, "x", x, [" ".join(g[a*m2:(a+1)*m2]) for a in range(m1)])
