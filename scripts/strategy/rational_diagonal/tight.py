import sys
from diag2 import rows_of, dictator
from recipes_core import works_PQ
from itertools import product, permutations, combinations
m1, m2, k = map(int, sys.argv[1:4])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def forces(R, A): return any(set(r) <= A for r in R)
def tight(g):
    R1 = rows_of(g, m1, m2, 0); R2 = rows_of(g, m1, m2, 1)
    for r in range(0, k+1):
        for A in combinations(outs, r):
            A = set(A); B = set(outs) - A
            if not forces(R1, A) and not forces(R2, B): return False
    return True
def tobottom(P): return P[1:] + P[:1]
tot = ntight = cifail = revfail = 0; ex = []
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs): continue
    tot += 1
    if not tight(g): continue
    ntight += 1
    ci = any(works_PQ(rows_of(g, m1, m2, i), P, tobottom(P)) for i in (0, 1) for P in prefs)
    rv = any(works_PQ(rows_of(g, m1, m2, i), P, P[::-1]) for i in (0, 1) for P in prefs)
    if not ci:
        cifail += 1
    if not rv:
        revfail += 1
    if len(ex) < 4: ex.append(g)
print(m1, m2, k, "nondictatorial", tot, "tight", ntight, "CI fails among tight", cifail, "rev fails among tight", revfail)
for g in ex: print([" ".join(g[a*m2:(a+1)*m2]) for a in range(m1)])
