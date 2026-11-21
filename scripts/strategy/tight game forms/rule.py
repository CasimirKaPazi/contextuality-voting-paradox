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
stat = collections.Counter(); tot = 0
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs) or not tight(g): continue
    tot += 1
    # rule candidate: pick i and x with x not forcible by i and x forcible by opponent?? record which (P,Q) shapes work
    good = set()
    for i in (0, 1):
        R = rows_of(g, m1, m2, i); Ro = rows_of(g, m1, m2, 1 - i)
        for P in prefs:
            x = P[0]
            if forces(R, {x}): continue
            for Q in prefs:
                if Q[-1] != x: continue
                if works_PQ(R, P, Q):
                    # shape: is Q = reverse(P)? is Q = P with x to bottom?
                    shape = "rev" if Q == P[::-1] else ("ci" if Q == P[1:] + P[:1] else "other")
                    good.add((shape, forces(Ro, {x})))
    for s in good: stat[s] += 1
    stat[("any", None)] += bool(good)
print(tot, dict(stat))
