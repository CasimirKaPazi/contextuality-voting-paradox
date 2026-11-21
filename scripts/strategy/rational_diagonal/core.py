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
def reduce(g):
    R = list(range(m1)); C = list(range(m2))
    changed = True
    while changed and R and C:
        changed = False
        for r in R:
            if len({g[r*m2+c] for c in C}) == 1: R.remove(r); changed = True; break
        if changed: continue
        for c in C:
            if len({g[r*m2+c] for r in R}) == 1: C.remove(c); changed = True; break
    return R, C
def cyc(t):  # the three rotations of a 3-tuple
    return [t, t[1:]+t[:1], t[2:]+t[:2]]
stat = collections.Counter()
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs) or g[0] != 'a' or dictator(g, m1, m2, outs) or not TT(g): continue
    R, C = reduce(g)
    if not R or not C: stat["totally reducible"] += 1; continue
    core = tuple(g[r*m2+c] for r in R for c in C)
    co = sorted(set(core))
    stat["core outcomes %d" % len(co)] += 1
    if len(co) != 3: continue
    # orientation that works on the core for player 0
    cr = rows_of(core, len(R), len(C), 0)
    good = [t for t in permutations(co) if any(works_PQ(cr, t, q) for q in permutations(co) if q[-1] == t[0])]
    # recipe on full form: P restricted to core outcomes is one of 'good' orientations, P's top = that top, Q bottom = P top
    ok = False
    for i in (0, 1):
        Rw = rows_of(g, m1, m2, i)
        for P in prefs:
            Pc = tuple(x for x in P if x in co)
            if Pc not in good or P[0] != Pc[0]: continue
            if any(works_PQ(Rw, P, Q) for Q in prefs if Q[-1] == P[0]): ok = True; break
        if ok: break
    stat["core recipe works" if ok else "core recipe FAILS"] += 1
print(m1, m2, k, dict(stat))
