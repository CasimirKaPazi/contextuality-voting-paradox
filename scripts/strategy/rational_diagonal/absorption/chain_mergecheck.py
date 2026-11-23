"""Merging lemma: a safe line stays safe when two outcomes that are adjacent in all four orders
(two adjacent middle outcomes of P) and different from its critical outcome are merged.  For every
failing test, one safe line is taken; every middle pair avoiding its critical outcome is merged and
the test is checked again on the merged form (which must still fail)."""
import random, itertools, collections
from sg import matrix
from k3_chain import works, T, forces, tt
from chain_pairs import valid, safe_lines
random.seed(37); st = collections.Counter()
def crit(line, Po):
    ro = {u: n for n, u in enumerate(Po)}; return min(line, key=lambda u: ro[u])
for k in (4, 5, 6):
    g = 0
    while g < (600 if k < 6 else 150):
        nn = random.randint(k, k + 6)
        p = tuple(random.randrange(2) for _ in range(nn)); o = tuple(random.randrange(k) for _ in range(nn)); z = random.randrange(k)
        R = matrix(p, o, z, 0)
        if not valid(R, k): continue
        g += 1
        for Ri, Ro in ((R, T(R)), (T(R), R)):
            for a, c in itertools.permutations(range(k), 2):
                if forces(Ri, a) or forces(Ro, c): continue
                for mid in itertools.permutations([u for u in range(k) if u not in (a, c)]):
                    P = (a,) + mid + (c,); rP = P[::-1]; Ps = (a,) + rP[:-1]; rPs = (c,) + P[:-1]
                    for (M, Px, Po) in ((Ri, P, rP), (Ro, rP, P), (Ri, Ps, rP), (Ro, rPs, P)):
                        S = safe_lines(M, Px, Po)
                        if not S: continue
                        y = crit(S[0], Po)
                        for q in range(1, k - 2):
                            x1, x2 = P[q], P[q + 1]
                            if y in (x1, x2): continue
                            f = lambda A: [[x1 if u == x2 else u for u in r] for r in A]
                            Pxm = tuple(u for u in Px if u != x2); Pom = tuple(u for u in Po if u != x2)
                            still = not works(f(M), Pxm, Pom)
                            st[(k, "test still fails after merging", still)] += 1
print(dict(st))
