"""Random totally reducible forms with many outcomes: does some (i, P) with Q = reverse(P)
or Q = P rotated (top moved to the bottom) work?"""
import random, sys
from itertools import permutations
from recipes_core import works_PQ
from diag2 import dictator
k = int(sys.argv[1]); trials = int(sys.argv[2]); random.seed(k)
prefs = list(permutations(range(k))); bad = done = 0
while done < trials:
    z = random.randrange(k); M = [[z]]
    for _ in range(random.randint(3, 14)):
        o = random.randrange(k)
        if random.random() < 0.5: M.insert(random.randint(0, 0), [o] * len(M[0]))
        else: [r.insert(0, o) for r in M]
    used = sorted({x for r in M for x in r}); g = tuple(x for r in M for x in r)
    if len(used) < 3 or dictator(g, len(M), len(M[0]), used): continue
    done += 1
    ok = any(works_PQ(R, P, Q) for R in (M, [list(c) for c in zip(*M)]) for P in prefs
             for Q in (P[::-1], P[1:] + P[:1]))
    if not ok: bad += 1; print("FAIL", M)
print(f"k={k}: {done} random valid forms, {bad} failures")
