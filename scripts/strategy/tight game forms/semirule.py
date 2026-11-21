import sys, random, collections
from itertools import permutations
from diag2 import dictator, rows_of
from recipes_core import works_PQ
rnd = random.Random(5); outs = "abcd"; st = collections.Counter(); ex = []
for _ in range(6000):
    n = rnd.randint(4, 8)
    seq = [(rnd.randint(0, 1), rnd.choice(outs)) for _ in range(n)]
    rows = [(t, o) for t, (p, o) in enumerate(seq) if p == 0]
    cols = [(t, o) for t, (p, o) in enumerate(seq) if p == 1]
    if len(rows) < 2 or len(cols) < 2: continue
    m1, m2 = len(rows), len(cols)
    g = tuple(ob if tb < tc else oc for (tb, ob) in rows for (tc, oc) in cols)
    used = sorted(set(g))
    if len(used) < 3 or dictator(g, m1, m2, used): continue
    prefs = list(permutations(used))
    W = set()
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)
        for P in prefs:
            for Q in prefs:
                if works_PQ(R, P, Q): W.add((i, P[0], Q[-1]))
    last = seq[-1][0]
    st["works for owner of last line"] += any(i == last for i, _, _ in W)
    st["works for other player"] += any(i != last for i, _, _ in W)
    st["total"] += 1
    # does a working pair always have Q bottom = P top?
    st["exists with Qbottom=Ptop"] += any(a == b for _, a, b in W)
    if not any(i == last for i, _, _ in W) and len(ex) < 3: ex.append(seq)
print(dict(st)); print(ex)
