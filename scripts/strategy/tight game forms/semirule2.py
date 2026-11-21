import sys, random, collections
from itertools import permutations
from diag2 import dictator, rows_of
from recipes_core import works_PQ
rnd = random.Random(7); st = collections.Counter(); ex = []
for _ in range(8000):
    k = rnd.choice([3, 4]); outs = "abcd"[:k]
    n = rnd.randint(4, 9)
    seq = [(rnd.randint(0, 1), rnd.choice(outs)) for _ in range(n)]
    rows = [(t, o) for t, (p, o) in enumerate(seq) if p == 0]
    cols = [(t, o) for t, (p, o) in enumerate(seq) if p == 1]
    if len(rows) < 2 or len(cols) < 2: continue
    m1, m2 = len(rows), len(cols)
    g = tuple(ob if tb < tc else oc for (tb, ob) in rows for (tc, oc) in cols)
    used = sorted(set(g))
    if len(used) < 3 or dictator(g, m1, m2, used): continue
    prefs = list(permutations(used))
    i = 1 - seq[-1][0]             # the player who does not own the last node
    R = rows_of(g, m1, m2, i)
    zs = any(works_PQ(R, P, P[::-1]) for P in prefs)
    anyQ = any(works_PQ(R, P, Q) for P in prefs for Q in prefs)
    st["total"] += 1; st["non-last owner, zero-sum works"] += zs; st["non-last owner, some Q works"] += anyQ
    if not anyQ and len(ex) < 3: ex.append(seq)
print(dict(st)); print(ex)
