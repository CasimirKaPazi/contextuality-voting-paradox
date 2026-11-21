"""Totally reducible ('semi-dictatorial') game forms: lines (rows/columns) with removal times and
outcomes; cell (b,c) = outcome of whichever of b, c is removed first.
Random sequences; test non-dictatorial forms with >= 3 outcomes for the rational diagonal."""
import sys, random
from itertools import permutations
from diag2 import works_fast, dictator
rnd = random.Random(int(sys.argv[1])); trials = int(sys.argv[2]); maxlen = int(sys.argv[3]); k = int(sys.argv[4])
outs = "abcdefg"[:k]
tested = fails = 0
for _ in range(trials):
    n = rnd.randint(4, maxlen)
    seq = [(rnd.randint(0, 1), rnd.choice(outs)) for _ in range(n)]
    rows = [(t, o) for t, (p, o) in enumerate(seq) if p == 0]
    cols = [(t, o) for t, (p, o) in enumerate(seq) if p == 1]
    if len(rows) < 2 or len(cols) < 2: continue
    g = tuple(ob if tb < tc else oc for (tb, ob) in rows for (tc, oc) in cols)
    used = sorted(set(g))
    if len(used) < 3 or dictator(g, len(rows), len(cols), used): continue
    tested += 1
    if works_fast(g, len(rows), len(cols), used, list(permutations(used))) is None:
        fails += 1; print("FAIL", seq, flush=True)
print("tested", tested, "fails", fails)
