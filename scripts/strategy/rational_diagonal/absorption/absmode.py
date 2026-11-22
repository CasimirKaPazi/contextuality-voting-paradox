"""For valid extensions (q, x), x present: absorbed by q's own configs, by the opponent's,
or by both?"""
import pickle, collections, sys
from sg import forces, present, valid
from absorb import absorbs
k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
st = collections.Counter(); ex = []
for p, o, z, W in data:
    g = (p, o, z); pr = present(o, z)
    for q in (0, 1):
        for x in pr:
            if not valid((q,) + p, (x,) + o, z): continue
            own = any(c[0] == q and absorbs(g, c, q, x) for c in W)
            opp = any(c[0] != q and absorbs(g, c, q, x) for c in W)
            st[(own, opp)] += 1
            if not own and len(ex) < 5: ex.append((p, o, z, q, x))
print("(absorbed by own configs, by opponent's):", dict(st))
for e in ex: print(e)
