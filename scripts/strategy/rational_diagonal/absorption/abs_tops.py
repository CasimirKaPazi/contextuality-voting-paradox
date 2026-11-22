"""Simplified absorption through top sets only:
(q, x) absorbed if q works with a top other than x, or the opponent works with kind rot and
top x.  Does this cover every valid extension?"""
import pickle, collections, sys
from sg import present, valid
k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
st = collections.Counter(); ex = []
for p, o, z, W in data:
    pr = present(o, z)
    T = {i: {c[1][0] for c in W if c[0] == i} for i in (0, 1)}
    Trot = {i: {c[1][0] for c in W if c[0] == i and c[2] == "rot"} for i in (0, 1)}
    for q in (0, 1):
        for x in pr:
            if not valid((q,) + p, (x,) + o, z): continue
            ok = bool(T[q] - {x}) or x in Trot[1 - q]
            st[ok] += 1
            if not ok and len(ex) < 8: ex.append((p, o, z, q, x, T, Trot))
print("valid extensions covered by the top rule:", dict(st))
for e in ex: print(e)
