"""The position rule on stopping games (Section 7).  A line (q, x) with x present, added at the
front of a valid stopping game so that the result is valid, should be absorbed by
  - a working configuration of q whose top among the present outcomes is not x, or
  - a working configuration of the other player whose top is present and whose opponent order
    has x among its two lowest present outcomes.
Reports the valid extensions, those with no selected configuration that survives, and selected
configurations that do not survive (the rule's soundness, which is proved by hand).
Usage: python3 positions.py k N   (needs data_k{k}_N{N}.pkl from collect.py)"""
import pickle, collections, sys
from sg import present, valid, works_direct
k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
def Qof(c): return c[1][::-1] if c[2] == 'rev' else c[1][1:] + c[1][:1]
def selected(c, q, x, pr):
    if c[0] == q: return [w for w in c[1] if w in pr][0] != x
    return c[1][0] in pr and x in [w for w in Qof(c) if w in pr][-2:]
st = collections.Counter(); ex = []
for p, o, z, W in data:
    pr = present(o, z)
    for q in (0, 1):
        for x in pr:
            p2, o2 = (q,) + p, (x,) + o
            if not valid(p2, o2, z): continue
            S = [c for c in W if selected(c, q, x, pr)]
            good = [c for c in S if works_direct(p2, o2, z, c[0], c[1], Qof(c))]
            st["valid extensions"] += 1; st["unsound selections"] += len(S) - len(good)
            if not good:
                st["missed"] += 1
                if len(ex) < 4: ex.append((p, o, z, q, x))
print(f"k={k}, up to {N} nodes:", dict(st), ex)
