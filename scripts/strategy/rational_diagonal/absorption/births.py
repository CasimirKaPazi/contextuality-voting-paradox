"""Valid G and valid G' = (q, x)·G with x present: configs working in G' but not in G?"""
import pickle, collections, sys
from sg import present, valid
from chain import W_of
k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
st = collections.Counter()
for p, o, z, W in data:
    if len(p) >= N: continue
    for q in (0, 1):
        for x in present(o, z):
            g2 = ((q,) + p, (x,) + o, z)
            if not valid(*g2): continue
            W2 = W_of(*g2)
            born = W2 - W
            st["extensions"] += 1
            st["with births"] += bool(born)
            st["only births (no survivor)"] += bool(W2) and not (W2 & W)
print(dict(st))
