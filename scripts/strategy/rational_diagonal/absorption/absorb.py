"""For a valid game G' and a front node (p, o) with o already present: is some working config
of G' absorbed, i.e. still working after the node is added?  Compared with validity of the
extended game."""
import pickle, collections, sys
from sg import forces, present, works_direct, valid
from collect import rev, rot

def ytypes(p, o, z, i, P, Q):
    """the y of every row of i"""
    rq = {x: r for r, x in enumerate(Q)}; N = len(o); Y = set()
    for s in [t for t in range(N) if p[t] == i] + [None]:
        S = N if s is None else s
        os_ = z if s is None else o[s]
        cand = [o[t] for t in range(S) if p[t] != i] + [os_]
        Y.add(min(cand, key=lambda x: rq[x]))
    return Y

def absorbs(g, c, q, x):
    p, o, z = g; i, P, kind = c
    Q = rev(P) if kind == "rev" else rot(P)
    if i == q: return P[0] != x
    rq = {v: r for r, v in enumerate(Q)}
    return all(rq[x] >= rq[y] for y in ytypes(p, o, z, i, P, Q))

if __name__ == "__main__":
    k = int(sys.argv[1]); N = int(sys.argv[2])
    data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
    st = collections.Counter()
    for p, o, z, W in data:
        g = (p, o, z); pr = present(o, z)
        for q in (0, 1):
            for x in pr:
                ext_valid = valid((q,) + p, (x,) + o, z)
                ab = any(absorbs(g, c, q, x) for c in W)
                st[(ext_valid, ab)] += 1
    print("(extension valid, absorbed):", dict(st))
    