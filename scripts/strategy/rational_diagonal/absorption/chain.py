"""Along the run of valid suffixes ending at a valid game: is there one configuration (player,
order restricted to the outcomes present, kind) that works on every suffix of the run?"""
import pickle, collections, sys
from itertools import permutations
from sg import present, valid, works_direct
from collect import rev, rot

def restrict(P, keep): return tuple(x for x in P if x in keep)

def W_of(p, o, z):
    used = sorted(present(o, z)); W = set()
    for i in (0, 1):
        for P in permutations(used):
            for kind, Q in (("rev", rev(P)), ("rot", rot(P))):
                if works_direct(p, o, z, i, P, Q): W.add((i, P, kind))
    return W

if __name__ == "__main__":
    k = int(sys.argv[1]); N = int(sys.argv[2])
    data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
    st = collections.Counter(); ex = []
    for p, o, z, W in data:
        if len(p) != N: continue
        run = [(p, o, z)]
        for j in range(1, len(p)):
            g = (p[j:], o[j:], z)
            if not valid(*g): break
            run.append(g)
        st[("run length", len(run))] += 1
        # configs of the full game whose restrictions work on every suffix of the run
        alive = 0
        for c in W:
            i, P, kind = c
            ok = True
            for g in run[1:]:
                keep = present(g[1], g[2]); Pr = restrict(P, keep)
                Q = rev(Pr) if kind == "rev" else rot(Pr)
                if kind == "rot" and P[0] not in keep: ok = False; break
                if not works_direct(*g, i, Pr, Q): ok = False; break
            alive += ok
        st[("one config along the whole run", alive > 0)] += 1
        if alive == 0 and len(ex) < 4: ex.append((p, o, z, len(run)))
    print(dict(st)); print(*ex, sep="\n")
