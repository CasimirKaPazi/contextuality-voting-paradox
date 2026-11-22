"""All valid stopping games with N nodes and k outcomes, first node owned by player 0,
outcomes renamed in order of first appearance from the front (node 0 has outcome 0).
For each game: the set of working (i, P, kind), kind in {rev, rot}."""
import sys, pickle
from itertools import permutations, product
from sg import works_direct, valid, present

def rot(P): return P[1:] + P[:1]          # top moved to the bottom
def rev(P): return P[::-1]

def canonical(o, z):
    m = {}
    for x in list(o) + [z]:
        if x not in m: m[x] = len(m)
    return tuple(m[x] for x in o), m[z]

def games(N, k):
    seen = set()
    for p in product((0, 1), repeat=N):
        if p[0] != 0: continue
        for oz in product(range(k), repeat=N + 1):
            o, z = canonical(oz[:N], oz[N])
            if (p, o, z) in seen: continue
            seen.add((p, o, z))
            if valid(p, o, z): yield p, o, z

def working(p, o, z):
    used = sorted(present(o, z)); W = set()
    for i in (0, 1):
        for P in permutations(used):
            for kind, Q in (("rev", rev(P)), ("rot", rot(P))):
                if works_direct(p, o, z, i, P, Q): W.add((i, P, kind))
    return W

if __name__ == "__main__":
    k = int(sys.argv[1]); Nmax = int(sys.argv[2]); data = []
    for N in range(1, Nmax + 1):
        for p, o, z in games(N, k):
            data.append((p, o, z, working(p, o, z)))
    print(len(data), "games; without a working pair:", sum(1 for d in data if not d[3]))
    pickle.dump(data, open(f"data_k{k}_N{Nmax}.pkl", "wb"))
