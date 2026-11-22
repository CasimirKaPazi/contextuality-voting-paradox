"""Which subsets of the four chain tests can fail together?  T1 = i in the opposed game,
T2 = o in the opposed game, T3 = i in its twin game, T4 = o in its twin game."""
import random, itertools, collections, pickle
from sg import matrix
from k3_chain import works, T, forces, tt
def tests(R, k):
    out = []
    for Ri, Ro in ((R, T(R)), (T(R), R)):
        for a, c in itertools.permutations(range(k), 2):
            if forces(Ri, a) or forces(Ro, c): continue
            mids = [u for u in range(k) if u not in (a, c)]
            for mid in itertools.permutations(mids):
                P = (a,) + mid + (c,); rP = P[::-1]; P1 = (a,) + rP[:-1]; P2 = (c,) + P[:-1]
                out.append((works(Ri, P, rP), works(Ro, rP, P), works(Ri, P1, rP), works(Ro, P2, P)))
    return out
def valid(R, k):
    return len({v for r in R for v in r}) == k and not any(all(forces(M, u) for u in range(k)) for M in (R, T(R)))
random.seed(11)
for k in (3, 4, 5):
    cnt = collections.Counter(); g = 0
    while g < (1500 if k < 5 else 400):
        n = random.randint(k, k + 6)
        p = tuple(random.randrange(2) for _ in range(n)); o = tuple(random.randrange(k) for _ in range(n)); z = random.randrange(k)
        R = matrix(p, o, z, 0)
        if not valid(R, k): continue
        g += 1
        for t in tests(R, k): cnt["".join("1234"[n] for n in range(4) if not t[n])] += 1
    print(f"k={k}: sets of failing tests (stopping games):", sorted(cnt.items(), key=lambda x: (len(x[0]), x[0])))
