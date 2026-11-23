"""Coverage check for core_chain_starts.py: the chain summary of every enumerated core, in both
orientations and under every renaming of outcomes, must lie inside some starting summary with the
same outcomes present.  Usage: python3 core_chain_cover.py k starts_k.txt cores_files..."""
import sys
from itertools import permutations
k = int(sys.argv[1])
P = tuple(range(k)); rP = P[::-1]; Ps = (0,) + rP[:-1]; rPs = (k - 1,) + P[:-1]
CFG = [(0, P, rP), (1, rP, P), (0, Ps, rP), (1, rPs, P)]
RK = [({u: n for n, u in enumerate(own)}, {u: n for n, u in enumerate(opp)}) for _, own, opp in CFG]
starts = {}
for line in open(sys.argv[2]):
    v = tuple(map(int, line.split())); starts.setdefault(v[0], []).append(v[1:])
def summ(R, cfg):
    pl = CFG[cfg][0]; rp, rq = RK[cfg]
    L = R if pl == 0 else [list(c) for c in zip(*R)]
    C = [list(c) for c in zip(*L)]; out = 0
    for r in L:
        y = min(r, key=lambda u: rq[u])
        M = min((v for c in range(len(C)) if r[c] == y for v in C[c]), key=lambda u: rp[u])
        out |= 1 << (y * k + M)
    return out
bad = tot = 0
for fn in sys.argv[3:]:
    for line in open(fn):
        M0 = [list(map(int, w)) for w in line.split()]
        for M1 in (M0, [list(c) for c in zip(*M0)]):
            for pi in permutations(range(k)):
                R = [[pi[x] for x in r] for r in M1]
                pr = sum(1 << u for u in {x for r in R for x in r})
                vec = [summ(R, c) for c in range(4)]; tot += 1
                if not any(all(x & ~y == 0 for x, y in zip(vec, s)) for s in starts.get(pr, [])):
                    bad += 1
                    if bad <= 3: print("not covered:", line.strip(), pi)
print(tot, "core summaries,", bad, "not covered")
