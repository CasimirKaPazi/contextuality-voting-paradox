"""Intermediate scores as best replies: Warren Smith's examples (RVstrat.pdf, Section 3) and exact checks.

1. Smith's Section 3.1, exactly: the other voters' totals are (1, 1.1, 1) or (0, 1.1, 1.2) with equal
   probability, utilities (10, 5, 0), scores in [0, 1], highest total wins.  The best ballot is (1, s, 0)
   with s strictly between 0.1 and 0.9 (B must pass C in the second state and stay below A in the first).
2. Smith's Section 3.2, by Monte Carlo: one known voter (0, 0.798, 0.618), one uniformly random voter,
   utilities (1, 0.832, 0); the best score for B is near 0.58.
3. Exact best replies in Laslier's binomial model (each mark uncounted with probability 1/D) when the
   other voters use the whole scale 0..k (here k = 4): how often the unique best ballot has an
   intermediate score, by electorate size.
"""
import itertools, random
from fractions import Fraction as F
from ballot_mistakes import win_numerators

def smith_31():
    states = [(F(1), F(11, 10), F(1)), (F(0), F(11, 10), F(12, 10))]
    u = (10, 5, 0)
    def eu(b):
        tot = 0
        for st in states:
            t = [st[i] + b[i] for i in range(3)]
            top = max(t); w = [i for i in range(3) if t[i] == top]
            tot += F(sum(u[i] for i in w), len(w))
        return tot / len(states)
    grid = [F(i, 20) for i in range(21)]
    best = max(eu((F(1), s, F(0))) for s in grid)
    window = [s for s in grid if eu((F(1), s, F(0))) == best]
    ext = max(eu(b) for b in itertools.product((F(0), F(1)), repeat=3))
    print(f"Smith 3.1: best approval-style ballot {ext}, best ballot (1, s, 0) {best} "
          f"for s in [{window[0]}, {window[-1]}] (grid step 1/20)")

def smith_32(T=400000, seed=1):
    rng = random.Random(seed)
    v1, u = (0, 0.798, 0.618), (1, 0.832, 0)
    draws = [(rng.random(), rng.random(), rng.random()) for _ in range(T)]
    res = []
    for s in [i / 50 for i in range(51)]:
        tot = 0.0
        for d in draws:
            t = (v1[0] + d[0] + 1, v1[1] + d[1] + s, v1[2] + d[2])
            tot += u[max(range(3), key=lambda i: t[i])]
        res.append((tot / T, s))
    e, s = max(res)
    print(f"Smith 3.2: best score for B about {s:.2f} (expected utility {e:.4f}); "
          f"s = 0: {res[0][0]:.4f}, s = 1: {res[-1][0]:.4f}  ({T} draws)")

def tally_pmf(scores, D):
    pmf = [1]
    for v in scores:
        new = [0] * (len(pmf) + v)
        for i, p in enumerate(pmf):
            new[i] += p; new[i + v] += p * (D - 1)
        pmf = new
    return pmf

def own(pmf, s, D):
    if s == 0:
        return [p * D for p in pmf]
    out = [0] * (len(pmf) + s)
    for i, p in enumerate(pmf):
        out[i] += p; out[i + s] += p * (D - 1)
    return out

def best(others, u, k, D):
    m = len(u)
    base = [tally_pmf([b[x] for b in others], D) for x in range(m)]
    vals = []
    for b in itertools.product(range(k + 1), repeat=m):
        pm = [own(base[x], b[x], D) for x in range(m)]
        L = max(len(p) for p in pm); pm = [p + [0] * (L - len(p)) for p in pm]
        vals.append((sum(ux * wx for ux, wx in zip(u, win_numerators(pm))), b))
    top = max(v for v, _ in vals)
    return [b for v, b in vals if v == top]

def whole_scale(k=4, m=3, T=40, seed=5):
    rng = random.Random(seed)
    for D in (20, 200):
        for N in (10, 30, 90):
            inter = 0
            for _ in range(T):
                others = []
                for _ in range(N):
                    uo = [rng.gauss(0.55, 0.3), rng.gauss(0.5, 0.3), rng.gauss(0.4, 0.3)]
                    lo, hi = min(uo), max(uo)
                    others.append(tuple(round(k * (x - lo) / (hi - lo)) for x in uo))
                arg = best(others, rng.sample(range(1, 1000), m), k, D)
                inter += len(arg) == 1 and any(0 < x < k for x in arg[0])
            print(f"others on the whole scale 0..{k}, uncounted marks 1/{D}, N = {N}: "
                  f"unique best ballot with an intermediate score for {inter}/{T} voters")

if __name__ == "__main__":
    smith_31()
    smith_32()
    whole_scale()
