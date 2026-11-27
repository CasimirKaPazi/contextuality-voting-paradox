"""Maximal lotteries as Pfaffians of the margins.

Checks Proposition 8 of notes/equality-of-voters-and-alternatives.md on random margin matrices:
  1. a unique maximal lottery is carried by an odd set E of candidates, and its probabilities are
     v_j / sum(v) with v_j = (-1)^(j-1) Pf(G without e_j); for a candidate y outside E the sum of
     v_j G[e_j, y] is the Pfaffian of E with y listed last, with the sign of sum(v);
  2. how often 1, 3, 5, 7 candidates carry the lottery;
  3. walls: along a line between two margin matrices, where the carrying set changes, the Pfaffian of
     an even set S vanishes; the carrying set on each side is S without one candidate or S with one
     more; and the maximal lotteries at the wall form the segment between the lotteries on the two
     sides.
Run: python3 maximal_lottery_pfaffians.py   (needs numpy and scipy; about twenty seconds)
"""
import itertools
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(12)


def pf(M):
    n = len(M)
    if n == 0:
        return 1.0
    if n % 2:
        return 0.0
    total = 0.0
    for j in range(1, n):
        rest = [k for k in range(1, n) if k != j]
        total += (-1) ** (j - 1) * M[0, j] * pf(M[np.ix_(rest, rest)])
    return total


def sub(G, S):
    S = list(S)
    return G[np.ix_(S, S)]


def lottery(G, objective=None, slack=0.0):
    """A maximal lottery (minimising the objective). With slack, lotteries that lose to no candidate
    by more than the slack: used at a wall, which is only located up to rounding."""
    m = len(G)
    objective = np.zeros(m) if objective is None else objective
    return linprog(objective, A_ub=-G.T, b_ub=np.full(m, slack), A_eq=np.ones((1, m)), b_eq=[1],
                   bounds=(0, 1), method="highs").x


def carrier(G):
    return tuple(np.flatnonzero(lottery(G) > 1e-9))


def random_margins(m):
    A = rng.normal(size=(m, m))
    return A - A.T


def pfaffian_vector(G, E):
    return np.array([(-1) ** j * pf(sub(G, [e for e in E if e != E[j]])) for j in range(len(E))])


# ---------- 1 and 2 ----------
for m in (3, 4, 5, 6, 7):
    sizes = {}
    for _ in range(300):
        G = random_margins(m)
        p = lottery(G)
        E = tuple(np.flatnonzero(p > 1e-9))
        sizes[len(E)] = sizes.get(len(E), 0) + 1
        assert len(E) % 2 == 1
        v = pfaffian_vector(G, E)
        assert np.all(v > 0) or np.all(v < 0)
        assert np.allclose(p[list(E)], v / v.sum(), atol=1e-7)
        for y in range(m):
            if y not in E:
                wall = pf(sub(G, list(E) + [y]))
                assert np.isclose(v @ G[list(E), y], wall) and wall * v.sum() > 0
    print(f"{m} candidates, 300 random margin matrices: the lottery is the vector of Pfaffians in every case;"
          f" candidates carrying it: {dict(sorted(sizes.items()))}")

# ---------- 3. walls ----------
def crossing(G0, G1):
    """A point on the line from G0 to G1 where the carrying set changes."""
    lo, hi, E0 = 0.0, 1.0, carrier(G0)
    for _ in range(50):
        mid = (lo + hi) / 2
        if carrier((1 - mid) * G0 + mid * G1) == E0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


for m in (4, 5, 6):
    kinds = {(-1, -1): 0, (-1, 1): 0, (1, 1): 0}
    done = 0
    while done < 60:
        G0, G1 = random_margins(m), random_margins(m)
        if carrier(G0) == carrier(G1):
            continue
        t = crossing(G0, G1)
        at = lambda s: (1 - s) * G0 + s * G1
        before, after = at(t - 1e-4), at(t + 1e-4)
        E, F = set(carrier(before)), set(carrier(after))
        if len(E) % 2 == 0 or len(F) % 2 == 0 or E == F:   # another wall within the step: skip
            continue
        if len(E) == len(F):          # S without one candidate on both sides, or with one more on both
            candidates = [S for S in (E | F, E & F) if abs(len(S) - len(E)) == 1]
        else:                         # S without a candidate on one side, with one more on the other
            small, large = sorted((E, F), key=len)
            candidates = [small | {y} for y in large - small] if small < large and len(large) == len(small) + 2 else []
        scale = np.abs(at(t)).max()
        walls = [S for S in candidates if abs(pf(sub(at(t), sorted(S)))) < 1e-4 * scale ** (len(S) // 2)]
        assert len(walls) == 1, (E, F)
        S = walls[0]
        kinds[tuple(sorted(len(X) - len(S) for X in (E, F)))] += 1
        # the maximal lotteries at the wall: the segment between the lotteries on the two sides
        p0, p1 = lottery(before), lottery(after)
        d = p1 - p0
        slack = 1e-5 * scale
        ends = lottery(at(t), d, slack), lottery(at(t), -d, slack)
        assert np.allclose(ends[0], p0, atol=2e-3) and np.allclose(ends[1], p1, atol=2e-3)
        others = np.array([lottery(at(t), rng.normal(size=m), slack) for _ in range(6)])
        assert np.linalg.matrix_rank(np.vstack([others - p0, d]), tol=5e-3) == 1
        done += 1
    print(f"{m} candidates, 60 crossings: the Pfaffian of one even set S vanishes at each. The carrying sets on the"
          f" two sides: S without a candidate on both {kinds[(-1, -1)]}, S without one and S with one more"
          f" {kinds[(-1, 1)]}, S with one more on both {kinds[(1, 1)]}; the maximal lotteries at the wall are the"
          " segment between the two sides")
print("all checks passed")
