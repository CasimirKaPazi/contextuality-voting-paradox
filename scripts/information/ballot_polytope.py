"""The ballot polytope (*The Ballot Polytope*, Sections 2 to 5).

Every ballot has a count vector (what it adds to the method's count).  The ballot polytope of a method
is the convex hull of these vectors.  Where the value of a ballot is linear in its count vector (large
electorates), a best reply is a vertex of the polytope.

1. Ballots, distinct count vectors and vertices for a list of methods, three and four candidates.
   Totals are taken up to a number added to all of them.  A point is a vertex if it is not a convex
   combination of the other points (linear programme).
2. Central symmetry of the polytopes (the count vectors of a ballot and of some other ballot add up to
   the same vector, whatever the ballot).
3. Three candidates, smooth model (Dirichlet beliefs with precision 85 around the sincere shares, one
   ballot of weight 0.002, K samples): how many voters have a ballot with an equal rank as their
   unique best reply, for BTR-plurality when candidates ranked equal at the top share one first
   preference, when each gets a whole one, and for a rule that reads the margins only; and what
   these voters gain in expected utility, as a share of the difference between their best and worst
   strict ballots.  Where the ballots with equal ranks are not vertices, both are sampling noise and
   fall as K grows.
About one minute.
"""
import itertools
import numpy as np
from scipy.optimize import linprog


def weak_orders(m):
    """Rankings with equal ranks, as tuples of levels (0 = top), every level used."""
    out = []
    for levels in itertools.product(range(m), repeat=m):
        if set(levels) == set(range(max(levels) + 1)):
            out.append(levels)
    return out


def strict_orders(m):
    return [lv for lv in weak_orders(m) if len(set(lv)) == m]


def centred(v):
    v = np.asarray(v, float)
    return v - v.mean()


def margins(lv):
    m = len(lv)
    return [np.sign(lv[y] - lv[x]) for x in range(m) for y in range(x + 1, m)]


def firsts(lv, whole):
    top = [x for x in range(len(lv)) if lv[x] == 0]
    return [(1 if whole else 1 / len(top)) if x in top else 0 for x in range(len(lv))]


def fp(lv, whole):
    """First preferences up to a number added to all of them (a ballot that gives every candidate a
    first preference changes no order and counts as none)."""
    return list(centred(firsts(lv, whole)))


def borda_average(lv):
    m = len(lv)
    return centred([sum((lv[y] > lv[x]) + 0.5 * (lv[y] == lv[x]) for y in range(m) if y != x) for x in range(m)])


def borda_truncated(m):
    """Rank any number of candidates strictly; the ranked get m - 1, m - 2, ..., the others 0."""
    out = []
    for k in range(1, m + 1):
        for chosen in itertools.permutations(range(m), k):
            v = [0] * m
            for i, c in enumerate(chosen):
                v[c] = m - 1 - i
            out.append(centred(v))
    return out


def methods(m):
    W, S = weak_orders(m), strict_orders(m)
    unit = np.eye(m)
    cumulative = [centred(np.bincount(c, minlength=m)) for c in itertools.combinations_with_replacement(range(m), 3)]
    return [
        ("plurality", [centred(unit[x]) for x in range(m)]),
        ("cumulative voting, 3 points", cumulative),
        ("approval", [centred(b) for b in itertools.product((0, 1), repeat=m)]),
        ("score 0..2", [centred(b) for b in itertools.product((0, 1, 2), repeat=m)]),
        ("Borda, strict rankings", [borda_average(lv) for lv in S]),
        ("Borda, equal ranks averaged", [borda_average(lv) for lv in W]),
        ("Borda, truncated ballots", borda_truncated(m)),
        ("margins, strict rankings", [margins(lv) for lv in S]),
        ("margins, equal ranks", [margins(lv) for lv in W]),
        ("first preferences and margins, strict", [fp(lv, True) + margins(lv) for lv in S]),
        ("the same, equal tops share one first preference", [fp(lv, False) + margins(lv) for lv in W]),
        ("the same, equal tops get a whole one each", [fp(lv, True) + margins(lv) for lv in W]),
    ]


def vertices(points):
    P = np.unique(np.round(np.array(points, float), 9), axis=0)
    idx = []
    for i in range(len(P)):
        others = np.delete(P, i, axis=0)
        res = linprog(np.zeros(len(others)), A_eq=np.vstack([others.T, np.ones(len(others))]),
                      b_eq=np.append(P[i], 1), bounds=(0, None), method="highs")
        if res.status != 0:
            idx.append(i)
    return P, idx


def symmetric(P):
    c = P.mean(axis=0)
    rows = {tuple(np.round(p, 6)) for p in P}
    return all(tuple(np.round(2 * c - p, 6)) in rows for p in P)


def part1():
    print("1. and 2. ballots, distinct count vectors, vertices, central symmetry")
    for m in (3, 4):
        for name, pts in methods(m):
            P, idx = vertices(pts)
            print(f"   m = {m}  {name:48s} {len(pts):4d} ballots, {len(P):4d} count vectors, "
                  f"{len(idx):3d} vertices, centrally symmetric: {symmetric(P[idx])}")


# ---- part 3: the smooth model with equal ranks, three candidates

def btr_winner(S, FP, AB):
    f = S @ FP.T
    o = np.argsort(f, 1)
    b, mid, t = o[:, 0], o[:, 1], o[:, 2]
    pref = np.einsum('kb,xyb->kxy', S, AB)
    i = np.arange(len(S))
    s = np.where(pref[i, b, mid] > pref[i, mid, b], b, mid)
    return np.where(pref[i, s, t] > pref[i, t, s], s, t)


def margin_winner(S, FP, AB):
    """The Condorcet winner, or else the candidate with the smallest largest defeat."""
    pref = np.einsum('kb,xyb->kxy', S, AB)
    marg = pref - pref.transpose(0, 2, 1)
    worst = np.where(np.eye(3, dtype=bool)[None], np.inf, marg).min(axis=2)
    return np.argmax(worst, 1)


def part3(K, profiles=8, voters=200, s=85, delta=0.002):
    W = weak_orders(3)
    strict = [len(set(lv)) == 3 for lv in W]
    AB = np.zeros((3, 3, len(W)))
    for j, lv in enumerate(W):
        for x in range(3):
            for y in range(3):
                AB[x, y, j] = lv[x] < lv[y]
    rules = (("BTR-plurality, equal tops share one first preference", btr_winner, False),
             ("BTR-plurality, equal tops get a whole one each", btr_winner, True),
             ("margins only (Condorcet winner, else smallest largest defeat)", margin_winner, False))
    for name, win, whole in rules:
        FP = np.array([firsts(lv, whole) for lv in W]).T
        rng = np.random.default_rng(3)
        weak_best = total = 0
        gain = stake = 0.0
        for _ in range(profiles):
            U = rng.random((voters, 3))
            v = np.zeros(len(W))
            for u in U:
                o = np.argsort(-u)
                lv = [0, 0, 0]
                for pos, c in enumerate(o):
                    lv[c] = pos
                v[W.index(tuple(lv))] += 1 / voters
            S = rng.dirichlet(s * v + 0.5, size=K)
            P = np.zeros((len(W), 3))
            for b in range(len(W)):
                T = S.copy()
                T[:, b] += delta
                P[b] = np.bincount(win(T, FP, AB), minlength=3) / K
            EU = U @ P.T
            best_strict = EU[:, strict].max(1)
            best_weak = EU[:, [not x for x in strict]].max(1)
            weak_best += int((best_weak > best_strict + 1e-12).sum())
            gain += np.maximum(best_weak - best_strict, 0).sum()
            stake += (best_strict - EU[:, strict].min(1)).sum()
            total += voters
        print(f"   K = {K:6d}  {name}: {weak_best}/{total} voters, "
              f"gain {100 * gain / stake:.2f} per cent of what is at stake between strict ballots")


if __name__ == "__main__":
    part1()
    print("3. three candidates, smooth model: voters whose unique best reply has an equal rank")
    for K in (10000, 40000, 160000):
        part3(K)
