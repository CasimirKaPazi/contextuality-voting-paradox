"""Lottery-valued aggregation with independence of irrelevant alternatives.

A random rule assigns to each profile of strict rankings a lottery over strict
rankings. It satisfies probabilistic independence of irrelevant alternatives
if the probability that society puts x above y depends only on the voters'
comparisons of x and y (the column of the pair), and it is unanimous (Pareto)
if a unanimous column gives probability 0 or 1. Such a rule is a no-signalling
empirical model on the scenario of *Contextuality and Symmetry*, Section 1:
the probability attached to a variable (pair, column) is the same in every
profile (context) that contains it.

A mixture of dictatorships with weights w_i gives the pair the probability
sum_i w_i * column_i: power is additive. A model whose marginals are not of
this form is contextual, since a non-contextual model is a mixture of
deterministic solutions, and by Arrow's theorem these are the dictatorships.

Part 1 (linear programming). For m alternatives and N voters, maximise and
minimise x[pair][column] - sum_i column_i * x[first pair][e_i] over all rules.
The feasible marginals at a profile are those of the linear ordering polytope;
for m <= 5 it is given by the bounds and the triangle inequalities
0 <= x_ij + x_jk - x_ik <= 1, which are used here. Deviation 0 means that the
marginals of every rule are additive.

Part 2 (a contextual rule). The coin rule follows unanimity on a pair and
otherwise gives the pair probability 1/2, with a joint lottery chosen to keep
the outcome a ranking. The script checks, for each unanimity order that occurs,
whether a lottery over rankings with these marginals exists (exhaustively for
m <= 4, on random profiles for m = 5, 6).
"""
from itertools import product, permutations, combinations
import random
import numpy as np
from scipy.optimize import linprog


def rankings(m):
    return [{x: i for i, x in enumerate(p)} for p in permutations(range(m))]


def additivity_gap(m, N):
    pairs = list(combinations(range(m), 2))
    pi = {p: k for k, p in enumerate(pairs)}
    rb = [tuple(int(r[x] < r[y]) for x, y in pairs) for r in rankings(m)]
    cols = list(product((0, 1), repeat=N))
    var = {}
    for j in range(len(pairs)):
        for c in cols:
            if 0 < sum(c) < N:
                var[(j, c)] = len(var)
    nv = len(var)

    def lin(j, c):
        row = np.zeros(nv)
        if sum(c) == N:
            return row, 1.0
        if sum(c) > 0:
            row[var[(j, c)]] = 1
        return row, 0.0

    A, b, seen = [], [], set()
    for prof in product(rb, repeat=N):
        for i, j, k in combinations(range(m), 3):
            cs = [tuple(v[pi[p]] for v in prof) for p in ((i, j), (j, k), (i, k))]
            key = (i, j, k, *cs)
            if key in seen:
                continue
            seen.add(key)
            (r1, k1), (r2, k2), (r3, k3) = lin(pi[(i, j)], cs[0]), lin(pi[(j, k)], cs[1]), lin(pi[(i, k)], cs[2])
            row, const = r1 + r2 - r3, k1 + k2 - k3
            A.append(-row); b.append(const)
            A.append(row); b.append(1 - const)
    A, b = np.array(A), np.array(b)
    unit = [tuple(int(i == k) for i in range(N)) for k in range(N)]
    worst = 0.0
    for (j, c), idx in var.items():
        obj = np.zeros(nv)
        obj[idx] += 1
        for k in range(N):
            if c[k]:
                obj[var[(0, unit[k])]] -= 1
        for sign in (1, -1):
            res = linprog(sign * obj, A_ub=A, b_ub=b, bounds=[(0, 1)] * nv, method="highs")
            assert res.status == 0
            worst = max(worst, abs(res.fun))
    return nv, worst


def coin_rule_failures(m, N, samples=0, seed=1):
    pairs = list(combinations(range(m), 2))
    R = rankings(m)
    M = np.array([[int(r[x] < r[y]) for r in R] for x, y in pairs], float)

    def unanimity(prof):
        d = {}
        for x, y in pairs:
            s = [r[x] < r[y] for r in prof]
            if all(s):
                d[(x, y)] = 1
            elif not any(s):
                d[(x, y)] = 0
        return frozenset(d.items())

    rng = random.Random(seed)
    if samples:
        orders = {unanimity([rng.choice(R) for _ in range(N)]) for _ in range(samples)}
    else:
        orders = {unanimity(prof) for prof in product(R, repeat=N)}
    bad = 0
    for P in orders:
        d = dict(P)
        target = np.array([d.get(p, 0.5) for p in pairs])
        res = linprog(np.zeros(len(R)), A_eq=np.vstack([M, np.ones(len(R))]),
                      b_eq=np.append(target, 1), bounds=[(0, 1)] * len(R), method="highs")
        bad += res.status != 0
    return len(orders), bad


def main():
    print("Part 1: largest deviation of a rule's marginals from additive power")
    for m, N in [(3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (5, 2)]:
        nv, worst = additivity_gap(m, N)
        print(f"  m={m} N={N}: {nv} free probabilities, deviation {worst:.2f}")
    print("Part 2: coin rule (unanimity, otherwise 1/2 on each pair)")
    for m, N, s in [(3, 3, 0), (3, 4, 0), (4, 3, 0), (4, 4, 0), (5, 3, 20000), (6, 3, 20000), (6, 4, 20000)]:
        n, bad = coin_rule_failures(m, N, s)
        how = f"{s} random profiles" if s else "all profiles"
        print(f"  m={m} N={N} ({how}): {n} unanimity orders, no lottery at {bad}")


if __name__ == "__main__":
    main()
