"""Lottery-valued aggregation with independence of irrelevant alternatives.

A random rule assigns to each profile of strict rankings a lottery over strict
rankings. It satisfies probabilistic independence of irrelevant alternatives
if the probability that society puts x above y depends only on the voters'
comparisons of x and y (the column of the pair), and it is unanimous (Pareto)
if a unanimous column gives probability 0 or 1. On the scenario of
*Contextuality and Symmetry*, Section 1, such a rule is a weakly compatible
family: the probability attached to a variable (pair, column) is the same in
every profile (context) that contains it.

A mixture of dictatorships with weights w_i gives the pair the probability
sum_i w_i * column_i: power is additive. A non-contextual family is a mixture
of deterministic solutions, and by Arrow's theorem these are the
dictatorships.

Part 1 (linear programming). For m alternatives and N voters, maximise and
minimise x[pair][column] - sum_i column_i * x[first pair][e_i] over all rules.
The feasible marginals at a profile are those of the linear ordering polytope;
for m <= 5 it is given by the bounds and the triangle inequalities
0 <= x_ij + x_jk - x_ik <= 1, which are used here. Deviation 0 means that the
marginals of every rule are additive.

Part 2 (a non-additive rule). The coin rule follows unanimity on a pair and
otherwise gives the pair probability 1/2, with a joint lottery chosen to keep
the outcome a ranking. The script checks, for each unanimity order that occurs,
whether a lottery over rankings with these marginals exists (exhaustively for
m <= 4, on random profiles for m = 5, 6).

Part 4 (more alternatives). For four alternatives and two voters, no fully
compatible unanimous family puts mass on rankings that no voter holds; with two
voters this forces the mixture of dictatorships. Theorem 5 of Four Levels proves
the three-alternative case for any number of voters.

Part 3 (full compatibility). Probabilistic independence only asks that each
pair's probability depend on that pair's column (weak compatibility). An
empirical model in the sense of Abramsky and Brandenburger also requires two
profiles that share the columns of two pairs to induce the same joint lottery
on those two pairs. For three alternatives and N = 2, 3 the script checks by
linear programming (a) that every fully compatible unanimous family is a
mixture of dictatorships, lotteries included, and (b) for N = 2, 3, 4 whether
the coin rule admits a fully compatible choice of lotteries (it does only for
N = 2).
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


def _three_alt_setup(N):
    R = list(permutations("abc"))

    def bits(r):
        q = {x: i for i, x in enumerate(r)}
        return (int(q["a"] < q["b"]), int(q["b"] < q["c"]), int(q["c"] < q["a"]))

    T = [bits(r) for r in R]
    profs = sorted({tuple(tuple(v[j] for v in prof) for j in range(3))
                    for prof in product(T, repeat=N)})
    return T, profs


def _full_compat_system(N, T, profs, marg=None):
    nv = len(profs) * 6
    idx = lambda pi, t: pi * 6 + t

    def margrow(pi, j):
        row = np.zeros(nv)
        for t, tr in enumerate(T):
            if tr[j] == 1:
                row[idx(pi, t)] = 1
        return row

    A, b = [], []
    for pi, cols in enumerate(profs):
        row = np.zeros(nv); row[[idx(pi, t) for t in range(6)]] = 1
        A.append(row); b.append(1)
        for j in range(3):
            k = sum(cols[j])
            if marg is not None:
                A.append(margrow(pi, j)); b.append(marg(cols[j]))
            elif k in (0, N):
                A.append(margrow(pi, j)); b.append(1.0 if k == N else 0.0)
    for j in range(3):
        g = {}
        for pi, cols in enumerate(profs):
            g.setdefault(cols[j], []).append(pi)
        for ps in g.values():
            for pi in ps[1:]:
                A.append(margrow(ps[0], j) - margrow(pi, j)); b.append(0)
    for j, k in combinations(range(3), 2):
        g = {}
        for pi, cols in enumerate(profs):
            g.setdefault((cols[j], cols[k]), []).append(pi)
        for ps in g.values():
            for pi in ps[1:]:
                for bj, bk in product((0, 1), repeat=2):
                    row = np.zeros(nv)
                    for t, tr in enumerate(T):
                        if tr[j] == bj and tr[k] == bk:
                            row[idx(ps[0], t)] += 1; row[idx(pi, t)] -= 1
                    A.append(row); b.append(0)
    return np.array(A), np.array(b), nv, idx, margrow


def full_compatibility_gap(N):
    """Largest deviation of a fully compatible unanimous family from the mixture of
    dictatorships with the weights read off at the single-voter columns."""
    T, profs = _three_alt_setup(N)
    A, b, nv, idx, margrow = _full_compat_system(N, T, profs)
    first = {}
    for pi, cols in enumerate(profs):
        for j in range(3):
            first.setdefault((j, cols[j]), pi)
    unit = [tuple(int(i == k) for i in range(N)) for k in range(N)]
    w = [margrow(first[(0, unit[k])], 0) for k in range(N)]
    worst = 0.0
    for pi, cols in enumerate(profs):
        for t, tr in enumerate(T):
            obj = np.zeros(nv); obj[idx(pi, t)] = 1
            for k in range(N):
                if tuple(cols[j][k] for j in range(3)) == tr:
                    obj -= w[k]
            for sign in (1, -1):
                res = linprog(sign * obj, A_eq=A, b_eq=b, bounds=[(0, 1)] * nv, method="highs")
                worst = max(worst, abs(res.fun))
    return worst


def coin_fully_compatible(N):
    T, profs = _three_alt_setup(N)
    marg = lambda col: 0.0 if sum(col) == 0 else 1.0 if sum(col) == N else 0.5
    A, b, nv, _, _ = _full_compat_system(N, T, profs, marg)
    res = linprog(np.zeros(nv), A_eq=A, b_eq=b, bounds=[(0, 1)] * nv, method="highs")
    return res.status == 0


def full_compat_support(m, N):
    """Part 4. Largest total mass, summed over profiles, that a fully compatible unanimous
    family can put on rankings that no voter holds. Contexts are profiles of m alternatives;
    two profiles with the same columns on a set E of pairs must induce the same joint
    distribution on E. Zero means every model is supported on the voters' rankings, which
    for two voters forces the mixture of dictatorships."""
    import scipy.sparse as sp
    pairs = list(combinations(range(m), 2))
    R = list(permutations(range(m)))
    T = []
    for r in R:
        q = {x: i for i, x in enumerate(r)}
        T.append(tuple(int(q[a] < q[b]) for a, b in pairs))
    nT = len(T)
    profs = list(product(range(nT), repeat=N))
    cols = [tuple(tuple(T[v][e] for v in pr) for e in range(len(pairs))) for pr in profs]
    rows, cs, vals, b = [], [], [], []

    def add(entries, rhs):
        r = len(b)
        for c, v in entries:
            rows.append(r); cs.append(c); vals.append(v)
        b.append(rhs)

    for pi in range(len(profs)):
        add([(pi * nT + t, 1) for t in range(nT)], 1)
        for e in range(len(pairs)):
            k = sum(cols[pi][e])
            if k in (0, N):
                want = 1 if k == N else 0
                add([(pi * nT + t, 1) for t in range(nT) if T[t][e] != want], 0)
    for size in range(1, len(pairs)):
        for E in combinations(range(len(pairs)), size):
            g = {}
            for pi in range(len(profs)):
                g.setdefault(tuple(cols[pi][e] for e in E), []).append(pi)
            for ps in g.values():
                if len(ps) < 2:
                    continue
                for val in product((0, 1), repeat=size):
                    ts = [t for t in range(nT) if tuple(T[t][e] for e in E) == val]
                    for pi in ps[1:]:
                        add([(ps[0] * nT + t, 1) for t in ts] + [(pi * nT + t, -1) for t in ts], 0)
    nv = len(profs) * nT
    A = sp.csr_matrix((vals, (rows, cs)), shape=(len(b), nv))
    c = np.zeros(nv)
    for pi, pr in enumerate(profs):
        for t in range(nT):
            if t not in pr:
                c[pi * nT + t] = -1
    res = linprog(c, A_eq=A, b_eq=np.array(b), bounds=(0, 1), method="highs")
    return max(0.0, -res.fun)


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
    print("Part 3: full compatibility (empirical models in the sense of Abramsky and Brandenburger)")
    for N in (2, 3):
        print(f"  m=3 N={N}: largest deviation of a model from the mixture of dictatorships: "
              f"{full_compatibility_gap(N):.3f}")
    for N in (2, 3, 4):
        print(f"  m=3 N={N}: coin rule admits fully compatible lotteries: {coin_fully_compatible(N)}")
    print("Part 4: full compatibility with more alternatives (mass outside the voters' rankings)")
    for m, N in [(3, 2), (3, 3), (4, 2)]:
        print(f"  m={m} N={N}: {full_compat_support(m, N):.3f}")


if __name__ == "__main__":
    main()
