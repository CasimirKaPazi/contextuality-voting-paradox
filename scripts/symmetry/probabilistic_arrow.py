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

Part 4 (four alternatives). Up to four voters, every fully compatible unanimous family
is a mixture of dictatorships, in three steps: (1) no mass outside the voters' rankings;
(2) at all but a few profiles the triple marginals, which Theorem 5 of Four Levels fixes,
then determine the lottery; (3) at the remaining profiles, full compatibility with a
profile that differs in one voter's ranking fixes it. Theorem 5 of Four Levels proves
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
from itertools import combinations_with_replacement, product, permutations, combinations
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
    """Part 4, step 1. Largest total mass that a fully compatible unanimous family can put
    on rankings that no voter holds, summed over profiles.

    The feasible set and this objective are invariant under permuting the voters and
    renaming the alternatives, so the maximum is attained at a model invariant under both.
    For an anonymous model a profile is a multiset of rankings, and full compatibility says
    that multisets with the same multiset of restrictions to a set E of pairs have the same
    joint law on E. The program is set up on orbits of (multiset, ranking) under renaming,
    with one set E per orbit of such sets."""
    import scipy.sparse as sp
    alts = range(m)
    pairs = list(combinations(alts, 2))
    R = list(permutations(alts)); nR = len(R)
    Ridx = {r: i for i, r in enumerate(R)}
    T = np.array([[int(r.index(a) < r.index(b)) for a, b in pairs] for r in R])
    profs = list(combinations_with_replacement(range(nR), N)); P = len(profs)
    pid = {q: i for i, q in enumerate(profs)}
    pa = np.array(profs)
    perms_alt = list(permutations(alts))
    lab = np.full((P, nR), np.iinfo(np.int64).max, dtype=np.int64)
    for pi in perms_alt:
        ra = np.array([Ridx[tuple(pi[x] for x in r)] for r in R])
        qi = np.array([pid[tuple(x)] for x in np.sort(ra[pa], axis=1)])
        np.minimum(lab, qi[:, None] * nR + ra[None, :], out=lab)
    _, orb = np.unique(lab, return_inverse=True)
    orb = orb.reshape(P, nR); nv = orb.max() + 1

    def rowsum(mask):
        ts = np.nonzero(mask)[0]
        r = np.repeat(np.arange(P), len(ts))
        return sp.csr_matrix((np.ones(len(r)), (r, orb[:, ts].ravel())), shape=(P, nv))

    blocks, rhs = [rowsum(np.ones(nR, bool))], [np.ones(P)]
    for e in range(len(pairs)):
        bits = T[pa][:, :, e]
        for allv, want in ((0, 1), (1, 0)):
            M = rowsum(T[:, e] == want)[np.all(bits == allv, axis=1)]
            blocks.append(M); rhs.append(np.zeros(M.shape[0]))
    seen = set()
    for size in range(1, len(pairs)):
        for E in combinations(range(len(pairs)), size):
            c = min(tuple(sorted(tuple(sorted((pi[pairs[e][0]], pi[pairs[e][1]]))) for e in E))
                    for pi in perms_alt)
            if c in seen:
                continue
            seen.add(c)
            pat = (T[:, list(E)] * (2 ** np.arange(len(E)))).sum(1)
            first, rep = {}, np.empty(P, dtype=np.int64)
            for k, q in enumerate(profs):
                rep[k] = first.setdefault(tuple(sorted(pat[list(q)])), k)
            sel = rep != np.arange(P)
            for val in range(2 ** len(E)):
                if (pat == val).any():
                    M = rowsum(pat == val)
                    blocks.append(M[sel] - M[rep[sel]]); rhs.append(np.zeros(int(sel.sum())))
    A = sp.vstack(blocks).tocsr()
    outside = np.array([[t not in q for t in range(nR)] for q in profs])
    c = -np.bincount(orb[outside], minlength=nv).astype(float)
    res = linprog(c, A_eq=A, b_eq=np.concatenate(rhs), bounds=(0, 1), method="highs")
    return max(0.0, -res.fun)


def triple_separation(m, N):
    """Part 4, steps 2 and 3. Given step 1, a model at a profile is a distribution on the
    voters' distinct rankings whose triple marginals are those of the mixture of
    dictatorships (Theorem 5 applied to each triple). Step 2: count the profiles at which
    these marginals do not determine such a distribution. Step 3: for each of them, check
    that every remaining direction is killed by full compatibility with a profile that
    differs in one voter's ranking, shares the columns on some set E of pairs, and is
    determined by step 2. Returns (number of undetermined multisets, number not resolved)."""
    alts = range(m)
    pairs = list(combinations(alts, 2))
    R = list(permutations(alts))
    triples = list(combinations(alts, 3))

    def tri_matrix(D):
        return np.array([[int(sorted(tr, key=R[t].index) == list(sg)) for t in D]
                         for tr in triples for sg in permutations(tr)])

    def separated(prof):
        D = sorted(set(prof))
        return np.linalg.matrix_rank(tri_matrix(D)) == len(D)

    bits = [[int(r.index(a) < r.index(b)) for a, b in pairs] for r in R]
    undetermined = unresolved = 0
    for q in combinations_with_replacement(range(len(R)), N):
        if separated(q):
            continue
        undetermined += 1
        D = sorted(set(q))
        _, sv, vt = np.linalg.svd(tri_matrix(D))
        K = vt[np.sum(sv > 1e-9):]                       # directions not fixed by triples
        rows = []
        for k in range(N):
            for r2 in range(len(R)):
                if r2 == q[k]:
                    continue
                q2 = q[:k] + (r2,) + q[k + 1:]
                if not separated(q2):
                    continue
                E = [e for e in range(len(pairs)) if bits[r2][e] == bits[q[k]][e]]
                for size in range(1, len(E) + 1):
                    for F in combinations(E, size):
                        for val in product((0, 1), repeat=size):
                            ind = np.array([int(all(bits[t][f] == v for f, v in zip(F, val)))
                                            for t in D])
                            rows.append(K @ ind)
        if not rows or np.linalg.matrix_rank(np.array(rows), tol=1e-9) < K.shape[0]:
            unresolved += 1
    return undetermined, unresolved

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
    print("Part 4: full compatibility with four alternatives")
    for m, N in [(3, 3), (4, 2), (4, 3), (4, 4)]:
        und, unres = triple_separation(m, N)
        print(f"  m={m} N={N}: mass outside the voters' rankings {full_compat_support(m, N):.3f}; "
              f"profiles not fixed by triples {und}, of which not resolved by one-voter changes {unres}")


if __name__ == "__main__":
    main()
