"""What individually rational groups can do to a participant in CORE's sequential variant.

Participant i refuses every proposal and calls (the strategy of the CORE paper's Proposition 2).
Every group S without i that the process reaches settles on a lottery L_S over the outcomes
that each member weakly prefers to the lottery a call at S would lead to (individual
rationality); calling is the case L_S = that lottery.  The worst value to i over all such
behaviour is a linear program, G_i.  Variant: L_S must also be Pareto-efficient for the members
of S (mixed-integer program, support of L_S inside the maximisers of a positive weighting).
Compared with the endowment e_i and the paper's floor f_i against arbitrary others.
Part 5: under strictly concave loss on a line, the weights w = A^-1 1 with A = [h(|q_k - q_m|)]
are positive (the criterion for the random ballot to be Pareto-efficient for the members).
"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

def groups_without(n, i):
    others = [j for j in range(n) if j != i]
    return [frozenset(c) for r in range(2, n) for c in itertools.combinations(others, r)]

def setup(n, K, i):
    G = groups_without(n, i)
    idx = {S: g for g, S in enumerate(G)}
    nv = len(G) * K
    D = {}                                   # D[S]: (K x nv matrix, K constant) final outcome law from S
    for j in range(n):
        S = frozenset([j]); D[S] = (np.zeros((K, nv)), None)
    subsets = [frozenset(c) for r in range(2, n + 1) for c in itertools.combinations(range(n), r)]
    return G, idx, nv, D, subsets

def build(U, i):
    n, K = U.shape
    ideal = U.argmax(1)
    G, idx, nv, D, subsets = setup(n, K, i)
    for j in range(n):
        c = np.zeros(K); c[ideal[j]] = 1; D[frozenset([j])] = (np.zeros((K, nv)), c)
    call, ineq = {}, []
    for S in subsets:
        A = sum(D[S - {k}][0] for k in S) / len(S); b = sum(D[S - {k}][1] for k in S) / len(S)
        call[S] = (A, b)
        if S in idx:
            g = idx[S]; A2 = np.zeros((K, nv)); A2[:, g*K:(g+1)*K] = np.eye(K)
            D[S] = (A2, np.zeros(K))
            for j in S:   # u_j . call - u_j . L_S <= 0
                ineq.append((U[j] @ A - U[j] @ A2, -(U[j] @ b)))
        else:
            D[S] = call[S]
    V = frozenset(range(n))
    obj = (U[i] @ D[V][0], U[i] @ D[V][1])
    Aeq = np.zeros((len(G), nv))
    for g in range(len(G)): Aeq[g, g*K:(g+1)*K] = 1
    return G, idx, nv, ineq, Aeq, obj, call, D

def rational_floor(U, i):
    G, idx, nv, ineq, Aeq, obj, call, D = build(U, i)
    if nv == 0: return obj[1], None
    Aub = np.array([r for r, _ in ineq]); bub = np.array([b for _, b in ineq])
    res = linprog(obj[0], A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=np.ones(len(G)), bounds=(0, 1), method="highs")
    assert res.status == 0, res.message
    return res.fun + obj[1], res.x

def efficient_floor(U, i, lam_max=50.0, big=None):
    """Worst value to i when every group without i agrees on a lottery that is individually rational and
    Pareto-efficient for its members: support of L_S within argmax of sum_j lam_j u_j, lam_j in [1, lam_max]."""
    n, K = U.shape
    G, idx, nv, ineq, Aeq, obj, call, D = build(U, i)
    if nv == 0: return obj[1]
    rng = U.max() - U.min(); big = big or 2 * lam_max * n * rng + 1
    # variable layout: [L (nv)] [z (nv)] [lam per group member] [M per group]
    lam_index = {}; p = 2 * nv
    for S in G:
        for j in sorted(S): lam_index[(S, j)] = p; p += 1
    M_index = {S: p + g for g, S in enumerate(G)}; N = p + len(G)
    rows, lo, hi = [], [], []
    def add(row, l, h): rows.append(row); lo.append(l); hi.append(h)
    for r, b in ineq:
        row = np.zeros(N); row[:nv] = r; add(row, -np.inf, b)
    for g in range(len(G)):
        row = np.zeros(N); row[g*K:(g+1)*K] = 1; add(row, 1, 1)
    for S in G:
        g = idx[S]
        for o in range(K):
            v = g*K + o
            row = np.zeros(N); row[v] = 1; row[nv + v] = -1; add(row, -np.inf, 0)        # L <= z
            row = np.zeros(N)
            for j in S: row[lam_index[(S, j)]] = U[j, o]
            row[M_index[S]] = -1; add(row.copy(), -np.inf, 0)                            # score <= M
            row[nv + v] = -big; add(row, -big, np.inf)                                   # score >= M - big(1-z)
    c = np.zeros(N); c[:nv] = obj[0]
    lb = np.zeros(N); ub = np.ones(N)
    for k in lam_index.values(): lb[k], ub[k] = 1, lam_max
    for k in M_index.values(): lb[k], ub[k] = -np.inf, np.inf
    integ = np.zeros(N); integ[nv:2*nv] = 1
    res = milp(c, constraints=LinearConstraint(np.array(rows), lo, hi), integrality=integ, bounds=Bounds(lb, ub))
    if res.status != 0:
        if lam_max < 1e4: return efficient_floor(U, i, lam_max * 10)
        raise RuntimeError(res.message)
    return res.fun + obj[1]

def floors(U, i):
    n, K = U.shape; ideal = U.argmax(1)
    t = U[i, ideal[i]]; e = np.mean([U[i, ideal[j]] for j in range(n)])
    ebar = np.mean([U[i, ideal[j]] for j in range(n) if j != i]); w = U[i].min()
    f = t / n + ebar / n + (n - 2) / n * w if n > 2 else e
    return f, e

def greedy_value(U, i):
    """Each group without i, smallest first, picks the individually rational lottery worst for i."""
    n, K = U.shape; ideal = U.argmax(1)
    D = {frozenset([j]): np.eye(K)[ideal[j]] for j in range(n)}
    for r in range(2, n + 1):
        for S in map(frozenset, itertools.combinations(range(n), r)):
            c = sum(D[S - {k}] for k in S) / r
            if i in S: D[S] = c; continue
            res = linprog(U[i], A_ub=np.array([-U[j] for j in S]), b_ub=np.array([-(U[j] @ c) for j in S]),
                          A_eq=np.ones((1, K)), b_eq=[1], bounds=(0, 1), method="highs")
            D[S] = res.x
    return U[i] @ D[frozenset(range(n))]

def ballot_gain(U, S):
    """Largest utilitarian gain of a lottery all members of S weakly prefer to their random ballot."""
    K = U.shape[1]; ideal = U.argmax(1); E = np.zeros(K)
    for j in S: E[ideal[j]] += 1 / len(S)
    res = linprog(-U[list(S)].sum(0), A_ub=np.array([-U[j] for j in S]), b_ub=np.array([-(U[j] @ E) for j in S]),
                  A_eq=np.ones((1, K)), b_eq=[1], bounds=(0, 1), method="highs")
    return -res.fun - U[list(S)].sum(0) @ E

def line_instance(rng, n, K, kind):
    pos = rng.uniform(0, 1, n)
    out = rng.uniform(-0.2, 1.2, K) if kind == "peaks not available" else np.concatenate([pos, rng.uniform(-0.2, 1.2, K - n)])
    d = np.abs(pos[:, None] - out[None, :])
    if kind == "tent, rescaled": return -rng.uniform(0.2, 5, (n, 1)) * d + rng.uniform(-1, 1, (n, 1))
    if kind == "quadratic loss": return -d ** 2
    if kind == "square-root loss": return -np.sqrt(d)
    return -d

if __name__ == "__main__":
    rng = np.random.default_rng(1)
    U = np.array([[10, 5, 5, -100], [0, 10, 0, 9], [0, 0, 10, 9]], float)
    f, e = floors(U, 0); g, _ = rational_floor(U, 0)
    print(f"Part 1, the CORE paper's example, participant 1: f = {f:.2f}, G = {g:.2f}, "
          f"efficient G = {efficient_floor(U, 0):.2f}, e = {e:.2f}")
    print("Part 2, independent uniform utilities, participant 1; differences in units of its utility range")
    for n, K, T in [(3, 4, 100), (4, 5, 100), (5, 6, 60), (6, 6, 20)]:
        r = []
        for _ in range(T):
            U = rng.uniform(0, 1, (n, K)); f, e = floors(U, 0); g, _ = rational_floor(U, 0)
            sp = U[0].max() - U[0].min()
            ge = efficient_floor(U, 0) if n <= 5 else np.nan
            r.append(((g - f) / sp, (e - g) / sp, g < e - 1e-9, (greedy_value(U, 0) - g) / sp, (ge - g) / sp))
        r = np.array(r, float)
        eff = f"{np.mean(r[:, 4]):.3f}" if n <= 5 else "  -  "
        print(f"  n={n} K={K}: mean (G - f) {np.mean(r[:, 0]):.3f}, mean (e - G) {np.mean(r[:, 1]):.3f}, "
              f"share with G < e {np.mean(r[:, 2]):.2f}, largest (greedy - G) {np.max(r[:, 3]):.3f}, "
              f"mean (efficient G - G) {eff}")
    print("Part 3, outcomes on a line; largest (e - G) over all participants, in units of utility range")
    for kind in ["tent", "tent, rescaled", "peaks not available", "quadratic loss", "square-root loss"]:
        worst = 0; cases = 0; total = 0
        for n, K, T in [(4, 8, 40), (5, 8, 30), (6, 8, 10)]:
            for _ in range(T):
                U = line_instance(rng, n, K, kind)
                for i in range(n):
                    f, e = floors(U, i); g, _ = rational_floor(U, i)
                    gap = (e - g) / (U[i].max() - U[i].min()); worst = max(worst, gap)
                    cases += gap > 1e-7; total += 1
        print(f"  {kind:20s} largest {worst:.2e}, cases with G < e: {cases}/{total}")
    worst = 0; cases = 0; total = 0
    for n, K, T in [(4, 8, 40), (5, 8, 30), (6, 8, 10)]:
        for _ in range(T):
            pos = rng.uniform(0, 1, (n, 2)); out = np.concatenate([pos, rng.uniform(0, 1, (K - n, 2))])
            U = -np.linalg.norm(pos[:, None, :] - out[None, :, :], axis=2)
            for i in range(n):
                f, e = floors(U, i); g, _ = rational_floor(U, i)
                gap = (e - g) / (U[i].max() - U[i].min()); worst = max(worst, gap); cases += gap > 1e-7; total += 1
    print(f"  {'plane, distance':20s} largest {worst:.2e}, cases with G < e: {cases}/{total}")
    print("Part 4, largest gain of an individually rational lottery over a group's random ballot (whole group, 2 to 6 members)")
    for kind in ["square-root loss", "tent", "quadratic loss"]:
        best = 0
        for _ in range(150):
            n = int(rng.integers(2, 7)); U = line_instance(rng, n, n + int(rng.integers(1, 8)), kind)
            best = max(best, ballot_gain(U, tuple(range(n))))
        print(f"  {kind:20s} {best:.2e}")
    print("Part 5, smallest min(w)/max|w| for w = A^-1 1, A = [h(|q_k - q_m|)], 4000 peak sets of 2 to 11 members")
    hs = {"square root": np.sqrt, "power 0.3": lambda d: d**0.3, "power 0.99": lambda d: d**0.99,
          "log(1 + 50 d)": lambda d: np.log1p(50*d), "1 - exp(-5 d)": lambda d: 1 - np.exp(-5*d),
          "min(d, 0.3), not strictly concave": lambda d: np.minimum(d, 0.3)}
    for name, h in hs.items():
        worst = np.inf
        for t in range(4000):
            m = int(rng.integers(2, 12))
            q = np.sort(rng.uniform(0, 1, m)) if t % 3 else np.sort(np.concatenate(
                [rng.normal(c, 0.01, m // 2 + 1) for c in rng.uniform(0, 1, 2)]))[:m]
            A = h(np.abs(q[:, None] - q[None, :]))
            w = np.linalg.solve(A, np.ones(m)); worst = min(worst, w.min() / np.abs(w).max())
        print(f"  {name:34s} {worst:.2e}")
