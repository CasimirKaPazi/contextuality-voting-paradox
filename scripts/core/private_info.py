"""Private information in the call game (CORE note, Section 3h).

Part 1, public ideals and private attitudes. Every member's utility is some concave function on the
        outcome space with its maximum at the member's (known) ideal. Under the mean rule, every
        proposal other than one with mean mu_S is rejected by some member for some such utility: the
        script constructs the rejecting utility -||x - p_m|| - lam * max(0, <v, x - p_m>) of the proof
        for random off-mean points and lotteries in the plane and checks the rejection. On the line,
        every lottery with mean mu_S that is not less risky than the call is rejected too (stop-loss
        utilities -|x - q_1| - lam * max(0, x - t)).
Part 2, private ideals on the line. If the agreement were the mean of declared ideals in [0, 1], with
        losses proportional to distance, best replies converge to the median of the ideals and the
        points k/n, k = 1..n-1 (Renault and Trannoy's median formula for equal weights). How often does
        that outcome leave a member below their true endowment, the random ballot over true ideals?
Part 3, strategy-proof rules on a grid. The line is a grid of K points; members report single-peaked
        strict orders, and a rule assigns a lottery to every profile of orders (not only of peaks).
        Strategy-proofness in the sense of stochastic dominance and no harm (every member, with loss
        proportional to distance from their peak, weakly prefers the rule to the random ballot) are
        linear constraints. The largest total gain over the random ballot is zero, and pushing in random
        directions inside the feasible set stays at the random ballot.
Run: python3 private_info.py   (numpy and scipy; about two minutes, most of it for K = 5 with three
members)
"""
import itertools
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog


def mean_rule_call(P, S):
    """Under the mean rule, the call at S: uniform over the means of S minus one member."""
    S = sorted(S)
    return np.array([P[[j for j in S if j != k]].mean(0) for k in S])


def part1(T=500, seed=9):
    rng = np.random.default_rng(seed)
    fails = 0
    for _ in range(T):
        n = int(rng.integers(3, 7)); P = rng.uniform(0, 1, (n, 2))
        call = mean_rule_call(P, range(n)); mu = P.mean(0)
        # a lottery whose mean is not mu
        L = mu + rng.normal(scale=0.1, size=(3, 2)) + rng.normal(scale=0.05, size=2)
        w = rng.dirichlet(np.ones(3)); mL = w @ L
        v = (mL - mu) / np.linalg.norm(mL - mu)
        m = int(np.argmin(P @ v))                       # the member furthest back in direction v
        lam = 10.0 / max(1e-9, v @ (mL - mu))
        u = lambda X: -np.linalg.norm(X - P[m], axis=-1) - lam * np.maximum(0, (X - P[m]) @ v)
        if not w @ u(L) < u(call).mean():
            fails += 1
    print(f"Part 1, plane: off-mean lotteries not rejected by the constructed utility: {fails} of {T}")
    fails = tested = 0
    for _ in range(T):
        n = int(rng.integers(3, 7)); q = np.sort(rng.uniform(0, 1, n))
        call = mean_rule_call(q[:, None], range(n))[:, 0]; mu = q.mean()
        # a lottery on [q1, qn] with mean mu: two points around mu, spread out
        a, b = rng.uniform(q[0], mu), rng.uniform(mu, q[-1]); pa = (b - mu) / (b - a)
        Lx, Lw = np.array([a, b]), np.array([pa, 1 - pa])
        ts = np.linspace(q[0], q[-1], 401)
        gap = [(Lw @ np.maximum(0, Lx - t)) - np.maximum(0, call - t).mean() for t in ts]
        k = int(np.argmax(gap))
        if gap[k] <= 1e-9:
            continue                                   # this lottery is less risky than the call
        tested += 1; t = ts[k]; lam = 10.0 / gap[k]
        u = lambda x: -np.abs(x - q[0]) - lam * np.maximum(0, x - t)
        if not Lw @ u(Lx) < u(call).mean():
            fails += 1
    print(f"Part 1, line: lotteries with the right mean but riskier than the call, not rejected: "
          f"{fails} of {tested}")


def average_rule_equilibrium(p, iters=2000):
    n = len(p); r = p.copy()
    for _ in range(iters):
        old = r.copy()
        for i in range(n):
            rest = r.sum() - r[i]
            r[i] = np.clip(n * p[i] - rest, 0, 1)       # best reply: bring the mean to p_i if possible
        if np.abs(r - old).max() < 1e-12:
            break
    return r.mean()


def part2(T=4000, seed=10):
    rng = np.random.default_rng(seed)
    dev = 0.0; below = 0; worst = 0.0; members = 0
    for _ in range(T):
        n = int(rng.integers(2, 8)); p = rng.uniform(0, 1, n)
        x = average_rule_equilibrium(p)
        formula = np.median(np.r_[p, np.arange(1, n) / n])
        dev = max(dev, abs(x - formula))
        endow = -np.abs(p[:, None] - p[None, :]).mean(1)
        short = endow - (-np.abs(x - p))
        members += n; below += int((short > 1e-9).sum()); worst = max(worst, short.max())
    print(f"Part 2, line: largest |equilibrium - median formula| {dev:.1e}; members below their true "
          f"endowment {below / members:.3f}, by up to {worst:.3f} (the interval has length 1)")


def single_peaked_orders(K):
    res = []
    for peak in range(K):
        left, right = list(range(peak - 1, -1, -1)), list(range(peak + 1, K))
        for pos in itertools.combinations(range(K - 1), len(left)):
            o, li, ri = [peak], 0, 0
            for t in range(K - 1):
                if t in pos:
                    o.append(left[li]); li += 1
                else:
                    o.append(right[ri]); ri += 1
            res.append(tuple(o))
    return res


def grid_check(K, n, directions=5, seed=0):
    O = single_peaked_orders(K); m = len(O)
    profiles = list(itertools.product(range(m), repeat=n)); idx = {p: i for i, p in enumerate(profiles)}
    P = len(profiles); nv = P * K
    rows, cols, vals, b = [], [], [], []; r = 0
    for p in profiles:                                  # strategy-proofness (stochastic dominance)
        for i in range(n):
            o = O[p[i]]
            for lie in range(m):
                if lie == p[i]:
                    continue
                q = list(p); q[i] = lie
                for k in range(1, K):
                    for x in o[:k]:
                        rows += [r, r]; cols += [idx[tuple(q)] * K + x, idx[p] * K + x]; vals += [1, -1]
                    b.append(0); r += 1
    obj = np.zeros(nv); RB = np.zeros((P, K))
    for p in profiles:                                  # no harm against the random ballot
        pk = [O[a][0] for a in p]
        for x in pk:
            RB[idx[p], x] += 1 / n
        for i in range(n):
            for x in range(K):
                rows.append(r); cols.append(idx[p] * K + x); vals.append(abs(x - pk[i]))
                obj[idx[p] * K + x] += abs(x - pk[i])
            b.append(np.mean([abs(pj - pk[i]) for pj in pk])); r += 1
    A = sp.csr_matrix((vals, (rows, cols)), shape=(r, nv))
    eq = dict(A_eq=sp.csr_matrix((np.ones(nv), (np.repeat(np.arange(P), K), np.arange(nv))), shape=(P, nv)),
              b_eq=np.ones(P), bounds=(0, 1), method="highs")
    res = linprog(obj, A_ub=A, b_ub=b, **eq)
    gain = (obj @ RB.ravel()) - res.fun
    A2 = sp.vstack([A, sp.csr_matrix(obj[None, :])]); b2 = np.r_[b, obj @ RB.ravel() + 1e-9]
    rng = np.random.default_rng(seed); far = np.abs(res.x - RB.ravel()).max()
    for _ in range(directions):
        c = rng.normal(size=nv)
        for sgn in (1, -1):
            x = linprog(sgn * c, A_ub=A2, b_ub=b2, **eq).x
            far = max(far, np.abs(x - RB.ravel()).max())
    print(f"Part 3, grid of {K} points, {n} members ({m} orders each): largest total gain {gain:.1e}, "
          f"largest distance from the random ballot {far:.1e}")


def part3():
    for K, n in ((4, 2), (5, 2), (4, 3), (5, 3)):
        grid_check(K, n)


if __name__ == "__main__":
    part1(); part2(); part3()
