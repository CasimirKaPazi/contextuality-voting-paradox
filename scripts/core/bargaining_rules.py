"""CORE's sequential variant with a fixed bargaining rule in every group (CORE note, Section 3d).

Every group S the process reaches bargains over lotteries on the outcomes, with its own call as the
disagreement point: the lottery c(S), the average of the outcome laws of the groups S minus one member.
All participants follow the rule; nobody refuses. Rules (each picks a lottery that every member weakly
prefers to c(S); if no member can gain, the group calls):
  call         every group calls (holdings = endowments)
  utilitarian  largest sum of the members' gains
  Kalai-Smor.  largest equal fraction of each member's largest possible gain
  Nash         largest product of the gains of the members who can gain
  Raiffa 1     each member's best individually rational lottery, averaged (random dictatorship over the
               improvements, one step)
  Raiffa       the same step repeated, each time from the last point, until it stops moving
Part 1 (line, losses proportional to distance, peaks available, any weights): every rule ends at the
lottery with mean equal to the mean of all peaks, so every participant holds the value of that point.
Part 2, reported per family of instances, in units of each participant's utility range: the share of
participants below their endowment, the largest shortfall, the mean gain over the endowment, and the
largest shortfall that individual rationality alone allows (e - G of Section 3b), for comparison.
Run: python3 bargaining_rules.py   (numpy and scipy; a few minutes)
"""
import itertools
import numpy as np
from scipy.optimize import linprog, minimize

from rational_floor import rational_floor, line_instance

EPS = 1e-9


def lp_max(c, A_ub, b_ub, K):
    res = linprog(-c, A_ub=A_ub, b_ub=b_ub, A_eq=np.ones((1, K)), b_eq=[1], bounds=(0, 1), method="highs")
    if res.status != 0:
        return None, None
    return res.x, -res.fun


def best_for(A, d, m):
    """Member m's best lottery among those all members weakly prefer to d; ties broken towards the others."""
    K = A.shape[1]
    x, v = lp_max(A[m], -A, -(d - 1e-10), K)
    A2 = np.vstack([-A, -A[m:m + 1]]); b2 = np.concatenate([-(d - 1e-10), [-(v - 1e-10)]])
    x2, _ = lp_max(A.sum(0) - A[m], A2, b2, K)
    return x if x2 is None else x2


def rule_point(name, A, d):
    s, K = A.shape
    d = d - 1e-10  # numerical slack: the call itself must stay feasible
    bests = [best_for(A, d, m) for m in range(s)]
    b = np.array([A[m] @ bests[m] for m in range(s)])
    can = b > d + EPS
    if not can.any():
        return None
    if name == "utilitarian":
        return lp_max(A.sum(0), -A, -d, K)[0]
    if name == "Kalai-Smor.":
        # variables (x, t): maximise t, A x - d >= t (b - d) on members who can gain
        A_ub = np.hstack([-A, np.where(can, b - d, 0)[:, None]]); b_ub = -d
        res = linprog(np.r_[np.zeros(K), -1], A_ub=A_ub, b_ub=b_ub, A_eq=np.r_[np.ones(K), 0][None, :],
                      b_eq=[1], bounds=[(0, 1)] * K + [(0, None)], method="highs")
        return res.x[:K]
    x0 = np.mean(bests, axis=0)
    if name == "Raiffa 1":
        return x0
    if name == "Raiffa":
        x, dd = x0, A @ x0
        for _ in range(100):
            nb = [best_for(A, dd, m) for m in range(s)]
            xn = np.mean(nb, axis=0)
            if np.abs(A @ xn - dd).max() < 1e-8:
                break
            x, dd = xn, A @ xn
        return x
    if name == "Nash":
        idx = np.where(can)[0]
        f = lambda x: -np.sum(np.log(np.maximum(A[idx] @ x - d[idx], 1e-300)))
        cons = [{"type": "eq", "fun": lambda x: x.sum() - 1},
                {"type": "ineq", "fun": lambda x: A @ x - d}]
        res = minimize(f, x0, method="SLSQP", bounds=[(0, 1)] * K, constraints=cons,
                       options={"ftol": 1e-12, "maxiter": 500})
        x = np.clip(res.x, 0, None); x /= x.sum()
        return x if (A @ x >= d - 1e-7).all() and f(x) <= f(x0) + 1e-9 else x0
    raise ValueError(name)


def holdings(U, name, return_law=False):
    n, K = U.shape
    ideal = U.argmax(1)
    D = {frozenset([j]): np.eye(K)[ideal[j]] for j in range(n)}
    for r in range(2, n + 1):
        for S in map(frozenset, itertools.combinations(range(n), r)):
            c = sum(D[S - {k}] for k in S) / r
            if name == "call":
                D[S] = c; continue
            mem = sorted(S)
            x = rule_point(name, U[mem], U[mem] @ c)
            D[S] = c if x is None else x
    law = D[frozenset(range(n))]
    return (U @ law, law) if return_law else U @ law


def endowments(U):
    ideal = U.argmax(1)
    return U[:, ideal].mean(1)


RULES = ["utilitarian", "Kalai-Smor.", "Nash", "Raiffa 1", "Raiffa"]


def families(rng):
    def uniform(n, K):
        return rng.uniform(0, 1, (n, K))

    def plane(n, K):
        pos = rng.uniform(0, 1, (n, 2)); out = np.concatenate([pos, rng.uniform(0, 1, (K - n, 2))])
        return -np.linalg.norm(pos[:, None, :] - out[None, :, :], axis=2)

    return {
        "independent uniform": uniform,
        "line, linear loss": lambda n, K: line_instance(rng, n, K, "tent"),
        "line, quadratic loss": lambda n, K: line_instance(rng, n, K, "quadratic loss"),
        "plane, distance": plane,
    }


def part1(T=60, seed=11):
    rng = np.random.default_rng(seed)
    worst = 0.0
    for _ in range(T):
        n = int(rng.integers(2, 6)); K = n + int(rng.integers(1, 5))
        pos = rng.uniform(0, 1, n); out = np.concatenate([pos, rng.uniform(-0.2, 1.2, K - n)])
        alpha = rng.uniform(0.2, 5, n); beta = rng.uniform(-1, 1, n)
        U = -alpha[:, None] * np.abs(pos[:, None] - out[None, :]) + beta[:, None]
        target = -alpha * np.abs(pos.mean() - pos) + beta
        for r in RULES:
            worst = max(worst, np.abs(holdings(U, r) - target).max())
    print(f"Part 1, line with linear loss: largest |holding - value of the mean of the peaks| over all rules: "
          f"{worst:.1e}")


def main(sizes=((3, 5, 40), (4, 6, 30), (5, 7, 12)), seed=7):
    rng = np.random.default_rng(seed)
    print("Part 2, shifts against the endowment, in units of utility range")
    for fam, gen in families(rng).items():
        stats = {r: [] for r in RULES}
        floor_gap = []
        for n, K, T in sizes:
            for _ in range(T):
                U = gen(n, K)
                e = endowments(U)
                span = U.max(1) - U.min(1)
                for i in range(n):
                    g, _ = rational_floor(U, i)
                    floor_gap.append((e[i] - g) / span[i])
                for r in RULES:
                    h = holdings(U, r)
                    stats[r].extend(((h - e) / span).tolist())
        print(f"  {fam} ({len(floor_gap)} participants); largest shortfall individual rationality allows: "
              f"{max(floor_gap):.3f}")
        for r in RULES:
            d = np.array(stats[r])
            print(f"     {r:12s} below endowment {np.mean(d < -1e-7):5.2f}   largest shortfall {max(0, -d.min()):.3f}"
                  f"   mean gain {d.mean():+.4f}")


if __name__ == "__main__":
    part1(); main()
