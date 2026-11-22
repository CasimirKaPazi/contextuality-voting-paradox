"""The mean of the peaks as a rule for every group (CORE note, Section 3e).

Peaks p_j in R^d, utilities u_j(x) = -h(||x - p_j||) with a norm and an increasing loss h, outcomes
anywhere in the convex hull of the peaks. Under the mean rule every group the process reaches agrees
on the mean mu_S of its members' peaks; its call is then the uniform lottery over the points mu_{S-k},
which are the peaks reflected through mu_S and shrunk by 1/(|S| - 1).

Part 1: for convex h (here d, d^1.5, d^2) and the norms L1, L2, Linf, in dimension 2 and 3, the mean rule
        is individually rational for every member of every group, and every participant ends with at
        least their endowment. For concave h (sqrt) both fail.
Part 2: with the Euclidean norm and h(d) = d, no point of the hull is strictly better than mu_S for every
        member of S (the mean is efficient).
Part 3: in the plane, Euclidean distance, outcomes = peaks, means of all groups and a few other points of
        the hull: the five rules of bargaining_rules.py against the mean rule (share below endowment,
        mean gain, distance of the final expected position from mu_V). With quadratic loss the
        utilitarian rule is the mean rule.
Run: python3 mean_rule.py   (numpy and scipy; a few minutes)
"""
import itertools
import numpy as np
from scipy.optimize import minimize

from bargaining_rules import holdings, endowments, RULES

NORMS = {"L1": 1, "L2": 2, "Linf": np.inf}
LOSSES = {"d": lambda d: d, "d^1.5": lambda d: d ** 1.5, "d^2": lambda d: d ** 2, "sqrt d": np.sqrt}


def groups(n):
    for r in range(1, n + 1):
        yield from map(frozenset, itertools.combinations(range(n), r))


def mean_rule_margins(P, norm, h):
    """Smallest IR margin over all groups and members, and smallest holding minus endowment."""
    n = len(P)
    mu = {S: P[sorted(S)].mean(0) for S in groups(n)}
    u = lambda j, x: -h(np.linalg.norm(x - P[j], ord=norm))
    ir = np.inf
    for S in mu:
        if len(S) < 2:
            continue
        call = [mu[S - {k}] for k in S]
        for m in S:
            ir = min(ir, u(m, mu[S]) - np.mean([u(m, x) for x in call]))
    V = frozenset(range(n))
    end = min(u(i, mu[V]) - np.mean([u(i, P[j]) for j in range(n)]) for i in range(n))
    return ir, end


def part1(T=300, seed=1):
    rng = np.random.default_rng(seed)
    for lname, h in LOSSES.items():
        for nname, nm in NORMS.items():
            worst_ir = worst_end = np.inf
            for _ in range(T):
                n = int(rng.integers(2, 7)); d = int(rng.integers(2, 4))
                ir, end = mean_rule_margins(rng.uniform(0, 1, (n, d)), nm, h)
                worst_ir, worst_end = min(worst_ir, ir), min(worst_end, end)
            print(f"Part 1, loss {lname:6s} norm {nname:4s}: smallest IR margin {worst_ir:+.2e}, "
                  f"smallest holding minus endowment {worst_end:+.2e}")


def part2(T=200, seed=2):
    rng = np.random.default_rng(seed)
    worst = -np.inf
    for _ in range(T):
        s = int(rng.integers(2, 7)); P = rng.uniform(0, 1, (s, 2)); mu = P.mean(0)
        base = np.linalg.norm(P - mu, axis=1)
        # maximise t with ||y - p_j|| <= base_j - t for all j (y unrestricted; the hull is no restriction here)
        cons = [{"type": "ineq", "fun": (lambda z, j=j: base[j] - z[2] - np.linalg.norm(z[:2] - P[j]))}
                for j in range(s)]
        res = minimize(lambda z: -z[2], np.r_[mu, 0.0], constraints=cons, method="SLSQP")
        worst = max(worst, -res.fun)
    print(f"Part 2, Euclidean, linear loss: largest uniform strict improvement on the mean over {T} groups: "
          f"{worst:.1e}")


def plane_instance(rng, n, extra=4, power=1):
    P = rng.uniform(0, 1, (n, 2))
    pts = [P[sorted(S)].mean(0) for S in groups(n)]          # peaks and all group means
    w = rng.dirichlet(np.ones(n), extra); pts += list(w @ P)  # a few more points of the hull
    X = np.array(pts)
    U = -np.linalg.norm(P[:, None, :] - X[None, :, :], axis=2) ** power
    return P, X, U


def part3(sizes=((3, 25), (4, 12)), seed=3):
    rng = np.random.default_rng(seed)
    for power, label in ((1, "distance"), (2, "squared distance")):
        stats = {r: [] for r in RULES + ["mean"]}
        dist = {r: [] for r in RULES}
        for n, T in sizes:
            for _ in range(T):
                P, X, U = plane_instance(rng, n, power=power)
                e = endowments(U); span = U.max(1) - U.min(1)
                mu = P.mean(0)
                k = next(i for i, x in enumerate(X) if np.allclose(x, mu))
                stats["mean"].extend(((U[:, k] - e) / span).tolist())
                for r in RULES:
                    h, law = holdings(U, r, return_law=True)
                    stats[r].extend(((h - e) / span).tolist())
                    dist[r].append(np.linalg.norm(law @ X - mu))
        print(f"Part 3, plane, {label}:")
        for r in RULES + ["mean"]:
            d = np.array(stats[r])
            extra = "" if r == "mean" else f"   distance of the expected outcome from the mean {np.mean(dist[r]):.3f}"
            print(f"     {r:12s} below endowment {np.mean(d < -1e-7):5.2f}   mean gain {d.mean():+.4f}{extra}")


if __name__ == "__main__":
    part1(); part2(); part3()
