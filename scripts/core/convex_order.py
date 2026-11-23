"""Agreements that are safe for every concave utility (CORE note, Section 3f).

An agreement L at a group S is weakly preferred to the call c(S) by every expected utility with a
concave utility function on the outcome space exactly when L is below c(S) in the convex order:
there is a coupling (X, Y) with X ~ L, Y ~ c(S) and E[Y | X] = X, so that L arises from the call by
pooling outcomes into blocks and enacting each block's mean (Strassen).

Part 1: pooling agreements in the plane. Every group the process reaches pools the atoms of its call
        into random blocks and enacts the block means (with full pooling this is the mean rule). For
        random utilities -h(||x - p||) with norms L1, L2, Linf and convex increasing h, and for random
        concave piecewise linear utilities, every participant ends with at least the endowment.
Part 2: the five rules of bargaining_rules.py in the plane (Euclidean distance, outcomes = ideals, the
        means of all groups and four further points of the hull). For each reached group: is the
        rule's agreement below the call in the convex order (a linear program for the coupling)?
        How far are outsiders from their endowment when it is not?
Run: python3 convex_order.py   (numpy and scipy; under a minute)
"""
import itertools
import numpy as np
from scipy.optimize import linprog

from bargaining_rules import rule_point, endowments, RULES
from mean_rule import groups, plane_instance

# ---------------------------------------------------------------- part 1: pooling in the plane


def pool(atoms, weights, rng):
    """Random partition of the atoms into blocks; each block is replaced by its mean."""
    k = len(atoms)
    lab = rng.integers(0, rng.integers(1, k + 1), k)
    pts, ws = [], []
    for b in np.unique(lab):
        idx = lab == b
        w = weights[idx].sum()
        pts.append((weights[idx, None] * atoms[idx]).sum(0) / w); ws.append(w)
    return np.array(pts), np.array(ws)


def pooling_process(P, rng):
    n = len(P)
    D = {frozenset([j]): (P[[j]], np.ones(1)) for j in range(n)}
    for S in groups(n):
        if len(S) < 2:
            continue
        pts = np.vstack([D[S - {k}][0] for k in S])
        ws = np.concatenate([D[S - {k}][1] for k in S]) / len(S)
        D[S] = pool(pts, ws, rng)
    return D[frozenset(range(n))]


def random_concave(rng, P, j):
    """A random concave utility peaked at p_j: a norm with convex loss, or a minimum of affine maps."""
    if rng.random() < 0.5:
        nm = [1, 2, np.inf][rng.integers(3)]; g = rng.uniform(1, 3)
        return lambda X: -np.linalg.norm(X - P[j], ord=nm, axis=-1) ** g
    A = rng.normal(size=(6, P.shape[1])); b = rng.normal(size=6)
    return lambda X: np.min(X @ A.T + b, axis=-1)


def part1(T=400, seed=4):
    rng = np.random.default_rng(seed)
    worst = np.inf
    for _ in range(T):
        n = int(rng.integers(2, 6)); P = rng.uniform(0, 1, (n, 2))
        pts, ws = pooling_process(P, rng)
        for j in range(n):
            u = random_concave(rng, P, j)
            worst = min(worst, ws @ u(pts) - u(P).mean())
    print(f"Part 1, pooling agreements in every group, {T} instances: smallest holding minus endowment "
          f"{worst:+.2e}")

# ---------------------------------------------------------------- part 2: the rules and the convex order


def cx_violation(X, L, c, tol=1e-6):
    """Least total violation of E[Y | X] = X over couplings of L and c (0 when L is below c)."""
    I = np.flatnonzero(L > tol); J = np.flatnonzero(c > tol)
    a, b = L[I] / L[I].sum(), c[J] / c[J].sum()
    nI, nJ, d = len(I), len(J), X.shape[1]
    nv = nI * nJ + 2 * nI * d                       # coupling, then positive and negative deviations
    A_eq, b_eq = [], []
    for i in range(nI):
        row = np.zeros(nv); row[i * nJ:(i + 1) * nJ] = 1; A_eq.append(row); b_eq.append(a[i])
    for j in range(nJ):
        row = np.zeros(nv); row[j:nI * nJ:nJ] = 1; A_eq.append(row); b_eq.append(b[j])
    for i in range(nI):
        for t in range(d):
            row = np.zeros(nv)
            row[i * nJ:(i + 1) * nJ] = X[J, t] - X[I[i], t]
            base = nI * nJ + 2 * (i * d + t)
            row[base], row[base + 1] = -1, 1
            A_eq.append(row); b_eq.append(0.0)
    cost = np.r_[np.zeros(nI * nJ), np.ones(2 * nI * d)]
    for method in ("highs", "highs-ipm"):       # the simplex can fail on tiny masses
        res = linprog(cost, A_eq=np.array(A_eq), b_eq=b_eq, bounds=(0, None), method=method)
        if res.status == 0:
            return res.fun
    raise RuntimeError(res.message)


def part2(sizes=((3, 40), (4, 20)), seed=5):
    rng = np.random.default_rng(seed)
    out = {r: {"groups": 0, "unsafe": 0, "harm": 0, "outsiders": 0, "worst": 0.0} for r in RULES}
    for n, T in sizes:
        for _ in range(T):
            P, X, U = plane_instance(rng, n)
            K = len(X); ideal = U.argmax(1); span = U.max(1) - U.min(1)
            for r in RULES:
                D = {frozenset([j]): np.eye(K)[ideal[j]] for j in range(n)}
                for S in groups(n):
                    if len(S) < 2:
                        continue
                    c = sum(D[S - {k}] for k in S) / len(S)
                    mem = sorted(S)
                    x = rule_point(r, U[mem], U[mem] @ c)
                    D[S] = c if x is None else x
                    o = out[r]; o["groups"] += 1
                    if cx_violation(X, D[S], c) > 1e-6:
                        o["unsafe"] += 1
                        for i in set(range(n)) - S:      # outsiders: agreement against the call
                            o["outsiders"] += 1
                            g = (U[i] @ D[S] - U[i] @ c) / span[i]
                            if g < -1e-7:
                                o["harm"] += 1; o["worst"] = min(o["worst"], g)
    print("Part 2, plane, distance: the rules' agreements and the convex order")
    for r, o in out.items():
        print(f"     {r:12s} groups {o['groups']:4d}   not below the call {o['unsafe'] / o['groups']:5.2f}   "
              f"outsiders of those worse off than under the call {o['harm']:3d} of {o['outsiders']:3d}, "
              f"by up to {-o['worst']:.4f}")


if __name__ == "__main__":
    part1(); part2()
