"""One scenario with electorates as contexts: consistency and participation together.

Anonymous rules on m alternatives; a profile is a non-empty multiset of strict
rankings with at most n voters. The variable at a profile p is its winner W(p).

Contexts:
  joins       {p, q, p+q}   constraint: W(p) = W(q)  implies  W(p+q) = W(p)
  extensions  {p, p+v}      constraint: the added voter v weakly prefers W(p+v) to W(p)
Boundary condition: W(p) is the Condorcet winner of p when p has one.

A weakly compatible family (one joint draw per context, with the rule's
lotteries as marginals) is the same as lotteries L(p) with
  L(p+q)(a) >= L(p)(a) + L(q)(a) - 1             for every join and candidate a
  L(p+v) first-order dominates L(p) for v       for every extension
(joint-draw lemma of Consistency as an Extension Problem, Section 3b, and
Strassen's theorem on a chain). Deterministic rules are the 0/1 solutions,
the global sections. On a one-voter join {p, v, p+v}, W(v) is v's top choice
and the extension constraint implies the join constraint.
An empirical model must also agree on pairs of profiles shared by two
contexts, e.g. the joins {p, q, p+q} and {p, p+q, 2p+q}; that is not imposed
here. Infeasibility therefore means: no weakly compatible family, hence no
empirical model. Feasibility of the lottery problem means only that a weakly
compatible family exists. (Extensions alone share no pair of profiles, so
there feasibility gives an empirical model.)

For each n the script decides feasibility of four problems:
  C  joins only, P  extensions only, C+P  both,
each as a linear program (lotteries) and as an integer program (deterministic).
Output: the smallest n at which each becomes infeasible, within the range tried.
Result for m = 3, n <= 12: C and C+P fail from 8 voters (deterministic) and
9 voters (lotteries); P is feasible throughout. For m = 4 the problem grows too
large beyond n = 4, where everything is feasible.
Usage: python3 electorate_scenario.py [m] [nmax]
"""
import sys
from itertools import permutations, combinations_with_replacement
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix


def setup(m, n):
    R = list(permutations(range(m)))
    k = len(R)
    beats = np.zeros((k, m, m), int)            # beats[r, x, y] = 1 if ranking r puts x above y
    for i, r in enumerate(R):
        pos = {a: j for j, a in enumerate(r)}
        for x in range(m):
            for y in range(m):
                if x != y and pos[x] < pos[y]:
                    beats[i, x, y] = 1
    profiles = []
    for size in range(1, n + 1):
        for ms in combinations_with_replacement(range(k), size):
            c = [0] * k
            for t in ms:
                c[t] += 1
            profiles.append(tuple(c))
    index = {p: i for i, p in enumerate(profiles)}

    def cw(p):
        M = np.tensordot(np.array(p), beats, 1)
        for x in range(m):
            if all(M[x, y] > M[y, x] for y in range(m) if y != x):
                return x
        return None
    winner = [cw(p) for p in profiles]
    return R, profiles, index, winner


def build(m, n, use_joins, use_ext):
    R, profiles, index, winner = setup(m, n)
    k = len(R)
    free = [i for i, w in enumerate(winner) if w is None]
    col = {}
    for i in free:
        for a in range(m):
            col[(i, a)] = len(col)
    nv = len(col)

    def term(i, a):
        """Return ('var', column) or ('const', value) for L(profile i)(a)."""
        if winner[i] is None:
            return ('var', col[(i, a)])
        return ('const', 1.0 if winner[i] == a else 0.0)

    rows, cols, vals, ub = [], [], [], []
    r = 0

    def add(coeffs, const, bound):
        """sum coeff * L + const <= bound, coeffs over terms."""
        nonlocal r
        c0 = const
        entries = {}
        for (kind, x), cf in coeffs:
            if kind == 'var':
                entries[x] = entries.get(x, 0.0) + cf
            else:
                c0 += cf * x
        entries = {x: v for x, v in entries.items() if v != 0}
        if not entries:
            if c0 > bound + 1e-9:
                return False
            return True
        for x, v in entries.items():
            rows.append(r); cols.append(x); vals.append(v)
        ub.append(bound - c0)
        r += 1
        return True

    ok = True
    if use_joins:
        P = len(profiles)
        sizes = [sum(p) for p in profiles]
        for i in range(P):
            for j in range(i, P):
                if sizes[i] + sizes[j] > n:
                    continue
                s = tuple(a + b for a, b in zip(profiles[i], profiles[j]))
                h = index[s]
                if winner[i] is not None and winner[j] is not None and winner[h] is not None:
                    continue
                for a in range(m):
                    # L(i)(a) + L(j)(a) - L(h)(a) <= 1
                    ok &= add([(term(i, a), 1.0), (term(j, a), 1.0), (term(h, a), -1.0)], 0.0, 1.0)
    if use_ext:
        for i, p in enumerate(profiles):
            if sum(p) >= n:
                continue
            for v in range(k):
                q = list(p); q[v] += 1
                h = index[tuple(q)]
                if winner[i] is not None and winner[h] is not None:
                    continue
                order = R[v]
                for t in range(1, m):
                    top = order[:t]
                    # sum_{a in top} L(i)(a) - L(h)(a) <= 0
                    ok &= add([(term(i, a), 1.0) for a in top] + [(term(h, a), -1.0) for a in top], 0.0, 0.0)
    A_ub = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr() if r else None
    # each free profile's lottery sums to 1
    er, ec = [], []
    for e, i in enumerate(free):
        for a in range(m):
            er.append(e); ec.append(col[(i, a)])
    A_eq = coo_matrix((np.ones(len(er)), (er, ec)), shape=(len(free), nv)).tocsr()
    return ok, nv, A_ub, np.array(ub), A_eq, len(free), len(profiles)


def feasible(m, n, use_joins, use_ext, integer):
    ok, nv, A_ub, b_ub, A_eq, nfree, nprof = build(m, n, use_joins, use_ext)
    if not ok:
        return False
    if nv == 0:
        return True
    if not integer:
        res = linprog(np.zeros(nv), A_ub=A_ub, b_ub=b_ub if A_ub is not None else None,
                      A_eq=A_eq, b_eq=np.ones(nfree), bounds=(0, 1), method='highs')
        return res.status == 0
    cons = [LinearConstraint(A_eq, np.ones(nfree), np.ones(nfree))]
    if A_ub is not None:
        cons.append(LinearConstraint(A_ub, -np.inf, b_ub))
    res = milp(np.zeros(nv), constraints=cons, integrality=np.ones(nv),
               bounds=Bounds(0, 1), options={'time_limit': 600})
    if res.status == 0:
        return True
    if res.status == 2:   # infeasible
        return False
    return None           # time limit or other


def main():
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    problems = [('C', True, False), ('P', False, True), ('C+P', True, True)]
    first_fail = {}
    for n in range(1, nmax + 1):
        line = []
        for name, j, e in problems:
            for integer in (False, True):
                key = (name, integer)
                if key in first_fail:      # infeasibility persists for larger n
                    line.append(f"{name}{'/det' if integer else '/lot'}: -")
                    continue
                f = feasible(m, n, j, e, integer)
                if f is False:
                    first_fail[key] = n
                line.append(f"{name}{'/det' if integer else '/lot'}: {'?' if f is None else ('yes' if f else 'NO')}")
        print(f"m={m} n<={n}: " + "  ".join(line), flush=True)
    print("first n without an empirical model:", {f"{k[0]}/{'det' if k[1] else 'lot'}": v for k, v in first_fail.items()})


if __name__ == "__main__":
    main()
