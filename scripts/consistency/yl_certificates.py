"""Certificates of Young-Levenglick in the electorate scenario (Consistency as an Extension Problem,
Section 3d).

Three alternatives, anonymous profiles of at most n voters, joins {p, q, p+q} as contexts, the
Condorcet principle as boundary condition (the scenario of electorate_scenario.py, joins only).

Part 1, lotteries drawn jointly. At n = 8 a weakly compatible family exists. From n = 9 on there is
        none, and a Farkas certificate of least total weight has three rows of weight 1. They share
        one profile q without a Condorcet winner; for each candidate x there is a row (p_x, q, p_x + q)
        in which p_x has Condorcet winner x and p_x + q has as Condorcet winner the candidate that
        beats x in q. Each row forces L(q)(x) = 0, and the three contradict sum L(q) = 1. This is
        the blocking lemma at one profile. Checked for n = 9, 10, 11 (q is the doubled Condorcet
        profile at n = 9).
Part 2, deterministic rules. At n = 8 there is no consistent Condorcet extension, but no profile is
        blocked on its own: every profile without a Condorcet winner keeps a candidate that no join
        with a Condorcet profile excludes. A minimal infeasible set has ten such profiles: the
        Condorcet profile Q0, six four-voter profiles with two unbeaten candidates, and three
        eight-voter joins of them. The script checks infeasibility, minimality (dropping any one
        profile makes the rest satisfiable), and the three-case proof: W(Q0) = x forces the
        eight-voter profile above x to x through a five-voter electorate with Condorcet winner x,
        while the two four-voter profiles below it are pushed off x by their joins with Q0, onto
        the candidate y that beats x, and their join then forces y.
Run: python3 yl_certificates.py [n ...]   (numpy and scipy; about a minute for n = 9, 10, 11)
"""
import sys

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import coo_matrix, csr_matrix, hstack, identity, vstack

import electorate_scenario as S

M = 3
NAMES = None


def names(R):
    return ["".join("abc"[x] for x in r) for r in R]


def show(p, nm):
    return "{" + ", ".join(f"{c}×{nm[i]}" for i, c in enumerate(p) if c) + "}"


def beats_matrix(R):
    return np.array([[[1 if r.index(x) < r.index(y) else 0 for y in range(M)] for x in range(M)] for r in R])


def join_rows(profiles, index, winner, n):
    """The join rows in the order of electorate_scenario.build (rows without variables dropped)."""
    P = len(profiles)
    sizes = [sum(p) for p in profiles]
    rows = []
    for i in range(P):
        for j in range(i, P):
            if sizes[i] + sizes[j] > n:
                continue
            h = index[tuple(a + b for a, b in zip(profiles[i], profiles[j]))]
            if all(winner[t] is not None for t in (i, j, h)):
                continue
            for a in range(M):
                rows.append((i, j, h, a))
    return rows


def part1(ns):
    print("Part 1: lotteries drawn jointly")
    print(f"  n = 8: weakly compatible family exists: {S.feasible(M, 8, True, False, False)}")
    for n in ns:
        R, profiles, index, winner = S.setup(M, n)
        nm = names(R)
        B = beats_matrix(R)
        ok, nv, A, b, E, nf, _ = S.build(M, n, True, False)
        r = A.shape[0]
        # Farkas: y >= 0, z free, w >= 0 with A^T y + E^T z + w >= 0 and b.y + 1.z + 1.w <= -1
        M1 = -hstack([A.T.tocsr(), E.T.tocsr(), identity(nv)]).tocsr()
        row = csr_matrix(np.r_[b, np.ones(nf), np.ones(nv)])
        res = linprog(np.r_[np.ones(r), np.zeros(nf), np.ones(nv)],
                      A_ub=vstack([M1, row]).tocsr(), b_ub=np.r_[np.zeros(nv), -1],
                      bounds=[(0, None)] * r + [(None, None)] * nf + [(0, None)] * nv, method="highs")
        y = res.x[:r]
        supp = np.where(y > 1e-9)[0]
        rows = join_rows(profiles, index, winner, n)
        assert len(rows) == r
        sel = [rows[k] for k in supp]
        # identify the shared free profile and check the blocking shape
        frees = {t for (i, j, h, a) in sel for t in (i, j, h) if winner[t] is None}
        shape = len(frees) == 1 and len(sel) == M and np.allclose(y[supp], 1)
        q = frees.pop() if len(frees) == 1 else None
        if shape:
            Mq = np.tensordot(np.array(profiles[q]), B, 1)
            for (i, j, h, a) in sel:
                p = j if i == q else i
                beater = [c for c in range(M) if c != a and Mq[c, a] > Mq[a, c]]
                shape &= winner[p] == a and winner[h] in beater
            shape &= {a for (*_, a) in sel} == set(range(M))
        print(f"  n = {n}: certificate with {len(supp)} rows, total weight {res.fun:.0f};"
              f" blocking shape at one profile: {shape}; q = {show(profiles[q], nm) if q is not None else '-'}")
        if n == ns[0]:
            for (i, j, h, a) in sel:
                p = j if i == q else i
                print(f"     candidate {'abc'[a]}: {show(profiles[p], nm)} (winner {'abc'[winner[p]]}) + q"
                      f" has Condorcet winner {'abc'[winner[h]]}")
    print()


CORE8 = [  # name: ballots
    ("Q0", {"abc": 1, "bca": 1, "cab": 1}),
    ("Q1", {"abc": 1, "acb": 1, "cba": 2}),
    ("Q2", {"abc": 1, "bac": 2, "cab": 1}),
    ("Q3", {"abc": 1, "bca": 1, "cba": 2}),
    ("Q4", {"acb": 2, "bac": 1, "bca": 1}),
    ("Q5", {"acb": 2, "bca": 1, "cab": 1}),
    ("Q6", {"bca": 2, "cab": 1, "cba": 1}),
    ("Q7", {"abc": 1, "acb": 3, "bca": 1, "cab": 1, "cba": 2}),
    ("Q8", {"abc": 1, "acb": 2, "bac": 3, "bca": 1, "cab": 1}),
    ("Q9", {"abc": 1, "bca": 3, "cab": 1, "cba": 3}),
]


def part2():
    n = 8
    print("Part 2: deterministic rules, n = 8")
    R, profiles, index, winner = S.setup(M, n)
    nm = names(R)
    P = len(profiles)
    sizes = [sum(p) for p in profiles]
    free = [i for i in range(P) if winner[i] is None]
    joins = []
    U = {q: set(range(M)) for q in free}
    for i in range(P):
        for j in range(i, P):
            if sizes[i] + sizes[j] > n:
                continue
            h = index[tuple(a + b for a, b in zip(profiles[i], profiles[j]))]
            if all(winner[t] is not None for t in (i, j, h)):
                continue
            joins.append((i, j, h))
            for x, yy in ((i, j), (j, i)):
                if winner[x] is not None and winner[yy] is None and winner[h] is not None and winner[h] != winner[x]:
                    U[yy].discard(winner[x])
    print(f"  profiles without a Condorcet winner: {len(free)}; blocked on their own: "
          f"{sum(1 for q in free if not U[q])}")
    core = [index[tuple(d.get(s, 0) for s in nm)] for _, d in CORE8]
    lab = {q: name for q, (name, _) in zip(core, CORE8)}

    def feasible(Fset):
        col = {(q, a): k for k, (q, a) in enumerate((q, a) for q in sorted(Fset) for a in sorted(U[q]))}
        rows, cols, vals, ub = [], [], [], []
        for (i, j, h) in joins:
            if any(winner[t] is None and t not in Fset for t in (i, j, h)):
                continue
            for a in range(M):
                cst, ent = 0.0, {}
                for t, cf in ((i, 1), (j, 1), (h, -1)):
                    if winner[t] is not None:
                        cst += cf * (winner[t] == a)
                    elif (t, a) in col:
                        ent[col[(t, a)]] = ent.get(col[(t, a)], 0) + cf
                if not ent:
                    if cst > 1:
                        return False
                    continue
                for x, v in ent.items():
                    rows.append(len(ub)); cols.append(x); vals.append(v)
                ub.append(1 - cst)
        er = [e for e, q in enumerate(sorted(Fset)) for a in U[q]]
        ec = [col[(q, a)] for q in sorted(Fset) for a in sorted(U[q])]
        cons = [LinearConstraint(coo_matrix((np.ones(len(er)), (er, ec)), shape=(len(Fset), len(col))).tocsr(), 1, 1)]
        if ub:
            cons.append(LinearConstraint(coo_matrix((vals, (rows, cols)), shape=(len(ub), len(col))).tocsr(), -np.inf, ub))
        return milp(np.zeros(len(col)), constraints=cons, integrality=np.ones(len(col)), bounds=Bounds(0, 1)).status == 0

    print(f"  all {len(free)} profiles satisfiable: {feasible(set(free))}")
    print(f"  the ten profiles satisfiable: {feasible(set(core))}; "
          f"each nine of them satisfiable: {all(feasible(set(core) - {q}) for q in core)}")
    for q, (name, _) in zip(core, CORE8):
        print(f"     {name} {show(profiles[q], nm):42} unblocked candidates {''.join('abc'[a] for a in sorted(U[q]))}")

    def find(x, y, z):  # a join x + y = z, any of them given as a label or as 'CW=c'
        for (i, j, h) in joins:
            for (u, v) in ((i, j), (j, i)):
                if all((lab.get(t) == s) if not s.startswith("CW=") else (winner[t] == "abc".index(s[3]))
                       for t, s in ((u, x), (v, y), (h, z))):
                    return True
        return False
    cases = {"a": ("Q7", "Q1", "Q5", "c"), "b": ("Q8", "Q2", "Q4", "a"), "c": ("Q9", "Q3", "Q6", "b")}
    for x, (top, l1, l2, beater) in cases.items():
        steps = [find("Q0", "CW=" + x, top), find("Q0", l1, "CW=" + beater), find("Q0", l2, "CW=" + beater),
                 find(l1, l2, top)]
        dom = {"abc"[a] for a in U[core[int(l1[1])]]} == {x, beater} == {"abc"[a] for a in U[core[int(l2[1])]]}
        print(f"  case W(Q0) = {x}: Q0 + (winner {x}) = {top}; Q0 + {l1} and Q0 + {l2} have winner {beater};"
              f" {l1} + {l2} = {top}; {l1}, {l2} unbeaten {{{x}, {beater}}}: {all(steps) and dom}")
    print()


if __name__ == "__main__":
    ns = [int(a) for a in sys.argv[1:]] or [9, 10, 11]
    part1(ns)
    part2()
