"""Gibbard-Satterthwaite as a scenario: one variable per profile (the outcome), one context per
pair of profiles differing in one voter's ballot, admissible pairs (x, x') with x weakly better
than x' for the voter's ballot in the first profile and x' weakly better than x for its ballot in
the second (no gain by switching either way); unanimity as boundary condition.
An empirical model: a lottery p(pi) per profile and, per context, a joint draw with these
marginals supported on admissible pairs.  Linear programs for small cases:
  (1) the largest total probability of outcomes that are nobody's top choice;
  (2) the largest spread of a voter's apparent weight across profiles;
  (3) the same with only SD-strategy-proofness (both directions) instead of joint draws.
Both objectives are 0 on every case run, for both conditions: the models are the mixtures of
dictatorships (Gibbard–Satterthwaite note, Section 3).  Usage: python3 gs_scenario.py m n.
From four alternatives on only the SD form is run (it gives the same models, Section 2).
Cases run: m = 3 with n = 2 and 3; m = 4 with n = 2.  m = 3, n = 3 takes some minutes."""
import itertools, sys, numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
m, n = int(sys.argv[1]), int(sys.argv[2])
A = range(m); R = list(itertools.permutations(A))
P = list(itertools.product(range(len(R)), repeat=n)); pidx = {p: i for i, p in enumerate(P)}
def better_eq(r, x, y): return R[r].index(x) <= R[r].index(y)
pairs = []
for p in P:
    for k in range(n):
        for r2 in range(len(R)):
            if r2 > p[k]:
                q = list(p); q[k] = r2; pairs.append((pidx[p], pidx[tuple(q)], k))
def build(joint):
    nv = len(P) * m; off = nv
    if joint: nv += len(pairs) * m * m
    rows, rhs, ub_rows, ub_rhs = [], [], [], []
    def var(pi, x): return pi * m + x
    eq = []
    for pi in range(len(P)):                      # lotteries sum to 1
        eq.append(({var(pi, x): 1 for x in A}, 1))
    for pi, p in enumerate(P):                    # unanimity
        tops = {R[r][0] for r in p}
        if len(tops) == 1:
            a = tops.pop(); eq.append(({var(pi, a): 1}, 1))
    ub = []
    for c, (i, j, k) in enumerate(pairs):
        ri, rj = P[i][k], P[j][k]
        if joint:
            def jv(x, y): return off + c * m * m + x * m + y
            for x in A:
                eq.append(({**{jv(x, y): 1 for y in A}, var(i, x): -1}, 0))
                eq.append(({**{jv(y, x): 1 for y in A}, var(j, x): -1}, 0))
            for x in A:
                for y in A:
                    if not (better_eq(ri, x, y) and better_eq(rj, y, x)):
                        eq.append(({jv(x, y): 1}, 0))
        else:
            # SD: for every upper set of ballot ri, p(i) has at least as much as p(j); and vice versa for rj
            for t in range(1, m):
                up = R[ri][:t]
                ub.append(({**{var(j, x): 1 for x in up}, **{var(i, x): -1 for x in up}}, 0))
                up = R[rj][:t]
                ub.append(({**{var(i, x): 1 for x in up}, **{var(j, x): -1 for x in up}}, 0))
    def mat(cons):
        M = lil_matrix((len(cons), nv)); b = np.zeros(len(cons))
        for r, (d, v) in enumerate(cons):
            for key, val in d.items(): M[r, key] += val
            b[r] = v
        return M.tocsr(), b
    Aeq, beq = mat(eq)
    Aub, bub = mat(ub) if ub else (None, None)
    return nv, Aeq, beq, Aub, bub, var
for joint in ((False,) if m >= 4 else (True, False)):
    nv, Aeq, beq, Aub, bub, var = build(joint)
    # (1) probability of outcomes that are nobody's top, summed over profiles
    c = np.zeros(nv)
    for pi, p in enumerate(P):
        tops = {R[r][0] for r in p}
        for x in A:
            if x not in tops: c[var(pi, x)] = -1
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=(0, 1), method="highs")
    worst_off_top = -res.fun
    # (2) spread of voter 0's weight: profiles where voter 0's top differs from all others' tops
    best = 0
    sel = [pi for pi, p in enumerate(P) if all(R[p[0]][0] != R[p[k]][0] for k in range(1, n))]
    rng = np.random.default_rng(0)
    for _ in range(6):
        i1, i2 = rng.choice(sel, 2, replace=False)
        c = np.zeros(nv); c[var(i1, R[P[i1][0]][0])] = -1; c[var(i2, R[P[i2][0]][0])] = 1
        res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=(0, 1), method="highs")
        best = max(best, -res.fun)
    print(f"m={m} n={n} {'joint draws' if joint else 'SD only    '}: max prob. of non-top outcomes {worst_off_top:.2e}; "
          f"max spread of voter 1's weight {best:.2e}")
