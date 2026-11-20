"""
Can a Condorcet extension be consistent? Geometric test, three candidates, continuous vote shares.

Consistency means each winner region is convex. A Condorcet extension's winner region W_w contains
the Condorcet region R_w (a convex cone). Take a profile x in the cycle region. If x is assigned to w,
then every mixture of x with a point y of R_w must also be won by w. If some such mixture lies in
the Condorcet region R_v of another candidate v, assigning x to w is impossible.

For random x in the cycle region and each candidate w, solve a linear feasibility problem:
  exists t in (0,1), y in R_w (strictly), with t*x + (1-t)*y in R_v (strictly) for some v != w.
If this is feasible for all three w, no Condorcet extension can assign x consistently.

The few profiles reported as "not blocked" lie within EPS of a wall (a pairwise margin of
about zero), where the strict margins required by the test cannot be met; they are artefacts
of the tolerance. The elementary argument behind the result is given in notes/map-of-voting-paradoxes.md.
"""
import numpy as np
from itertools import permutations
from scipy.optimize import linprog

rng = np.random.default_rng(2)
C = "abc"
ORD = list(permutations(C))
pos = {x: np.array([o.index(x) for o in ORD]) for x in C}
mvec = {(x, y): np.where(pos[x] < pos[y], 1.0, -1.0) for x in C for y in C if x != y}   # margin of x over y = mvec @ p
EPS = 1e-4

def cond_winner(p):
    for x in C:
        if all(mvec[(x, y)] @ p > 0 for y in C if y != x): return x
    return None

def blocked(x, w, v):
    """Feasible: t in (0,1), u = (1-t) y >= 0 with y in R_w, and z = t x + u in R_v."""
    # variables: u (6), t (1)
    A_ub, b_ub = [], []
    for o in C:
        if o != w:   # y in R_w  <=>  m_wo(u) >= EPS (1 - t)  <=>  -m_wo(u) - EPS t <= -EPS
            A_ub.append(np.r_[-mvec[(w, o)], -EPS]); b_ub.append(-EPS)
        if o != v:   # z in R_v  <=>  m_vo(t x + u) >= EPS
            A_ub.append(np.r_[-mvec[(v, o)], -(mvec[(v, o)] @ x)]); b_ub.append(-EPS)
    A_eq = [np.r_[np.ones(6), 1.0]]; b_eq = [1.0]     # sum u = 1 - t
    bounds = [(0, None)] * 6 + [(EPS, 1 - EPS)]
    r = linprog(np.zeros(7), A_ub=np.array(A_ub), b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    return r.status == 0

samples = all_blocked = 0
free_counts = {w: 0 for w in C}
while samples < 2000:
    x = rng.dirichlet(np.ones(6))
    if cond_winner(x) is not None:
        continue
    samples += 1
    ok = [w for w in C if not any(blocked(x, w, v) for v in C if v != w)]
    for w in ok: free_counts[w] += 1
    all_blocked += (len(ok) == 0)
print(f"cycle-region profiles tested: {samples}")
print(f"profiles where every assignment is blocked: {all_blocked}")
print(f"profiles where assigning to a / b / c is not blocked: {free_counts}")
