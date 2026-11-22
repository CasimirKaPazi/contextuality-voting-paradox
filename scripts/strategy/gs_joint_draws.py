"""Joint draws versus SD-strategy-proofness in the Gibbard–Satterthwaite scenario
(note *Gibbard–Satterthwaite as a Scenario*, Section 2).

Part 1. For a single pair of ballots: random pairs of lotteries that are SD-ordered both ways
        (truthful report not dominated, either way) and a test for a joint draw supported on
        admissible pairs.  Three alternatives: always one.  Four: not always.
Part 2. The small example for four alternatives, checked exactly.
Part 3. The example does not extend to a whole SD-strategy-proof scheme of one voter.
Part 4. The proof of Proposition 1 run as a computation: for vertices of the polytope of
        one-voter SD-strategy-proof schemes, the joint draw along a shortest path of adjacent
        swaps is built explicitly and checked (marginals and support)."""
import itertools, numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
NAME = "abcde"

def sd(p, q, r):  # p SD-dominates q for ranking r
    m = len(r)
    return all(sum(p[x] for x in r[:t]) >= sum(q[x] for x in r[:t]) - 1e-12 for t in range(1, m))

def admissible(x, y, r, r2):  # truthful outcome x under r, outcome y under report r2: no gain either way
    return r.index(x) <= r.index(y) and r2.index(y) <= r2.index(x)

def has_joint_draw(p, q, r, r2):
    m = len(r)
    ok = [(x, y) for x in range(m) for y in range(m) if admissible(x, y, r, r2)]
    A, b = [], []
    for x in range(m):
        A.append([1.0 if a == x else 0.0 for a, _ in ok]); b.append(float(p[x]))
        A.append([1.0 if c == x else 0.0 for _, c in ok]); b.append(float(q[x]))
    return linprog(np.zeros(len(ok)), A_eq=A, b_eq=b, bounds=(0, None), method="highs").status == 0

print("Part 1: single pairs of ballots")
rng = np.random.default_rng(1)
for m in (3, 4):
    R = list(itertools.permutations(range(m))); both = bad = 0
    for _ in range(20000):
        r, r2 = R[rng.integers(len(R))], R[rng.integers(len(R))]
        p, q = rng.dirichlet(np.ones(m) * 0.5), rng.dirichlet(np.ones(m) * 0.5)
        if sd(p, q, r) and sd(q, p, r2):
            both += 1; bad += not has_joint_draw(p, q, r, r2)
    print(f"  m={m}: {both} pairs SD-ordered both ways, {bad} without a joint draw")

print("Part 2: the example")
r, r2 = (0, 1, 2, 3), (1, 2, 3, 0)          # a>b>c>d and b>c>d>a
p = [F(1, 4), F(0), F(1, 4), F(1, 2)]       # lottery at a>b>c>d
q = [F(0), F(1, 4), F(0), F(3, 4)]          # lottery at b>c>d>a
print("  p SD-dominates q for a>b>c>d:", sd(p, q, r), "; q SD-dominates p for b>c>d>a:", sd(q, p, r2))
print("  admissible partners of c:", [NAME[y] for y in range(4) if admissible(2, y, r, r2)],
      "; q(c) =", q[2], "< p(c) =", p[2], "; joint draw:", has_joint_draw(p, q, r, r2))

print("Part 3: extension to a whole one-voter scheme")
m = 4; R = list(itertools.permutations(range(m))); N = len(R)
def v(i, x): return i * m + x
def polytope(m, R):
    N = len(R); Aeq = lil_matrix((N, N * m))
    for i in range(N):
        for x in range(m): Aeq[i, i * m + x] = 1
    rows = []
    for i in range(N):
        for j in range(N):
            if i != j:
                for t in range(1, m):
                    d = {}
                    for x in R[i][:t]:
                        d[j * m + x] = d.get(j * m + x, 0) + 1; d[i * m + x] = d.get(i * m + x, 0) - 1
                    rows.append(d)
    Aub = lil_matrix((len(rows), N * m))
    for k, d in enumerate(rows):
        for key, val in d.items(): Aub[k, key] = val
    return Aub.tocsr(), np.zeros(len(rows)), Aeq.tocsr(), np.ones(N)
Aub, bub, Aeq, beq = polytope(m, R)
fix = lil_matrix((2 * m, N * m)); fb = []
for k, (rr, lot) in enumerate(((r, p), (r2, q))):
    for x in range(m): fix[k * m + x, v(R.index(rr), x)] = 1; fb.append(float(lot[x]))
from scipy.sparse import vstack
res = linprog(np.zeros(N * m), A_ub=Aub, b_ub=bub, A_eq=vstack([Aeq, fix.tocsr()]),
              b_eq=np.concatenate([beq, fb]), bounds=(0, 1), method="highs")
print("  extends to an SD-strategy-proof scheme:", res.status == 0)

print("Part 4: joint draws along shortest paths of adjacent swaps")
def path(r, r2):  # bubble sort from r towards r2: each step swaps an adjacent pair on which they disagree
    cur, out, pos = list(r), [tuple(r)], {x: k for k, x in enumerate(r2)}
    changed = True
    while changed:
        changed = False
        for k in range(len(cur) - 1):
            if pos[cur[k]] > pos[cur[k + 1]]:
                cur[k], cur[k + 1] = cur[k + 1], cur[k]; out.append(tuple(cur)); changed = True
    return out
worst = 0; checked = 0
for trial in range(60):
    c = rng.normal(size=N * m)
    L = linprog(-c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=(0, 1), method="highs").x.reshape(N, m)
    for i in range(N):
        for j in range(N):
            if i == j: continue
            P = path(R[i], R[j]); J = np.diag(L[i])
            for a, b in zip(P, P[1:]):
                k = next(t for t in range(m) if a[t] != b[t]); x, y = a[k], a[k + 1]   # x above y in a
                pa, pb = L[R.index(a)], L[R.index(b)]
                others = [z for z in range(m) if z not in (x, y)]
                worst = max(worst, max(abs(pa[z] - pb[z]) for z in others), pb[x] - pa[x])  # localised, x loses
                K = np.eye(m)
                if pa[x] > 1e-12:
                    K[x, x] = pb[x] / pa[x]; K[x, y] = 1 - pb[x] / pa[x]
                J = J @ K
            worst = max(worst, np.abs(J.sum(0) - L[j]).max())
            for x in range(m):
                for y in range(m):
                    if J[x, y] > 1e-9 and not admissible(x, y, R[i], R[j]): worst = max(worst, J[x, y])
            checked += 1
print(f"  {checked} pairs of ballots in 60 vertices: largest violation {worst:.1e}")
