"""Theorem 5 for m alternatives, induction step from m-1 to m: exact check.

A ranking x1 > ... > xm is the event 'xi above x(i+1) for every i' on the path of its
consecutive pairs, so its social probability at a profile depends only on the m-1 columns of
that path (full compatibility).  Give every voter the greedy linear extension of its pattern on
the path (top-down, for a fixed priority order).  The step needs, for the canonical path
a1-...-am (every other ranking is a renaming):
  (closure)  every ranking whose restrictions to all (m-1)-element subsets occur among the rule's
             rankings is one of them;
  (target)   the indicator of a1 > ... > am, on the rule's rankings, is a linear combination of
             the indicators 'restriction to an (m-1)-subset equals o'.
Then at the completed profile the social law lives on the rule's rankings and the probability of
the target equals the mixture's, whatever the weights.

Exactness: the script solves A y = e modulo a prime, lifts y to the rationals by rational
reconstruction, and verifies A y = e exactly over the integers, so a success is a proof.
Usage: python3 pin_path_certificate.py m priority"""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np
P = 2_147_483_629   # prime < 2^31
m = int(sys.argv[1]); prio = sys.argv[2]
alts = "abcdefghijkl"[:m]; assert sorted(prio) == list(alts)
S = [(alts[i], alts[i + 1]) for i in range(m - 1)]
subs = list(itertools.combinations(range(m), m - 1))
def greedy(pattern):
    above = {x: set() for x in alts}
    for (u, v), b in zip(S, pattern):
        (above[v] if b else above[u]).add(u if b else v)
    rank, left = [], set(alts)
    while left:
        x = min((y for y in left if not (above[y] & left)), key=prio.index)
        rank.append(x); left.remove(x)
    return "".join(rank)
def restr(r, T):
    keep = {alts[i] for i in T}; return "".join(c for c in r if c in keep)
pats = list(itertools.product((0, 1), repeat=m - 1))
rule = {p: greedy(p) for p in pats}
for p, r in rule.items():
    assert all((r.index(u) < r.index(v)) == bool(b) for (u, v), b in zip(S, p)), "pattern"
W = sorted(set(rule.values()))
seen = [set(restr(r, T) for r in W) for T in subs]
miss0 = alts[[i for i in range(m) if i not in subs[0]][0]]
cands = {s[:k] + miss0 + s[k:] for s in seen[0] for k in range(m)}
closure = sorted(c for c in cands if all(restr(c, T) in seen[j] for j, T in enumerate(subs)))
print(f"m={m}, priority {prio}: {len(W)} rule rankings; closure {'holds' if closure == W else 'FAILS'}")
assert closure == W
feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
A = np.array([[1 if restr(r, subs[j]) == o else 0 for (j, o) in feats] for r in W], dtype=np.int64)
target = "".join(alts); e = np.array([1 if r == target else 0 for r in W], dtype=np.int64)
# solve A y = e modulo P: reduce the augmented system (columns of A are unknowns)
M = np.concatenate([A, e[:, None]], axis=1).astype(object)
rows, cols = M.shape; piv = []; rk = 0
for c in range(cols - 1):
    nz = [i for i in range(rk, rows) if M[i, c] % P]
    if not nz: continue
    i = nz[0]; M[[rk, i]] = M[[i, rk]]
    inv = pow(int(M[rk, c]) % P, P - 2, P); M[rk] = [(x * inv) % P for x in M[rk]]
    for i2 in range(rows):
        if i2 != rk and M[i2, c] % P:
            f = M[i2, c]; M[i2] = [(x - f * y) % P for x, y in zip(M[i2], M[rk])]
    piv.append(c); rk += 1
    if rk == rows: break
consistent = all(M[i, cols - 1] % P == 0 for i in range(rk, rows))
assert consistent, "target not identified modulo P"
y = [0] * (cols - 1)
for i, c in enumerate(piv): y[c] = int(M[i, cols - 1])
def rat(a):   # rational reconstruction of a modulo P
    r0, r1, s0, s1 = P, a % P, 0, 1
    while r1 * r1 * 2 > P: q = r0 // r1; r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    return Fr(r1, s1)
yq = [rat(v) for v in y]
ok = all(sum(int(A[i, j]) * yq[j] for j in range(cols - 1) if yq[j]) == int(e[i]) for i in range(rows))
print(f"  target a1 > ... > am identified: {'exactly verified' if ok else 'reconstruction failed'};",
      f"{sum(1 for v in yq if v)} marginal terms used")
assert ok
