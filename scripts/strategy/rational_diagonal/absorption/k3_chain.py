"""Three outcomes: the chain lemma.  If player i does not force a and the opponent o does not force
c (c != a; e the third outcome), then one of
    (i, rev, (a, e, c)),  (o, rot, (c, a, e)),  (i, rot, (a, c, e)),  (o, rev, (c, e, a))
works.  Checked with the direct (y, M) test on random totally tight forms and on all stopping
games with three outcomes up to 7 nodes; also reports failures on forms that are not totally tight."""
import random, itertools, pickle
from sg import matrix
def T(R): return [list(c) for c in zip(*R)]
def works(R, P, Q):
    """rows of R belong to the player with order P; opponent order Q (lists, best first)"""
    rp = {u: n for n, u in enumerate(P)}; rq = {u: n for n, u in enumerate(Q)}; C = T(R)
    for r in R:
        y = min(r, key=lambda u: rq[u])
        M = min((v for c in range(len(C)) if r[c] == y for v in C[c]), key=lambda u: rp[u])
        if not rp[M] < rp[y]: return False
    return True
def rev(R, P): return works(R, P, P[::-1])
def rot(R, P): return works(R, P, P[1:] + P[:1])
def forces(R, u): return any(all(v == u for v in r) for r in R)
def tt(R):
    n, m = len(R), len(R[0])
    for i1, i2 in itertools.combinations(range(n), 2):
        for j1, j2 in itertools.combinations(range(m), 2):
            p, q, r, s = R[i1][j1], R[i1][j2], R[i2][j1], R[i2][j2]
            if not (p == q or r == s or p == r or q == s): return False
    return True
def chain(R):
    """returns (cases, failures) over all players i and admissible (a, c)"""
    cases = fails = 0
    for Ri, Ro in ((R, T(R)), (T(R), R)):
        for a, c in itertools.permutations(range(3), 2):
            if forces(Ri, a) or forces(Ro, c): continue
            e = 3 - a - c; cases += 1
            ok = rev(Ri, (a, e, c)) or rot(Ro, (c, a, e)) or rot(Ri, (a, c, e)) or rev(Ro, (c, e, a))
            fails += not ok
    return cases, fails
random.seed(5); st = {"totally tight": [0, 0, 0], "not totally tight": [0, 0, 0]}
while st["totally tight"][0] < 3000 or st["not totally tight"][0] < 3000:
    n, m = random.randint(2, 6), random.randint(2, 6)
    R = [[random.randrange(3) for _ in range(m)] for _ in range(n)]
    # bias towards tightness: copy neighbours often
    for _ in range(random.randint(0, n * m)):
        i, j = random.randrange(n), random.randrange(m)
        R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
    if len({v for r in R for v in r}) < 3: continue
    key = "totally tight" if tt(R) else "not totally tight"
    if st[key][0] >= 3000: continue
    c, f = chain(R); st[key][0] += 1; st[key][1] += c; st[key][2] += f
print("random forms (forms, cases, failures):", st)
data = pickle.load(open("data_k3_N7.pkl", "rb")); tot = [0, 0]
for p, o, z, W in data:
    if len(set(o) | {z}) != 3: continue
    c, f = chain(matrix(p, o, z, 0)); tot[0] += c; tot[1] += f
print("stopping games up to 7 nodes (cases, failures):", tot)
