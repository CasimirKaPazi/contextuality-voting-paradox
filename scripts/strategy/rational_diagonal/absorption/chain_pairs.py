"""The pieces of a proof of the chain conjecture (Section 7), checked for k outcomes.
With P = (a, m_1..m_n, c) and v = m_q the saddle value of the opposed game G1:
  r1: a row of i safe in G1 (every best reply of o to it is an equilibrium);  s2: a column of o safe in G1;
  r3: a row of i safe in i's twin game, of type gamma (holds c) or delta (does not; worst outcome m_j);
  s4: a column of o safe in o's twin game, of type alpha (holds a) or beta (does not; best outcome m_l).
Proved pieces: (i) j >= q and l <= q; (ii) no alpha with gamma; (iii) no r1 with beta, l = q;
(iv) no s2 with delta, j = q.  The script counts violations (expected 0) and how often the
remaining cases (beta with l < q, delta with j > q) occur."""
import random, itertools, collections
from sg import matrix
from k3_chain import T, forces, tt
def safe_lines(R, Pi, Po):
    """rows of R (player with order Pi, opponent order Po) whose opponent-best cells are all equilibria"""
    ri = {u: n for n, u in enumerate(Pi)}; ro = {u: n for n, u in enumerate(Po)}; C = T(R); out = []
    for r in R:
        y = min(r, key=lambda u: ro[u])
        if all(all(ri[v] >= ri[y] for v in C[c]) for c in range(len(C)) if r[c] == y): out.append(r)
    return out
def saddle_index(Ri, P):
    pos = {u: n for n, u in enumerate(P)}
    v1 = min(max(pos[u] for u in r) for r in Ri); v2 = max(min(pos[u] for u in s) for s in T(Ri))
    return v1 if v1 == v2 else None
def valid(R, k):
    return len({v for r in R for v in r}) == k and not any(all(forces(M, u) for u in range(k)) for M in (R, T(R)))
def check(R, k, st):
    for Ri, Ro in ((R, T(R)), (T(R), R)):
        for a, c in itertools.permutations(range(k), 2):
            if forces(Ri, a) or forces(Ro, c): continue
            for mid in itertools.permutations([u for u in range(k) if u not in (a, c)]):
                P = (a,) + mid + (c,); rP = P[::-1]; Ps = (a,) + rP[:-1]; rPs = (c,) + P[:-1]
                pos = {u: n for n, u in enumerate(P)}; q = saddle_index(Ri, P)
                st["cases"] += 1; st["no saddle"] += q is None
                st["saddle value is a or c"] += q in (0, k - 1)
                r1 = safe_lines(Ri, P, rP); s2 = safe_lines(Ro, rP, P)
                r3 = safe_lines(Ri, Ps, rP); s4 = safe_lines(Ro, rPs, P)
                gamma = any(c in r for r in r3); alpha = any(a in s for s in s4)
                js = {pos[max(r, key=lambda u: pos[u])] for r in r3 if c not in r}
                ls = {pos[min(s, key=lambda u: pos[u])] for s in s4 if a not in s}
                st["(i) violated"] += any(j < q for j in js) or any(l > q for l in ls)
                st["(ii) violated"] += alpha and gamma
                st["(iii) violated"] += bool(r1) and q in ls
                st["(iv) violated"] += bool(s2) and q in js
                st["remaining: beta l<q or delta j>q"] += any(l < q for l in ls) or any(j > q for j in js)
                st["chain fails"] += bool(r1) and bool(s2) and bool(r3) and bool(s4)
if __name__ == "__main__":
    random.seed(13)
    for k in (3, 4, 5):
        st = collections.Counter(); g = 0
        while g < (1500 if k < 5 else 400):
            n = random.randint(k, k + 6)
            p = tuple(random.randrange(2) for _ in range(n)); o = tuple(random.randrange(k) for _ in range(n)); z = random.randrange(k)
            R = matrix(p, o, z, 0)
            if not valid(R, k): continue
            g += 1; check(R, k, st)
        print(f"k={k} stopping games:", dict(st))
    for k in (3, 4):
        st = collections.Counter(); g = 0
        while g < 800:
            n, m = random.randint(2, 6), random.randint(2, 6)
            R = [[random.randrange(k) for _ in range(m)] for _ in range(n)]
            for _ in range(random.randint(0, 2 * n * m)):
                i, j = random.randrange(n), random.randrange(m)
                R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
            if not valid(R, k) or not tt(R): continue
            g += 1; check(R, k, st)
        print(f"k={k} random totally tight:", dict(st))
