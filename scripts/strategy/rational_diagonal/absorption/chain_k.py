"""The chain for k outcomes.  If player i does not force a and the opponent o does not force c != a,
then for every order P with top a and bottom c one of
    (i, P, rev P),  (o, rev P, P),  (i, P', rev P),  (o, P'', P)
works, where P' = (a) + (rev P without its last) and P'' = (c) + (P without its last), so that the
rotation of P' is rev P and the rotation of P'' is P.  Checked on random stopping games and random
totally tight forms."""
import random, itertools, sys
from sg import matrix
from k3_chain import works, T, forces, tt
def chain_ok(R, k):
    cases = fails = 0; ex = None
    for Ri, Ro in ((R, T(R)), (T(R), R)):
        for a, c in itertools.permutations(range(k), 2):
            if forces(Ri, a) or forces(Ro, c): continue
            mids = [u for u in range(k) if u not in (a, c)]
            for mid in itertools.permutations(mids):
                P = (a,) + mid + (c,); rP = P[::-1]
                P1 = (a,) + rP[:-1]; P2 = (c,) + P[:-1]
                assert P1[1:] + P1[:1] == rP and P2[1:] + P2[:1] == P
                cases += 1
                ok = works(Ri, P, rP) or works(Ro, rP, P) or works(Ri, P1, rP) or works(Ro, P2, P)
                if not ok:
                    fails += 1; ex = ex or (R, P)
    return cases, fails, ex
def valid(R, k):
    return len({v for r in R for v in r}) == k and not any(all(forces(M, u) for u in range(k)) for M in (R, T(R)))
random.seed(7)
for k in (4, 5, 6):
    tot = [0, 0, 0]; ex = None
    while tot[0] < (3000 if k == 4 else 800):
        n = random.randint(k, k + 6)
        p = tuple(random.randrange(2) for _ in range(n)); o = tuple(random.randrange(k) for _ in range(n)); z = random.randrange(k)
        R = matrix(p, o, z, 0)
        if not valid(R, k): continue
        c, f, e = chain_ok(R, k); tot[0] += 1; tot[1] += c; tot[2] += f; ex = ex or e
    print(f"k={k} random stopping games (games, cases, failures):", tot, ex and (ex[0], ex[1]))
for k in (4,):
    tot = [0, 0, 0]; tries = 0
    while tot[0] < 1500 and tries < 10**7:
        tries += 1
        n, m = random.randint(2, 6), random.randint(2, 6)
        R = [[random.randrange(k) for _ in range(m)] for _ in range(n)]
        for _ in range(random.randint(0, 2 * n * m)):
            i, j = random.randrange(n), random.randrange(m)
            R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
        if not valid(R, k) or not tt(R): continue
        c, f, e = chain_ok(R, k); tot[0] += 1; tot[1] += c; tot[2] += f
    print(f"k={k} random totally tight forms (forms, cases, failures):", tot)
