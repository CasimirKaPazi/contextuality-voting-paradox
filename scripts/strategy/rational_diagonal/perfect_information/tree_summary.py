"""Summaries of game trees for the four chain configurations, composed node by node, and a check
against the summaries computed from the normal form.  Configurations, with P = (0, ..., k-1):
(0, P, rev P), (1, rev P, P), (0, P*, rev P), (1, (rev P)*, P); a configuration's lines are the
strategies of its player (rows for player 0, columns for player 1)."""
import random, sys, itertools
sys.path.insert(0, "../absorption")
from pi_trees import rand_tree, normal_form
from k3_chain import T
def cfgs(k):
    P = tuple(range(k)); rP = P[::-1]; Ps = (0,) + rP[:-1]; rPs = (k - 1,) + P[:-1]
    out = []
    for pl, own, opp in ((0, P, rP), (1, rP, P), (0, Ps, rP), (1, rPs, P)):
        out.append((pl, {u: n for n, u in enumerate(own)}, {u: n for n, u in enumerate(opp)}))
    return out
def leaf(z, k):
    return (tuple([frozenset([(z, z)])] * 4), frozenset([z]), frozenset([z]), frozenset([z]))
def compose(A, B, root, C):
    mA, prA, F0A, F1A = A; mB, prB, F0B, F1B = B; out = []
    for c, (pl, rp, rq) in enumerate(C):
        if root == pl:
            bA = min(prA, key=lambda u: rp[u]); bB = min(prB, key=lambda u: rp[u])
            s = {(y, min(M, bB, key=lambda u: rp[u])) for y, M in mA[c]} | {(y, min(M, bA, key=lambda u: rp[u])) for y, M in mB[c]}
        else:
            s = set()
            for (y1, M1) in mA[c]:
                for (y2, M2) in mB[c]:
                    if y1 == y2: s.add((y1, min(M1, M2, key=lambda u: rp[u])))
                    elif rq[y1] < rq[y2]: s.add((y1, M1))
                    else: s.add((y2, M2))
        out.append(frozenset(s))
    pr = prA | prB
    if root == 0: F0, F1 = F0A | F0B, F1A & F1B
    else: F1, F0 = F1A | F1B, F0A & F0B
    return (tuple(out), pr, F0, F1)
def summarise(t, k, C):
    if t[0] == "leaf": return leaf(t[1], k)
    ch = [summarise(c, k, C) for c in t[2]]
    s = ch[0]
    for x in ch[1:]: s = compose(s, x, t[1], C)
    return s
def direct(R, k, C):
    out = []
    for pl, rp, rq in C:
        L = R if pl == 0 else T(R); Cl = T(L); s = set()
        for r in L:
            y = min(r, key=lambda u: rq[u])
            M = min((v for j in range(len(Cl)) if r[j] == y for v in Cl[j]), key=lambda u: rp[u])
            s.add((y, M))
        out.append(frozenset(s))
    F0 = frozenset(u for u in range(k) if any(all(v == u for v in r) for r in R))
    F1 = frozenset(u for u in range(k) if any(all(v == u for v in c) for c in T(R)))
    return (tuple(out), frozenset(v for r in R for v in r), F0, F1)
if __name__ == "__main__":
    random.seed(17); bad = tot = 0
    for _ in range(3000):
        k = random.choice((3, 4, 5)); t = rand_tree(random.randint(2, 5), k); R = normal_form(t)
        if R is None: continue
        C = cfgs(k); tot += 1
        if summarise(t, k, C) != direct(R, k, C): bad += 1
    print(tot, "trees,", bad, "mismatches between the composed and the direct summaries")
