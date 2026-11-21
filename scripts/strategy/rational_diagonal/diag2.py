"""Two-player rational diagonal: characterization via a greedy order Q.
For player i with strict P, Ref(b) = columns c with b not a P-best reply to c.
T(b) = outcomes g(b,c), c in Ref(b); O(b) = row outcomes.
A strict Q works iff for every row b, the Q-top of O(b) lies in T(b).
Greedy: repeatedly pick an outcome that is 'safe' (no remaining row has it outside T),
remove rows containing it."""
from itertools import permutations, product
import sys

def rows_of(g, m1, m2, i):
    # rows indexed by player i's strategies; returns list of rows (tuples of outcomes over opponent strategies)
    if i == 0: return [tuple(g[a*m2+c] for c in range(m2)) for a in range(m1)]
    return [tuple(g[a*m2+c] for a in range(m1)) for c in range(m2)]

def q_exists(O, T, outcomes):
    rows = list(range(len(O)))
    while rows:
        appearing = set().union(*(O[b] for b in rows))
        safe = [o for o in appearing if all(o in T[b] for b in rows if o in O[b])]
        if not safe: return False
        o = safe[0]
        rows = [b for b in rows if o not in O[b]]
    return True

def works_fast(g, m1, m2, outcomes, prefs):
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)          # R[b][c]
        nb, nc = len(R), len(R[0])
        O = [set(r) for r in R]
        for P in prefs:
            rank = {x: k for k, x in enumerate(P)}   # smaller = better
            # best value for player i in each column c
            best = [min(rank[R[b][c]] for b in range(nb)) for c in range(nc)]
            T = [{R[b][c] for c in range(nc) if rank[R[b][c]] > best[c]} for b in range(nb)]
            if any(not t for t in T): continue      # some b dominant-ish? (b BR to every c)
            if q_exists(O, T, outcomes): return (i, P)
    return None

def works_brute(g, m1, m2, outcomes, prefs):
    for i in (0, 1):
        R = rows_of(g, m1, m2, i); nb, nc = len(R), len(R[0])
        for P in prefs:
            rp = {x: k for k, x in enumerate(P)}
            for Q in prefs:
                rq = {x: k for k, x in enumerate(Q)}
                ok = True
                for b in range(nb):
                    top = min(rq[R[b][c]] for c in range(nc))
                    brs = [c for c in range(nc) if rq[R[b][c]] == top]
                    if not any(rp[R[b][c]] > min(rp[R[bb][c]] for bb in range(nb)) for c in brs):
                        ok = False; break
                if ok: return (i, P, Q)
    return None

def dictator(g, m1, m2, outcomes):
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)
        if all(any(all(x == o for x in r) for r in R) for o in outcomes): return True
    return False
