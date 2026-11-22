"""Stopping games: nodes t = 0..N-1 with owner p[t] in {0,1} and outcome o[t]; terminal z.
A strategy of a player is its first stopping node, or None (never stop).
Normal form: outcome of (s0, s1) is the outcome of the earlier stop, z if neither stops.
works(i, P, Q): every strategy of i is refuted (the rational diagonal)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from itertools import permutations, product
from recipes_core import works_PQ

def strategies(p, i):
    return [t for t in range(len(p)) if p[t] == i] + [None]

def outcome(o, z, s0, s1):
    a = len(o) if s0 is None else s0
    b = len(o) if s1 is None else s1
    m = min(a, b)
    return z if m == len(o) else o[m]

def matrix(p, o, z, i):
    """rows: strategies of i, columns: strategies of the opponent"""
    R = []
    for s in strategies(p, i):
        row = []
        for t in strategies(p, 1 - i):
            row.append(outcome(o, z, s, t) if i == 0 else outcome(o, z, t, s))
        R.append(tuple(row))
    return R

def works_direct(p, o, z, i, P, Q):
    """the characterisation: (a) o_s = y and some outcome of i's nodes, the terminal one or an
    opponent node after s is better for i than y; (b) an opponent node before s with outcome y
    and an own node before it with a better one"""
    rp = {x: r for r, x in enumerate(P)}; rq = {x: r for r, x in enumerate(Q)}
    N = len(o)
    own = [o[t] for t in range(N) if p[t] == i] + [z]
    bestown = min(rp[x] for x in own)
    for s in strategies(p, i):
        S = N if s is None else s
        os_ = z if s is None else o[s]
        cand = [o[t] for t in range(S) if p[t] != i] + [os_]
        y = min(cand, key=lambda x: rq[x])
        ok = False
        later = [rp[o[t]] for t in range(S + 1, N) if p[t] != i]
        if os_ == y and min([bestown] + later) < rp[y]: ok = True
        for t in range(S):
            if p[t] != i and o[t] == y:
                if any(p[u] == i and rp[o[u]] < rp[y] for u in range(t)): ok = True
        if not ok: return False
    return True

def forces(p, o, z, i):
    """outcomes player i forces: the constant rows of i's matrix"""
    return {r[0] for r in matrix(p, o, z, i) if len(set(r)) == 1}

def present(o, z): return set(o) | {z}

def valid(p, o, z):
    pr = present(o, z)
    return len(pr) >= 3 and forces(p, o, z, 0) != pr and forces(p, o, z, 1) != pr

if __name__ == "__main__":
    import random
    rnd = random.Random(1); bad = 0
    for _ in range(3000):
        N = rnd.randint(1, 7); k = rnd.choice([3, 4]); outs = range(k)
        p = [rnd.randint(0, 1) for _ in range(N)]; o = [rnd.choice(outs) for _ in range(N)]
        z = rnd.choice(outs)
        used = sorted(present(o, z))
        for i in (0, 1):
            R = matrix(p, o, z, i)
            for P in permutations(used):
                Q = tuple(rnd.sample(used, len(used)))
                if works_PQ(R, P, Q) != works_direct(p, o, z, i, P, Q): bad += 1
    print("mismatches between the characterisation and the matrix test:", bad)
